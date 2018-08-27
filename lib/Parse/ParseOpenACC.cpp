//===--- ParseOpenACC.cpp - OpenACC directives parsing ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file implements parsing of all OpenACC directives and clauses.
///
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/StmtOpenACC.h"
#include "clang/Parse/ParseDiagnostic.h"
#include "clang/Parse/Parser.h"
#include "clang/Parse/RAIIObjectsForParser.h"
#include "clang/Sema/Scope.h"
#include "llvm/ADT/PointerIntPair.h"

using namespace clang;

//===----------------------------------------------------------------------===//
// OpenACC declarative directives.
//===----------------------------------------------------------------------===//

namespace {
enum OpenACCDirectiveKindEx {
  ACCD_cancellation = ACCD_unknown + 1,
  ACCD_data,
  ACCD_declare,
  ACCD_end,
  ACCD_end_declare,
  ACCD_enter,
  ACCD_exit,
  ACCD_point,
  ACCD_reduction,
  ACCD_target_enter,
  ACCD_target_exit,
  ACCD_update,
  ACCD_distribute_parallel,
  ACCD_teams_distribute_parallel,
  ACCD_target_teams_distribute_parallel
};

class ThreadprivateListParserHelper final {
  SmallVector<Expr *, 4> Identifiers;
  Parser *P;

public:
  ThreadprivateListParserHelper(Parser *P) : P(P) {}
  void operator()(CXXScopeSpec &SS, DeclarationNameInfo NameInfo) {
    ExprResult Res =
        P->getActions().ActOnOpenACCIdExpression(P->getCurScope(), SS, NameInfo);
    if (Res.isUsable())
      Identifiers.push_back(Res.get());
  }
  llvm::ArrayRef<Expr *> getIdentifiers() const { return Identifiers; }
};
} // namespace

// Map token string to extended ACC token kind that are
// OpenACCDirectiveKind + OpenACCDirectiveKindEx.
static unsigned getOpenACCDirectiveKindEx(StringRef S) {
  auto DKind = getOpenACCDirectiveKind(S);
  if (DKind != ACCD_unknown)
    return DKind;

  return llvm::StringSwitch<unsigned>(S)
      .Case("cancellation", ACCD_cancellation)
      .Case("data", ACCD_data)
      .Case("declare", ACCD_declare)
      .Case("end", ACCD_end)
      .Case("enter", ACCD_enter)
      .Case("exit", ACCD_exit)
      .Case("point", ACCD_point)
      .Case("reduction", ACCD_reduction)
      .Case("update", ACCD_update)
      .Default(ACCD_unknown);
}

static OpenACCDirectiveKind ParseOpenACCDirectiveKind(Parser &P) {
  // Array of foldings: F[i][0] F[i][1] ===> F[i][2].
  // E.g.: ACCD_for ACCD_simd ===> ACCD_for_simd
  // TODO: add other combined directives in topological order.
  static const unsigned F[][3] = {
    { ACCD_cancellation, ACCD_point, ACCD_cancellation_point },
    { ACCD_declare, ACCD_reduction, ACCD_declare_reduction },
    { ACCD_declare, ACCD_simd, ACCD_declare_simd },
    { ACCD_declare, ACCD_target, ACCD_declare_target },
    { ACCD_distribute, ACCD_parallel, ACCD_distribute_parallel },
    { ACCD_distribute_parallel, ACCD_for, ACCD_distribute_parallel_for },
    { ACCD_distribute_parallel_for, ACCD_simd, 
      ACCD_distribute_parallel_for_simd },
    { ACCD_distribute, ACCD_simd, ACCD_distribute_simd },
    { ACCD_end, ACCD_declare, ACCD_end_declare },
    { ACCD_end_declare, ACCD_target, ACCD_end_declare_target },
    { ACCD_target, ACCD_data, ACCD_target_data },
    { ACCD_target, ACCD_enter, ACCD_target_enter },
    { ACCD_target, ACCD_exit, ACCD_target_exit },
    { ACCD_target, ACCD_update, ACCD_target_update },
    { ACCD_target_enter, ACCD_data, ACCD_target_enter_data },
    { ACCD_target_exit, ACCD_data, ACCD_target_exit_data },
    { ACCD_for, ACCD_simd, ACCD_for_simd },
    { ACCD_parallel, ACCD_for, ACCD_parallel_for },
    { ACCD_parallel_for, ACCD_simd, ACCD_parallel_for_simd },
    { ACCD_parallel, ACCD_sections, ACCD_parallel_sections },
    { ACCD_taskloop, ACCD_simd, ACCD_taskloop_simd },
    { ACCD_target, ACCD_parallel, ACCD_target_parallel },
    { ACCD_target, ACCD_simd, ACCD_target_simd },
    { ACCD_target_parallel, ACCD_for, ACCD_target_parallel_for },
    { ACCD_target_parallel_for, ACCD_simd, ACCD_target_parallel_for_simd },
    { ACCD_teams, ACCD_distribute, ACCD_teams_distribute },
    { ACCD_teams_distribute, ACCD_simd, ACCD_teams_distribute_simd },
    { ACCD_teams_distribute, ACCD_parallel, ACCD_teams_distribute_parallel },
    { ACCD_teams_distribute_parallel, ACCD_for, ACCD_teams_distribute_parallel_for },
    { ACCD_teams_distribute_parallel_for, ACCD_simd, ACCD_teams_distribute_parallel_for_simd },
    { ACCD_target, ACCD_teams, ACCD_target_teams },
    { ACCD_target_teams, ACCD_distribute, ACCD_target_teams_distribute },
    { ACCD_target_teams_distribute, ACCD_parallel, ACCD_target_teams_distribute_parallel },
    { ACCD_target_teams_distribute, ACCD_simd, ACCD_target_teams_distribute_simd },
    { ACCD_target_teams_distribute_parallel, ACCD_for, ACCD_target_teams_distribute_parallel_for },
    { ACCD_target_teams_distribute_parallel_for, ACCD_simd, ACCD_target_teams_distribute_parallel_for_simd }
  };
  enum { CancellationPoint = 0, DeclareReduction = 1, TargetData = 2 };
  auto Tok = P.getCurToken();
  unsigned DKind =
      Tok.isAnnotation()
          ? static_cast<unsigned>(ACCD_unknown)
          : getOpenACCDirectiveKindEx(P.getPreprocessor().getSpelling(Tok));
  if (DKind == ACCD_unknown)
    return ACCD_unknown;

  for (unsigned i = 0; i < llvm::array_lengthof(F); ++i) {
    if (DKind != F[i][0])
      continue;

    Tok = P.getPreprocessor().LookAhead(0);
    unsigned SDKind =
        Tok.isAnnotation()
            ? static_cast<unsigned>(ACCD_unknown)
            : getOpenACCDirectiveKindEx(P.getPreprocessor().getSpelling(Tok));
    if (SDKind == ACCD_unknown)
      continue;

    if (SDKind == F[i][1]) {
      P.ConsumeToken();
      DKind = F[i][2];
    }
  }
  return DKind < ACCD_unknown ? static_cast<OpenACCDirectiveKind>(DKind)
                              : ACCD_unknown;
}

static DeclarationName parseOpenACCReductionId(Parser &P) {
  Token Tok = P.getCurToken();
  Sema &Actions = P.getActions();
  OverloadedOperatorKind OOK = OO_None;
  // Allow to use 'operator' keyword for C++ operators
  bool WithOperator = false;
  if (Tok.is(tok::kw_operator)) {
    P.ConsumeToken();
    Tok = P.getCurToken();
    WithOperator = true;
  }
  switch (Tok.getKind()) {
  case tok::plus: // '+'
    OOK = OO_Plus;
    break;
  case tok::minus: // '-'
    OOK = OO_Minus;
    break;
  case tok::star: // '*'
    OOK = OO_Star;
    break;
  case tok::amp: // '&'
    OOK = OO_Amp;
    break;
  case tok::pipe: // '|'
    OOK = OO_Pipe;
    break;
  case tok::caret: // '^'
    OOK = OO_Caret;
    break;
  case tok::ampamp: // '&&'
    OOK = OO_AmpAmp;
    break;
  case tok::pipepipe: // '||'
    OOK = OO_PipePipe;
    break;
  case tok::identifier: // identifier
    if (!WithOperator)
      break;
    LLVM_FALLTHROUGH;
  default:
    P.Diag(Tok.getLocation(), diag::err_acc_expected_reduction_identifier);
    P.SkipUntil(tok::colon, tok::r_paren, tok::annot_pragma_openacc_end,
                Parser::StopBeforeMatch);
    return DeclarationName();
  }
  P.ConsumeToken();
  auto &DeclNames = Actions.getASTContext().DeclarationNames;
  return OOK == OO_None ? DeclNames.getIdentifier(Tok.getIdentifierInfo())
                        : DeclNames.getCXXOperatorName(OOK);
}

/// \brief Parse 'acc declare reduction' construct.
///
///       declare-reduction-directive:
///        annot_pragma_openacc 'declare' 'reduction'
///        '(' <reduction_id> ':' <type> {',' <type>} ':' <expression> ')'
///        ['initializer' '(' ('acc_priv' '=' <expression>)|<function_call> ')']
///        annot_pragma_openacc_end
/// <reduction_id> is either a base language identifier or one of the following
/// operators: '+', '-', '*', '&', '|', '^', '&&' and '||'.
///
Parser::DeclGroupPtrTy
Parser::ParseOpenACCDeclareReductionDirective(AccessSpecifier AS) {
  // Parse '('.
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after,
                         getOpenACCDirectiveName(ACCD_declare_reduction))) {
    SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
    return DeclGroupPtrTy();
  }

  DeclarationName Name = parseOpenACCReductionId(*this);
  if (Name.isEmpty() && Tok.is(tok::annot_pragma_openacc_end))
    return DeclGroupPtrTy();

  // Consume ':'.
  bool IsCorrect = !ExpectAndConsume(tok::colon);

  if (!IsCorrect && Tok.is(tok::annot_pragma_openacc_end))
    return DeclGroupPtrTy();

  IsCorrect = IsCorrect && !Name.isEmpty();

  if (Tok.is(tok::colon) || Tok.is(tok::annot_pragma_openacc_end)) {
    Diag(Tok.getLocation(), diag::err_expected_type);
    IsCorrect = false;
  }

  if (!IsCorrect && Tok.is(tok::annot_pragma_openacc_end))
    return DeclGroupPtrTy();

  SmallVector<std::pair<QualType, SourceLocation>, 8> ReductionTypes;
  // Parse list of types until ':' token.
  do {
    ColonProtectionRAIIObject ColonRAII(*this);
    SourceRange Range;
    TypeResult TR =
        ParseTypeName(&Range, DeclaratorContext::PrototypeContext, AS);
    if (TR.isUsable()) {
      auto ReductionType =
          Actions.ActOnOpenACCDeclareReductionType(Range.getBegin(), TR);
      if (!ReductionType.isNull()) {
        ReductionTypes.push_back(
            std::make_pair(ReductionType, Range.getBegin()));
      }
    } else {
      SkipUntil(tok::comma, tok::colon, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    }

    if (Tok.is(tok::colon) || Tok.is(tok::annot_pragma_openacc_end))
      break;

    // Consume ','.
    if (ExpectAndConsume(tok::comma)) {
      IsCorrect = false;
      if (Tok.is(tok::annot_pragma_openacc_end)) {
        Diag(Tok.getLocation(), diag::err_expected_type);
        return DeclGroupPtrTy();
      }
    }
  } while (Tok.isNot(tok::annot_pragma_openacc_end));

  if (ReductionTypes.empty()) {
    SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
    return DeclGroupPtrTy();
  }

  if (!IsCorrect && Tok.is(tok::annot_pragma_openacc_end))
    return DeclGroupPtrTy();

  // Consume ':'.
  if (ExpectAndConsume(tok::colon))
    IsCorrect = false;

  if (Tok.is(tok::annot_pragma_openacc_end)) {
    Diag(Tok.getLocation(), diag::err_expected_expression);
    return DeclGroupPtrTy();
  }

  DeclGroupPtrTy DRD = Actions.ActOnOpenACCDeclareReductionDirectiveStart(
      getCurScope(), Actions.getCurLexicalContext(), Name, ReductionTypes, AS);

  // Parse <combiner> expression and then parse initializer if any for each
  // correct type.
  unsigned I = 0, E = ReductionTypes.size();
  for (auto *D : DRD.get()) {
    TentativeParsingAction TPA(*this);
    ParseScope ACCDRScope(this, Scope::FnScope | Scope::DeclScope |
                                    Scope::CompoundStmtScope |
                                    Scope::OpenACCDirectiveScope);
    // Parse <combiner> expression.
    Actions.ActOnOpenACCDeclareReductionCombinerStart(getCurScope(), D);
    ExprResult CombinerResult =
        Actions.ActOnFinishFullExpr(ParseAssignmentExpression().get(),
                                    D->getLocation(), /*DiscardedValue=*/true);
    Actions.ActOnOpenACCDeclareReductionCombinerEnd(D, CombinerResult.get());

    if (CombinerResult.isInvalid() && Tok.isNot(tok::r_paren) &&
        Tok.isNot(tok::annot_pragma_openacc_end)) {
      TPA.Commit();
      IsCorrect = false;
      break;
    }
    IsCorrect = !T.consumeClose() && IsCorrect && CombinerResult.isUsable();
    ExprResult InitializerResult;
    if (Tok.isNot(tok::annot_pragma_openacc_end)) {
      // Parse <initializer> expression.
      if (Tok.is(tok::identifier) &&
          Tok.getIdentifierInfo()->isStr("initializer"))
        ConsumeToken();
      else {
        Diag(Tok.getLocation(), diag::err_expected) << "'initializer'";
        TPA.Commit();
        IsCorrect = false;
        break;
      }
      // Parse '('.
      BalancedDelimiterTracker T(*this, tok::l_paren,
                                 tok::annot_pragma_openacc_end);
      IsCorrect =
          !T.expectAndConsume(diag::err_expected_lparen_after, "initializer") &&
          IsCorrect;
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        ParseScope ACCDRScope(this, Scope::FnScope | Scope::DeclScope |
                                        Scope::CompoundStmtScope |
                                        Scope::OpenACCDirectiveScope);
        // Parse expression.
        VarDecl *AccPrivParm =
            Actions.ActOnOpenACCDeclareReductionInitializerStart(getCurScope(),
                                                                D);
        // Check if initializer is acc_priv <init_expr> or something else.
        if (Tok.is(tok::identifier) &&
            Tok.getIdentifierInfo()->isStr("acc_priv")) {
          ConsumeToken();
          ParseOpenACCReductionInitializerForDecl(AccPrivParm);
        } else {
          InitializerResult = Actions.ActOnFinishFullExpr(
              ParseAssignmentExpression().get(), D->getLocation(),
              /*DiscardedValue=*/true);
        }
        Actions.ActOnOpenACCDeclareReductionInitializerEnd(
            D, InitializerResult.get(), AccPrivParm);
        if (InitializerResult.isInvalid() && Tok.isNot(tok::r_paren) &&
            Tok.isNot(tok::annot_pragma_openacc_end)) {
          TPA.Commit();
          IsCorrect = false;
          break;
        }
        IsCorrect =
            !T.consumeClose() && IsCorrect && !InitializerResult.isInvalid();
      }
    }

    ++I;
    // Revert parsing if not the last type, otherwise accept it, we're done with
    // parsing.
    if (I != E)
      TPA.Revert();
    else
      TPA.Commit();
  }
  return Actions.ActOnOpenACCDeclareReductionDirectiveEnd(getCurScope(), DRD,
                                                         IsCorrect);
}

void Parser::ParseOpenACCReductionInitializerForDecl(VarDecl *AccPrivParm) {
  // Parse declarator '=' initializer.
  // If a '==' or '+=' is found, suggest a fixit to '='.
  if (isTokenEqualOrEqualTypo()) {
    ConsumeToken();

    if (Tok.is(tok::code_completion)) {
      Actions.CodeCompleteInitializer(getCurScope(), AccPrivParm);
      Actions.FinalizeDeclaration(AccPrivParm);
      cutOffParsing();
      return;
    }

    ExprResult Init(ParseInitializer());

    if (Init.isInvalid()) {
      SkipUntil(tok::r_paren, tok::annot_pragma_openacc_end, StopBeforeMatch);
      Actions.ActOnInitializerError(AccPrivParm);
    } else {
      Actions.AddInitializerToDecl(AccPrivParm, Init.get(),
                                   /*DirectInit=*/false);
    }
  } else if (Tok.is(tok::l_paren)) {
    // Parse C++ direct initializer: '(' expression-list ')'
    BalancedDelimiterTracker T(*this, tok::l_paren);
    T.consumeOpen();

    ExprVector Exprs;
    CommaLocsTy CommaLocs;

    if (ParseExpressionList(Exprs, CommaLocs, [this, AccPrivParm, &Exprs] {
          Actions.CodeCompleteConstructor(
              getCurScope(), AccPrivParm->getType()->getCanonicalTypeInternal(),
              AccPrivParm->getLocation(), Exprs);
        })) {
      Actions.ActOnInitializerError(AccPrivParm);
      SkipUntil(tok::r_paren, tok::annot_pragma_openacc_end, StopBeforeMatch);
    } else {
      // Match the ')'.
      T.consumeClose();

      assert(!Exprs.empty() && Exprs.size() - 1 == CommaLocs.size() &&
             "Unexpected number of commas!");

      ExprResult Initializer = Actions.ActOnParenListExpr(
          T.getOpenLocation(), T.getCloseLocation(), Exprs);
      Actions.AddInitializerToDecl(AccPrivParm, Initializer.get(),
                                   /*DirectInit=*/true);
    }
  } else if (getLangOpts().CPlusPlus11 && Tok.is(tok::l_brace)) {
    // Parse C++0x braced-init-list.
    Diag(Tok, diag::warn_cxx98_compat_generalized_initializer_lists);

    ExprResult Init(ParseBraceInitializer());

    if (Init.isInvalid()) {
      Actions.ActOnInitializerError(AccPrivParm);
    } else {
      Actions.AddInitializerToDecl(AccPrivParm, Init.get(),
                                   /*DirectInit=*/true);
    }
  } else {
    Actions.ActOnUninitializedDecl(AccPrivParm);
  }
}

namespace {
/// RAII that recreates function context for correct parsing of clauses of
/// 'declare simd' construct.
/// OpenACC, 2.8.2 declare simd Construct
/// The expressions appearing in the clauses of this directive are evaluated in
/// the scope of the arguments of the function declaration or definition.
class FNContextRAII final {
  Parser &P;
  Sema::CXXThisScopeRAII *ThisScope;
  Parser::ParseScope *TempScope;
  Parser::ParseScope *FnScope;
  bool HasTemplateScope = false;
  bool HasFunScope = false;
  FNContextRAII() = delete;
  FNContextRAII(const FNContextRAII &) = delete;
  FNContextRAII &operator=(const FNContextRAII &) = delete;

public:
  FNContextRAII(Parser &P, Parser::DeclGroupPtrTy Ptr) : P(P) {
    Decl *D = *Ptr.get().begin();
    NamedDecl *ND = dyn_cast<NamedDecl>(D);
    RecordDecl *RD = dyn_cast_or_null<RecordDecl>(D->getDeclContext());
    Sema &Actions = P.getActions();

    // Allow 'this' within late-parsed attributes.
    ThisScope = new Sema::CXXThisScopeRAII(Actions, RD, /*TypeQuals=*/0,
                                           ND && ND->isCXXInstanceMember());

    // If the Decl is templatized, add template parameters to scope.
    HasTemplateScope = D->isTemplateDecl();
    TempScope =
        new Parser::ParseScope(&P, Scope::TemplateParamScope, HasTemplateScope);
    if (HasTemplateScope)
      Actions.ActOnReenterTemplateScope(Actions.getCurScope(), D);

    // If the Decl is on a function, add function parameters to the scope.
    HasFunScope = D->isFunctionOrFunctionTemplate();
    FnScope = new Parser::ParseScope(
        &P, Scope::FnScope | Scope::DeclScope | Scope::CompoundStmtScope,
        HasFunScope);
    if (HasFunScope)
      Actions.ActOnReenterFunctionContext(Actions.getCurScope(), D);
  }
  ~FNContextRAII() {
    if (HasFunScope) {
      P.getActions().ActOnExitFunctionContext();
      FnScope->Exit(); // Pop scope, and remove Decls from IdResolver
    }
    if (HasTemplateScope)
      TempScope->Exit();
    delete FnScope;
    delete TempScope;
    delete ThisScope;
  }
};
} // namespace

/// Parses clauses for 'declare simd' directive.
///    clause:
///      'inbranch' | 'notinbranch'
///      'simdlen' '(' <expr> ')'
///      { 'uniform' '(' <argument_list> ')' }
///      { 'aligned '(' <argument_list> [ ':' <alignment> ] ')' }
///      { 'linear '(' <argument_list> [ ':' <step> ] ')' }
static bool parseDeclareSimdClauses(
    Parser &P, ACCDeclareSimdDeclAttr::BranchStateTy &BS, ExprResult &SimdLen,
    SmallVectorImpl<Expr *> &Uniforms, SmallVectorImpl<Expr *> &Aligneds,
    SmallVectorImpl<Expr *> &Alignments, SmallVectorImpl<Expr *> &Linears,
    SmallVectorImpl<unsigned> &LinModifiers, SmallVectorImpl<Expr *> &Steps) {
  SourceRange BSRange;
  const Token &Tok = P.getCurToken();
  bool IsError = false;
  while (Tok.isNot(tok::annot_pragma_openacc_end)) {
    if (Tok.isNot(tok::identifier))
      break;
    ACCDeclareSimdDeclAttr::BranchStateTy Out;
    IdentifierInfo *II = Tok.getIdentifierInfo();
    StringRef ClauseName = II->getName();
    // Parse 'inranch|notinbranch' clauses.
    if (ACCDeclareSimdDeclAttr::ConvertStrToBranchStateTy(ClauseName, Out)) {
      if (BS != ACCDeclareSimdDeclAttr::BS_Undefined && BS != Out) {
        P.Diag(Tok, diag::err_acc_declare_simd_inbranch_notinbranch)
            << ClauseName
            << ACCDeclareSimdDeclAttr::ConvertBranchStateTyToStr(BS) << BSRange;
        IsError = true;
      }
      BS = Out;
      BSRange = SourceRange(Tok.getLocation(), Tok.getEndLoc());
      P.ConsumeToken();
    } else if (ClauseName.equals("simdlen")) {
      if (SimdLen.isUsable()) {
        P.Diag(Tok, diag::err_acc_more_one_clause)
            << getOpenACCDirectiveName(ACCD_declare_simd) << ClauseName << 0;
        IsError = true;
      }
      P.ConsumeToken();
      SourceLocation RLoc;
      SimdLen = P.ParseOpenACCParensExpr(ClauseName, RLoc);
      if (SimdLen.isInvalid())
        IsError = true;
    } else {
      OpenACCClauseKind CKind = getOpenACCClauseKind(ClauseName);
      if (CKind == ACCC_uniform || CKind == ACCC_aligned ||
          CKind == ACCC_linear) {
        Parser::OpenACCVarListDataTy Data;
        auto *Vars = &Uniforms;
        if (CKind == ACCC_aligned)
          Vars = &Aligneds;
        else if (CKind == ACCC_linear)
          Vars = &Linears;

        P.ConsumeToken();
        if (P.ParseOpenACCVarList(ACCD_declare_simd,
                                 getOpenACCClauseKind(ClauseName), *Vars, Data))
          IsError = true;
        if (CKind == ACCC_aligned)
          Alignments.append(Aligneds.size() - Alignments.size(), Data.TailExpr);
        else if (CKind == ACCC_linear) {
          if (P.getActions().CheckOpenACCLinearModifier(Data.LinKind,
                                                       Data.DepLinMapLoc))
            Data.LinKind = ACCC_LINEAR_val;
          LinModifiers.append(Linears.size() - LinModifiers.size(),
                              Data.LinKind);
          Steps.append(Linears.size() - Steps.size(), Data.TailExpr);
        }
      } else
        // TODO: add parsing of other clauses.
        break;
    }
    // Skip ',' if any.
    if (Tok.is(tok::comma))
      P.ConsumeToken();
  }
  return IsError;
}

/// Parse clauses for '#pragma acc declare simd'.
Parser::DeclGroupPtrTy
Parser::ParseACCDeclareSimdClauses(Parser::DeclGroupPtrTy Ptr,
                                   CachedTokens &Toks, SourceLocation Loc) {
  PP.EnterToken(Tok);
  PP.EnterTokenStream(Toks, /*DisableMacroExpansion=*/true);
  // Consume the previously pushed token.
  ConsumeAnyToken(/*ConsumeCodeCompletionTok=*/true);

  FNContextRAII FnContext(*this, Ptr);
  ACCDeclareSimdDeclAttr::BranchStateTy BS =
      ACCDeclareSimdDeclAttr::BS_Undefined;
  ExprResult Simdlen;
  SmallVector<Expr *, 4> Uniforms;
  SmallVector<Expr *, 4> Aligneds;
  SmallVector<Expr *, 4> Alignments;
  SmallVector<Expr *, 4> Linears;
  SmallVector<unsigned, 4> LinModifiers;
  SmallVector<Expr *, 4> Steps;
  bool IsError =
      parseDeclareSimdClauses(*this, BS, Simdlen, Uniforms, Aligneds,
                              Alignments, Linears, LinModifiers, Steps);
  // Need to check for extra tokens.
  if (Tok.isNot(tok::annot_pragma_openacc_end)) {
    Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
        << getOpenACCDirectiveName(ACCD_declare_simd);
    while (Tok.isNot(tok::annot_pragma_openacc_end))
      ConsumeAnyToken();
  }
  // Skip the last annot_pragma_openacc_end.
  SourceLocation EndLoc = ConsumeAnnotationToken();
  if (!IsError) {
    return Actions.ActOnOpenACCDeclareSimdDirective(
        Ptr, BS, Simdlen.get(), Uniforms, Aligneds, Alignments, Linears,
        LinModifiers, Steps, SourceRange(Loc, EndLoc));
  }
  return Ptr;
}

/// \brief Parsing of declarative OpenACC directives.
///
///       threadprivate-directive:
///         annot_pragma_openacc 'threadprivate' simple-variable-list
///         annot_pragma_openacc_end
///
///       declare-reduction-directive:
///        annot_pragma_openacc 'declare' 'reduction' [...]
///        annot_pragma_openacc_end
///
///       declare-simd-directive:
///         annot_pragma_openacc 'declare simd' {<clause> [,]}
///         annot_pragma_openacc_end
///         <function declaration/definition>
///
Parser::DeclGroupPtrTy Parser::ParseOpenACCDeclarativeDirectiveWithExtDecl(
    AccessSpecifier &AS, ParsedAttributesWithRange &Attrs,
    DeclSpec::TST TagType, Decl *Tag) {
  assert(Tok.is(tok::annot_pragma_openacc) && "Not an OpenACC directive!");
  ParenBraceBracketBalancer BalancerRAIIObj(*this);

  SourceLocation Loc = ConsumeAnnotationToken();
  auto DKind = ParseOpenACCDirectiveKind(*this);

  switch (DKind) {
  case ACCD_threadprivate: {
    ConsumeToken();
    ThreadprivateListParserHelper Helper(this);
    if (!ParseOpenACCSimpleVarList(ACCD_threadprivate, Helper, true)) {
      // The last seen token is annot_pragma_openacc_end - need to check for
      // extra tokens.
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
            << getOpenACCDirectiveName(ACCD_threadprivate);
        SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
      }
      // Skip the last annot_pragma_openacc_end.
      ConsumeAnnotationToken();
      return Actions.ActOnOpenACCThreadprivateDirective(Loc,
                                                       Helper.getIdentifiers());
    }
    break;
  }
  case ACCD_declare_reduction:
    ConsumeToken();
    if (auto Res = ParseOpenACCDeclareReductionDirective(AS)) {
      // The last seen token is annot_pragma_openacc_end - need to check for
      // extra tokens.
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
            << getOpenACCDirectiveName(ACCD_declare_reduction);
        while (Tok.isNot(tok::annot_pragma_openacc_end))
          ConsumeAnyToken();
      }
      // Skip the last annot_pragma_openacc_end.
      ConsumeAnnotationToken();
      return Res;
    }
    break;
  case ACCD_declare_simd: {
    // The syntax is:
    // { #pragma acc declare simd }
    // <function-declaration-or-definition>
    //
    ConsumeToken();
    CachedTokens Toks;
    while(Tok.isNot(tok::annot_pragma_openacc_end)) {
      Toks.push_back(Tok);
      ConsumeAnyToken();
    }
    Toks.push_back(Tok);
    ConsumeAnyToken();

    DeclGroupPtrTy Ptr;
    if (Tok.is(tok::annot_pragma_openacc))
      Ptr = ParseOpenACCDeclarativeDirectiveWithExtDecl(AS, Attrs, TagType, Tag);
    else if (Tok.isNot(tok::r_brace) && !isEofOrEom()) {
      // Here we expect to see some function declaration.
      if (AS == AS_none) {
        assert(TagType == DeclSpec::TST_unspecified);
        MaybeParseCXX11Attributes(Attrs);
        ParsingDeclSpec PDS(*this);
        Ptr = ParseExternalDeclaration(Attrs, &PDS);
      } else {
        Ptr =
            ParseCXXClassMemberDeclarationWithPragmas(AS, Attrs, TagType, Tag);
      }
    }
    if (!Ptr) {
      Diag(Loc, diag::err_acc_decl_in_declare_simd);
      return DeclGroupPtrTy();
    }
    return ParseACCDeclareSimdClauses(Ptr, Toks, Loc);
  }
  case ACCD_declare_target: {
    SourceLocation DTLoc = ConsumeAnyToken();
    if (Tok.isNot(tok::annot_pragma_openacc_end)) {
      // OpenACC 4.5 syntax with list of entities.
      llvm::SmallSetVector<const NamedDecl*, 16> SameDirectiveDecls;
      while (Tok.isNot(tok::annot_pragma_openacc_end)) {
        ACCDeclareTargetDeclAttr::MapTypeTy MT =
            ACCDeclareTargetDeclAttr::MT_To;
        if (Tok.is(tok::identifier)) {
          IdentifierInfo *II = Tok.getIdentifierInfo();
          StringRef ClauseName = II->getName();
          // Parse 'to|link' clauses.
          if (!ACCDeclareTargetDeclAttr::ConvertStrToMapTypeTy(ClauseName,
                                                               MT)) {
            Diag(Tok, diag::err_acc_declare_target_unexpected_clause)
                << ClauseName;
            break;
          }
          ConsumeToken();
        }
        auto Callback = [this, MT, &SameDirectiveDecls](
            CXXScopeSpec &SS, DeclarationNameInfo NameInfo) {
          Actions.ActOnOpenACCDeclareTargetName(getCurScope(), SS, NameInfo, MT,
                                               SameDirectiveDecls);
        };
        if (ParseOpenACCSimpleVarList(ACCD_declare_target, Callback, true))
          break;

        // Consume optional ','.
        if (Tok.is(tok::comma))
          ConsumeToken();
      }
      SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
      ConsumeAnyToken();
      return DeclGroupPtrTy();
    }

    // Skip the last annot_pragma_openacc_end.
    ConsumeAnyToken();

    if (!Actions.ActOnStartOpenACCDeclareTargetDirective(DTLoc))
      return DeclGroupPtrTy();

    DKind = ParseOpenACCDirectiveKind(*this);
    while (DKind != ACCD_end_declare_target && DKind != ACCD_declare_target &&
           Tok.isNot(tok::eof) && Tok.isNot(tok::r_brace)) {
      DeclGroupPtrTy Ptr;
      // Here we expect to see some function declaration.
      if (AS == AS_none) {
        assert(TagType == DeclSpec::TST_unspecified);
        MaybeParseCXX11Attributes(Attrs);
        ParsingDeclSpec PDS(*this);
        Ptr = ParseExternalDeclaration(Attrs, &PDS);
      } else {
        Ptr =
            ParseCXXClassMemberDeclarationWithPragmas(AS, Attrs, TagType, Tag);
      }
      if (Tok.isAnnotation() && Tok.is(tok::annot_pragma_openacc)) {
        TentativeParsingAction TPA(*this);
        ConsumeAnnotationToken();
        DKind = ParseOpenACCDirectiveKind(*this);
        if (DKind != ACCD_end_declare_target)
          TPA.Revert();
        else
          TPA.Commit();
      }
    }

    if (DKind == ACCD_end_declare_target) {
      ConsumeAnyToken();
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
            << getOpenACCDirectiveName(ACCD_end_declare_target);
        SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
      }
      // Skip the last annot_pragma_openacc_end.
      ConsumeAnyToken();
    } else {
      Diag(Tok, diag::err_acc_expected_end_declare_target);
      Diag(DTLoc, diag::note_matching) << "'#pragma acc declare target'";
    }
    Actions.ActOnFinishOpenACCDeclareTargetDirective();
    return DeclGroupPtrTy();
  }
  case ACCD_unknown:
    Diag(Tok, diag::err_acc_unknown_directive);
    break;
  case ACCD_parallel:
  case ACCD_simd:
  case ACCD_task:
  case ACCD_taskyield:
  case ACCD_barrier:
  case ACCD_taskwait:
  case ACCD_taskgroup:
  case ACCD_flush:
  case ACCD_for:
  case ACCD_for_simd:
  case ACCD_sections:
  case ACCD_section:
  case ACCD_single:
  case ACCD_master:
  case ACCD_ordered:
  case ACCD_critical:
  case ACCD_parallel_for:
  case ACCD_parallel_for_simd:
  case ACCD_parallel_sections:
  case ACCD_atomic:
  case ACCD_target:
  case ACCD_teams:
  case ACCD_cancellation_point:
  case ACCD_cancel:
  case ACCD_target_data:
  case ACCD_target_enter_data:
  case ACCD_target_exit_data:
  case ACCD_target_parallel:
  case ACCD_target_parallel_for:
  case ACCD_taskloop:
  case ACCD_taskloop_simd:
  case ACCD_distribute:
  case ACCD_end_declare_target:
  case ACCD_target_update:
  case ACCD_distribute_parallel_for:
  case ACCD_distribute_parallel_for_simd:
  case ACCD_distribute_simd:
  case ACCD_target_parallel_for_simd:
  case ACCD_target_simd:
  case ACCD_teams_distribute:
  case ACCD_teams_distribute_simd:
  case ACCD_teams_distribute_parallel_for_simd:
  case ACCD_teams_distribute_parallel_for:
  case ACCD_target_teams:
  case ACCD_target_teams_distribute:
  case ACCD_target_teams_distribute_parallel_for:
  case ACCD_target_teams_distribute_parallel_for_simd:
  case ACCD_target_teams_distribute_simd:
    Diag(Tok, diag::err_acc_unexpected_directive)
        << 1 << getOpenACCDirectiveName(DKind);
    break;
  }
  while (Tok.isNot(tok::annot_pragma_openacc_end))
    ConsumeAnyToken();
  ConsumeAnyToken();
  return nullptr;
}

/// \brief Parsing of declarative or executable OpenACC directives.
///
///       threadprivate-directive:
///         annot_pragma_openacc 'threadprivate' simple-variable-list
///         annot_pragma_openacc_end
///
///       declare-reduction-directive:
///         annot_pragma_openacc 'declare' 'reduction' '(' <reduction_id> ':'
///         <type> {',' <type>} ':' <expression> ')' ['initializer' '('
///         ('acc_priv' '=' <expression>|<function_call>) ')']
///         annot_pragma_openacc_end
///
///       executable-directive:
///         annot_pragma_openacc 'parallel' | 'simd' | 'for' | 'sections' |
///         'section' | 'single' | 'master' | 'critical' [ '(' <name> ')' ] |
///         'parallel for' | 'parallel sections' | 'task' | 'taskyield' |
///         'barrier' | 'taskwait' | 'flush' | 'ordered' | 'atomic' |
///         'for simd' | 'parallel for simd' | 'target' | 'target data' |
///         'taskgroup' | 'teams' | 'taskloop' | 'taskloop simd' |
///         'distribute' | 'target enter data' | 'target exit data' |
///         'target parallel' | 'target parallel for' |
///         'target update' | 'distribute parallel for' |
///         'distribute paralle for simd' | 'distribute simd' |
///         'target parallel for simd' | 'target simd' |
///         'teams distribute' | 'teams distribute simd' |
///         'teams distribute parallel for simd' |
///         'teams distribute parallel for' | 'target teams' |
///         'target teams distribute' |
///         'target teams distribute parallel for' |
///         'target teams distribute parallel for simd' |
///         'target teams distribute simd' {clause}
///         annot_pragma_openacc_end
///
StmtResult Parser::ParseOpenACCDeclarativeOrExecutableDirective(
    AllowedConstructsKind Allowed) {
  assert(Tok.is(tok::annot_pragma_openacc) && "Not an OpenACC directive!");
  ParenBraceBracketBalancer BalancerRAIIObj(*this);
  SmallVector<ACCClause *, 5> Clauses;
  SmallVector<llvm::PointerIntPair<ACCClause *, 1, bool>, ACCC_unknown + 1>
  FirstClauses(ACCC_unknown + 1);
  unsigned ScopeFlags = Scope::FnScope | Scope::DeclScope |
                        Scope::CompoundStmtScope | Scope::OpenACCDirectiveScope;
  SourceLocation Loc = ConsumeAnnotationToken(), EndLoc;
  auto DKind = ParseOpenACCDirectiveKind(*this);
  OpenACCDirectiveKind CancelRegion = ACCD_unknown;
  // Name of critical directive.
  DeclarationNameInfo DirName;
  StmtResult Directive = StmtError();
  bool HasAssociatedStatement = true;
  bool FlushHasClause = false;

  llvm::outs() << "Directive Kind is: " << getOpenACCDirectiveName(DKind) << "\n";

  switch (DKind) {
  case ACCD_threadprivate: {
    if (Allowed != ACK_Any) {
      Diag(Tok, diag::err_acc_immediate_directive)
          << getOpenACCDirectiveName(DKind) << 0;
    }
    ConsumeToken();
    ThreadprivateListParserHelper Helper(this);
    if (!ParseOpenACCSimpleVarList(ACCD_threadprivate, Helper, false)) {
      // The last seen token is annot_pragma_openacc_end - need to check for
      // extra tokens.
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
            << getOpenACCDirectiveName(ACCD_threadprivate);
        SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
      }
      DeclGroupPtrTy Res = Actions.ActOnOpenACCThreadprivateDirective(
          Loc, Helper.getIdentifiers());
      Directive = Actions.ActOnDeclStmt(Res, Loc, Tok.getLocation());
    }
    SkipUntil(tok::annot_pragma_openacc_end);
    break;
  }
  case ACCD_declare_reduction:
    ConsumeToken();
    if (auto Res = ParseOpenACCDeclareReductionDirective(/*AS=*/AS_none)) {
      // The last seen token is annot_pragma_openacc_end - need to check for
      // extra tokens.
      if (Tok.isNot(tok::annot_pragma_openacc_end)) {
        Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
            << getOpenACCDirectiveName(ACCD_declare_reduction);
        while (Tok.isNot(tok::annot_pragma_openacc_end))
          ConsumeAnyToken();
      }
      ConsumeAnyToken();
      Directive = Actions.ActOnDeclStmt(Res, Loc, Tok.getLocation());
    } else
      SkipUntil(tok::annot_pragma_openacc_end);
    break;
  case ACCD_flush:
    if (PP.LookAhead(0).is(tok::l_paren)) {
      FlushHasClause = true;
      // Push copy of the current token back to stream to properly parse
      // pseudo-clause ACCFlushClause.
      PP.EnterToken(Tok);
    }
    LLVM_FALLTHROUGH;
  case ACCD_taskyield:
  case ACCD_barrier:
  case ACCD_taskwait:
  case ACCD_cancellation_point:
  case ACCD_cancel:
  case ACCD_target_enter_data:
  case ACCD_target_exit_data:
  case ACCD_target_update:
    if (Allowed == ACK_Statements_OpenACCNonStandalone_OpenMPAnyExecutable
     || Allowed == ACK_Statements_OpenACCNonStandalone_OpenMPNonStandalone) {
      Diag(Tok, diag::err_acc_immediate_directive)
          << getOpenACCDirectiveName(DKind) << 0;
    }
    HasAssociatedStatement = false;
    // Fall through for further analysis.
    LLVM_FALLTHROUGH;
  case ACCD_parallel:
  case ACCD_simd:
  case ACCD_for:
  case ACCD_for_simd:
  case ACCD_sections:
  case ACCD_single:
  case ACCD_section:
  case ACCD_master:
  case ACCD_critical:
  case ACCD_parallel_for:
  case ACCD_parallel_for_simd:
  case ACCD_parallel_sections:
  case ACCD_task:
  case ACCD_ordered:
  case ACCD_atomic:
  case ACCD_target:
  case ACCD_teams:
  case ACCD_taskgroup:
  case ACCD_target_data:
  case ACCD_target_parallel:
  case ACCD_target_parallel_for:
  case ACCD_taskloop:
  case ACCD_taskloop_simd:
  case ACCD_distribute:
  case ACCD_distribute_parallel_for:
  case ACCD_distribute_parallel_for_simd:
  case ACCD_distribute_simd:
  case ACCD_target_parallel_for_simd:
  case ACCD_target_simd:
  case ACCD_teams_distribute:
  case ACCD_teams_distribute_simd:
  case ACCD_teams_distribute_parallel_for_simd:
  case ACCD_teams_distribute_parallel_for:
  case ACCD_target_teams:
  case ACCD_target_teams_distribute:
  case ACCD_target_teams_distribute_parallel_for:
  case ACCD_target_teams_distribute_parallel_for_simd:
  case ACCD_target_teams_distribute_simd: {
    ConsumeToken();
    // Parse directive name of the 'critical' directive if any.
    if (DKind == ACCD_critical) {
      BalancedDelimiterTracker T(*this, tok::l_paren,
                                 tok::annot_pragma_openacc_end);
      if (!T.consumeOpen()) {
        if (Tok.isAnyIdentifier()) {
          DirName =
              DeclarationNameInfo(Tok.getIdentifierInfo(), Tok.getLocation());
          ConsumeAnyToken();
        } else {
          Diag(Tok, diag::err_acc_expected_identifier_for_critical);
        }
        T.consumeClose();
      }
    } else if (DKind == ACCD_cancellation_point || DKind == ACCD_cancel) {
      CancelRegion = ParseOpenACCDirectiveKind(*this);
      if (Tok.isNot(tok::annot_pragma_openacc_end))
        ConsumeToken();
    }

    if (isOpenACCLoopDirective(DKind)){
      llvm::outs() << "------------ isOpenACCLoopDirective! ------------\n";
      ScopeFlags |= Scope::OpenACCLoopDirectiveScope;
    }
    if (isOpenACCSimdDirective(DKind))
      ScopeFlags |= Scope::OpenACCSimdDirectiveScope;
    ParseScope ACCDirectiveScope(this, ScopeFlags);
    Actions.StartOpenACCDSABlock(DKind, DirName, Actions.getCurScope(), Loc);

    llvm::outs() << "------------ Consuming other toks ------------\n";
    while (Tok.isNot(tok::annot_pragma_openacc_end)) {
      OpenACCClauseKind CKind =
          Tok.isAnnotation()
              ? ACCC_unknown
              : FlushHasClause ? ACCC_flush
                               : getOpenACCClauseKind(PP.getSpelling(Tok));

      llvm::outs() << "------------ OpenACCClauseKind is: " << getOpenACCClauseName(CKind) << " --------------- \n";
      Actions.StartOpenACCClause(CKind);
      FlushHasClause = false;
      ACCClause *Clause =
          ParseOpenACCClause(DKind, CKind, !FirstClauses[CKind].getInt());
      FirstClauses[CKind].setInt(true);
      if (Clause) {
        FirstClauses[CKind].setPointer(Clause);
        Clauses.push_back(Clause);
      }

      // Skip ',' if any.
      if (Tok.is(tok::comma))
        ConsumeToken();
      Actions.EndOpenACCClause();
    }
    // End location of the directive.
    EndLoc = Tok.getLocation();
    // Consume final annot_pragma_openacc_end.
    ConsumeAnnotationToken();
    llvm::outs() << "------------ Consuming tok annot_pragma_openacc_end ------------\n";

    // OpenACC [2.13.8, ordered Construct, Syntax]
    // If the depend clause is specified, the ordered construct is a stand-alone
    // directive.
    if (DKind == ACCD_ordered && FirstClauses[ACCC_depend].getInt()) {
      if (Allowed == ACK_Statements_OpenACCNonStandalone_OpenMPAnyExecutable
       || Allowed == ACK_Statements_OpenACCNonStandalone_OpenMPNonStandalone) {
        Diag(Loc, diag::err_acc_immediate_directive)
            << getOpenACCDirectiveName(DKind) << 1
            << getOpenACCClauseName(ACCC_depend);
      }
      HasAssociatedStatement = false;
    }
    StmtResult AssociatedStmt;
    if (HasAssociatedStatement) {
      // The body is a block scope like in Lambdas and Blocks.
      Actions.ActOnOpenACCRegionStart(DKind, getCurScope());
      // FIXME: We create a bogus CompoundStmt scope to hold the contents of
      // the captured region. Code elsewhere assumes that any FunctionScopeInfo
      // should have at least one compound statement scope within it.
      AssociatedStmt = (Sema::CompoundScopeRAII(Actions), ParseStatement());
      AssociatedStmt = Actions.ActOnOpenACCRegionEnd(AssociatedStmt, Clauses);
    } else if (DKind == ACCD_target_update || DKind == ACCD_target_enter_data ||
               DKind == ACCD_target_exit_data) {
      Actions.ActOnOpenACCRegionStart(DKind, getCurScope());
      AssociatedStmt = (Sema::CompoundScopeRAII(Actions),
                        Actions.ActOnCompoundStmt(Loc, Loc, llvm::None,
                                                  /*isStmtExpr=*/false));
      AssociatedStmt = Actions.ActOnOpenACCRegionEnd(AssociatedStmt, Clauses);
    }
    Directive = Actions.ActOnOpenACCExecutableDirective(
        DKind, DirName, CancelRegion, Clauses, AssociatedStmt.get(), Loc,
        EndLoc);
    // Exit scope.
    Actions.EndOpenACCDSABlock(Directive.get());
    ACCDirectiveScope.Exit();
    break;
  }
  case ACCD_declare_simd:
  case ACCD_declare_target:
  case ACCD_end_declare_target:
    Diag(Tok, diag::err_acc_unexpected_directive)
        << 1 << getOpenACCDirectiveName(DKind);
    SkipUntil(tok::annot_pragma_openacc_end);
    break;
  case ACCD_unknown:
    Diag(Tok, diag::err_acc_unknown_directive);
    SkipUntil(tok::annot_pragma_openacc_end);
    break;
  }

  return Directive;
}

// Parses simple list:
//   simple-variable-list:
//         '(' id-expression {, id-expression} ')'
//
bool Parser::ParseOpenACCSimpleVarList(
    OpenACCDirectiveKind Kind,
    const llvm::function_ref<void(CXXScopeSpec &, DeclarationNameInfo)> &
        Callback,
    bool AllowScopeSpecifier) {
  // Parse '('.
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after,
                         getOpenACCDirectiveName(Kind)))
    return true;
  bool IsCorrect = true;
  bool NoIdentIsFound = true;

  // Read tokens while ')' or annot_pragma_openacc_end is not found.
  while (Tok.isNot(tok::r_paren) && Tok.isNot(tok::annot_pragma_openacc_end)) {
    CXXScopeSpec SS;
    SourceLocation TemplateKWLoc;
    UnqualifiedId Name;
    // Read var name.
    Token PrevTok = Tok;
    NoIdentIsFound = false;

    if (AllowScopeSpecifier && getLangOpts().CPlusPlus &&
        ParseOptionalCXXScopeSpecifier(SS, nullptr, false)) {
      IsCorrect = false;
      SkipUntil(tok::comma, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    } else if (ParseUnqualifiedId(SS, false, false, false, false, nullptr,
                                  TemplateKWLoc, Name)) {
      IsCorrect = false;
      SkipUntil(tok::comma, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    } else if (Tok.isNot(tok::comma) && Tok.isNot(tok::r_paren) &&
               Tok.isNot(tok::annot_pragma_openacc_end)) {
      IsCorrect = false;
      SkipUntil(tok::comma, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
      Diag(PrevTok.getLocation(), diag::err_expected)
          << tok::identifier
          << SourceRange(PrevTok.getLocation(), PrevTokLocation);
    } else {
      Callback(SS, Actions.GetNameFromUnqualifiedId(Name));
    }
    // Consume ','.
    if (Tok.is(tok::comma)) {
      ConsumeToken();
    }
  }

  if (NoIdentIsFound) {
    Diag(Tok, diag::err_expected) << tok::identifier;
    IsCorrect = false;
  }

  // Parse ')'.
  IsCorrect = !T.consumeClose() && IsCorrect;

  return !IsCorrect;
}

/// \brief Parsing of OpenACC clauses.
///
///    clause:
///       if-clause | final-clause | num_threads-clause | safelen-clause |
///       default-clause | private-clause | firstprivate-clause | shared-clause
///       | linear-clause | aligned-clause | collapse-clause |
///       lastprivate-clause | reduction-clause | proc_bind-clause |
///       schedule-clause | copyin-clause | copyprivate-clause | untied-clause |
///       mergeable-clause | flush-clause | read-clause | write-clause |
///       update-clause | capture-clause | seq_cst-clause | device-clause |
///       simdlen-clause | threads-clause | simd-clause | num_teams-clause |
///       thread_limit-clause | priority-clause | grainsize-clause |
///       nogroup-clause | num_tasks-clause | hint-clause | to-clause |
///       from-clause | is_device_ptr-clause | task_reduction-clause |
///       in_reduction-clause
///
ACCClause *Parser::ParseOpenACCClause(OpenACCDirectiveKind DKind,
                                     OpenACCClauseKind CKind, bool FirstClause) {
  ACCClause *Clause = nullptr;
  bool ErrorFound = false;
  bool WrongDirective = false;
  // Check if clause is allowed for the given directive.
  if (CKind != ACCC_unknown && !isAllowedClauseForDirective(DKind, CKind)) {
    Diag(Tok, diag::err_acc_unexpected_clause) << getOpenACCClauseName(CKind)
                                               << getOpenACCDirectiveName(DKind);
    ErrorFound = true;
    WrongDirective = true;
  }

  switch (CKind) {
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_ordered:
  case ACCC_device:
  case ACCC_num_teams:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_num_tasks:
  case ACCC_hint:
    // OpenACC [2.5, Restrictions]
    //  At most one num_threads clause can appear on the directive.
    // OpenACC [2.8.1, simd construct, Restrictions]
    //  Only one safelen  clause can appear on a simd directive.
    //  Only one simdlen  clause can appear on a simd directive.
    //  Only one collapse clause can appear on a simd directive.
    // OpenACC [2.9.1, target data construct, Restrictions]
    //  At most one device clause can appear on the directive.
    // OpenACC [2.11.1, task Construct, Restrictions]
    //  At most one if clause can appear on the directive.
    //  At most one final clause can appear on the directive.
    // OpenACC [teams Construct, Restrictions]
    //  At most one num_teams clause can appear on the directive.
    //  At most one thread_limit clause can appear on the directive.
    // OpenACC [2.9.1, task Construct, Restrictions]
    // At most one priority clause can appear on the directive.
    // OpenACC [2.9.2, taskloop Construct, Restrictions]
    // At most one grainsize clause can appear on the directive.
    // OpenACC [2.9.2, taskloop Construct, Restrictions]
    // At most one num_tasks clause can appear on the directive.
    if (!FirstClause) {
      Diag(Tok, diag::err_acc_more_one_clause)
          << getOpenACCDirectiveName(DKind) << getOpenACCClauseName(CKind) << 0;
      ErrorFound = true;
    }

    if (CKind == ACCC_ordered && PP.LookAhead(/*N=*/0).isNot(tok::l_paren))
      Clause = ParseOpenACCClause(CKind, WrongDirective);
    else
      Clause = ParseOpenACCSingleExprClause(CKind, WrongDirective);
    break;
  case ACCC_default:
  case ACCC_proc_bind:
    // OpenACC [2.14.3.1, Restrictions]
    //  Only a single default clause may be specified on a parallel, task or
    //  teams directive.
    // OpenACC [2.5, parallel Construct, Restrictions]
    //  At most one proc_bind clause can appear on the directive.
    if (!FirstClause) {
      Diag(Tok, diag::err_acc_more_one_clause)
          << getOpenACCDirectiveName(DKind) << getOpenACCClauseName(CKind) << 0;
      ErrorFound = true;
    }

    Clause = ParseOpenACCSimpleClause(CKind, WrongDirective);
    break;
  case ACCC_schedule:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
    // OpenACC [2.7.1, Restrictions, p. 3]
    //  Only one schedule clause can appear on a loop directive.
    // OpenACC [2.10.4, Restrictions, p. 106]
    //  At most one defaultmap clause can appear on the directive.
    if (!FirstClause) {
      Diag(Tok, diag::err_acc_more_one_clause)
          << getOpenACCDirectiveName(DKind) << getOpenACCClauseName(CKind) << 0;
      ErrorFound = true;
    }
    LLVM_FALLTHROUGH;

  case ACCC_if:
    Clause = ParseOpenACCSingleExprWithArgClause(CKind, WrongDirective);
    break;
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_nogroup:
    // OpenACC [2.7.1, Restrictions, p. 9]
    //  Only one ordered clause can appear on a loop directive.
    // OpenACC [2.7.1, Restrictions, C/C++, p. 4]
    //  Only one nowait clause can appear on a for directive.
    if (!FirstClause) {
      Diag(Tok, diag::err_acc_more_one_clause)
          << getOpenACCDirectiveName(DKind) << getOpenACCClauseName(CKind) << 0;
      ErrorFound = true;
    }

    Clause = ParseOpenACCClause(CKind, WrongDirective);
    break;
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_shared:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_linear:
  case ACCC_aligned:
  case ACCC_copyin:
  case ACCC_copyprivate:
  case ACCC_flush:
  case ACCC_depend:
  case ACCC_map:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    Clause = ParseOpenACCVarListClause(DKind, CKind, WrongDirective);
    break;
  case ACCC_unknown:
    Diag(Tok, diag::warn_acc_extra_tokens_at_eol)
        << getOpenACCDirectiveName(DKind);
    SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
    break;
  case ACCC_threadprivate:
  case ACCC_uniform:
    if (!WrongDirective)
      Diag(Tok, diag::err_acc_unexpected_clause)
          << getOpenACCClauseName(CKind) << getOpenACCDirectiveName(DKind);
    SkipUntil(tok::comma, tok::annot_pragma_openacc_end, StopBeforeMatch);
    break;
  }
  return ErrorFound ? nullptr : Clause;
}

/// Parses simple expression in parens for single-expression clauses of OpenACC
/// constructs.
/// \param RLoc Returned location of right paren.
ExprResult Parser::ParseOpenACCParensExpr(StringRef ClauseName,
                                         SourceLocation &RLoc) {
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after, ClauseName.data()))
    return ExprError();

  SourceLocation ELoc = Tok.getLocation();
  ExprResult LHS(ParseCastExpression(
      /*isUnaryExpression=*/false, /*isAddressOfOperand=*/false, NotTypeCast));
  ExprResult Val(ParseRHSOfBinaryExpression(LHS, prec::Conditional));
  Val = Actions.ActOnFinishFullExpr(Val.get(), ELoc);

  // Parse ')'.
  T.consumeClose();

  RLoc = T.getCloseLocation();
  return Val;
}

/// \brief Parsing of OpenACC clauses with single expressions like 'final',
/// 'collapse', 'safelen', 'num_threads', 'simdlen', 'num_teams',
/// 'thread_limit', 'simdlen', 'priority', 'grainsize', 'num_tasks' or 'hint'.
///
///    final-clause:
///      'final' '(' expression ')'
///
///    num_threads-clause:
///      'num_threads' '(' expression ')'
///
///    safelen-clause:
///      'safelen' '(' expression ')'
///
///    simdlen-clause:
///      'simdlen' '(' expression ')'
///
///    collapse-clause:
///      'collapse' '(' expression ')'
///
///    priority-clause:
///      'priority' '(' expression ')'
///
///    grainsize-clause:
///      'grainsize' '(' expression ')'
///
///    num_tasks-clause:
///      'num_tasks' '(' expression ')'
///
///    hint-clause:
///      'hint' '(' expression ')'
///
ACCClause *Parser::ParseOpenACCSingleExprClause(OpenACCClauseKind Kind,
                                               bool ParseOnly) {
  SourceLocation Loc = ConsumeToken();
  SourceLocation LLoc = Tok.getLocation();
  SourceLocation RLoc;

  ExprResult Val = ParseOpenACCParensExpr(getOpenACCClauseName(Kind), RLoc);

  if (Val.isInvalid())
    return nullptr;

  if (ParseOnly)
    return nullptr;
  return Actions.ActOnOpenACCSingleExprClause(Kind, Val.get(), Loc, LLoc, RLoc);
}

/// \brief Parsing of simple OpenACC clauses like 'default' or 'proc_bind'.
///
///    default-clause:
///         'default' '(' 'none' | 'shared' ')
///
///    proc_bind-clause:
///         'proc_bind' '(' 'master' | 'close' | 'spread' ')
///
ACCClause *Parser::ParseOpenACCSimpleClause(OpenACCClauseKind Kind,
                                           bool ParseOnly) {
  SourceLocation Loc = Tok.getLocation();
  SourceLocation LOpen = ConsumeToken();
  // Parse '('.
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after,
                         getOpenACCClauseName(Kind)))
    return nullptr;

  unsigned Type = getOpenACCSimpleClauseType(
      Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok));
  SourceLocation TypeLoc = Tok.getLocation();
  if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
      Tok.isNot(tok::annot_pragma_openacc_end))
    ConsumeAnyToken();

  // Parse ')'.
  T.consumeClose();

  if (ParseOnly)
    return nullptr;
  return Actions.ActOnOpenACCSimpleClause(Kind, Type, TypeLoc, LOpen, Loc,
                                         Tok.getLocation());
}

/// \brief Parsing of OpenACC clauses like 'ordered'.
///
///    ordered-clause:
///         'ordered'
///
///    nowait-clause:
///         'nowait'
///
///    untied-clause:
///         'untied'
///
///    mergeable-clause:
///         'mergeable'
///
///    read-clause:
///         'read'
///
///    threads-clause:
///         'threads'
///
///    simd-clause:
///         'simd'
///
///    nogroup-clause:
///         'nogroup'
///
ACCClause *Parser::ParseOpenACCClause(OpenACCClauseKind Kind, bool ParseOnly) {
  SourceLocation Loc = Tok.getLocation();
  ConsumeAnyToken();

  if (ParseOnly)
    return nullptr;
  return Actions.ActOnOpenACCClause(Kind, Loc, Tok.getLocation());
}


/// \brief Parsing of OpenACC clauses with single expressions and some additional
/// argument like 'schedule' or 'dist_schedule'.
///
///    schedule-clause:
///      'schedule' '(' [ modifier [ ',' modifier ] ':' ] kind [',' expression ]
///      ')'
///
///    if-clause:
///      'if' '(' [ directive-name-modifier ':' ] expression ')'
///
///    defaultmap:
///      'defaultmap' '(' modifier ':' kind ')'
///
ACCClause *Parser::ParseOpenACCSingleExprWithArgClause(OpenACCClauseKind Kind,
                                                      bool ParseOnly) {
  SourceLocation Loc = ConsumeToken();
  SourceLocation DelimLoc;
  // Parse '('.
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after,
                         getOpenACCClauseName(Kind)))
    return nullptr;

  ExprResult Val;
  SmallVector<unsigned, 4> Arg;
  SmallVector<SourceLocation, 4> KLoc;
  if (Kind == ACCC_schedule) {
    enum { Modifier1, Modifier2, ScheduleKind, NumberOfElements };
    Arg.resize(NumberOfElements);
    KLoc.resize(NumberOfElements);
    Arg[Modifier1] = ACCC_SCHEDULE_MODIFIER_unknown;
    Arg[Modifier2] = ACCC_SCHEDULE_MODIFIER_unknown;
    Arg[ScheduleKind] = ACCC_SCHEDULE_unknown;
    auto KindModifier = getOpenACCSimpleClauseType(
        Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok));
    if (KindModifier > ACCC_SCHEDULE_unknown) {
      // Parse 'modifier'
      Arg[Modifier1] = KindModifier;
      KLoc[Modifier1] = Tok.getLocation();
      if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
          Tok.isNot(tok::annot_pragma_openacc_end))
        ConsumeAnyToken();
      if (Tok.is(tok::comma)) {
        // Parse ',' 'modifier'
        ConsumeAnyToken();
        KindModifier = getOpenACCSimpleClauseType(
            Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok));
        Arg[Modifier2] = KindModifier > ACCC_SCHEDULE_unknown
                             ? KindModifier
                             : (unsigned)ACCC_SCHEDULE_unknown;
        KLoc[Modifier2] = Tok.getLocation();
        if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
            Tok.isNot(tok::annot_pragma_openacc_end))
          ConsumeAnyToken();
      }
      // Parse ':'
      if (Tok.is(tok::colon))
        ConsumeAnyToken();
      else
        Diag(Tok, diag::warn_pragma_expected_colon) << "schedule modifier";
      KindModifier = getOpenACCSimpleClauseType(
          Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok));
    }
    Arg[ScheduleKind] = KindModifier;
    KLoc[ScheduleKind] = Tok.getLocation();
    if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
        Tok.isNot(tok::annot_pragma_openacc_end))
      ConsumeAnyToken();
    if ((Arg[ScheduleKind] == ACCC_SCHEDULE_static ||
         Arg[ScheduleKind] == ACCC_SCHEDULE_dynamic ||
         Arg[ScheduleKind] == ACCC_SCHEDULE_guided) &&
        Tok.is(tok::comma))
      DelimLoc = ConsumeAnyToken();
  } else if (Kind == ACCC_dist_schedule) {
    Arg.push_back(getOpenACCSimpleClauseType(
        Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok)));
    KLoc.push_back(Tok.getLocation());
    if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
        Tok.isNot(tok::annot_pragma_openacc_end))
      ConsumeAnyToken();
    if (Arg.back() == ACCC_DIST_SCHEDULE_static && Tok.is(tok::comma))
      DelimLoc = ConsumeAnyToken();
  } else if (Kind == ACCC_defaultmap) {
    // Get a defaultmap modifier
    Arg.push_back(getOpenACCSimpleClauseType(
        Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok)));
    KLoc.push_back(Tok.getLocation());
    if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
        Tok.isNot(tok::annot_pragma_openacc_end))
      ConsumeAnyToken();
    // Parse ':'
    if (Tok.is(tok::colon))
      ConsumeAnyToken();
    else if (Arg.back() != ACCC_DEFAULTMAP_MODIFIER_unknown)
      Diag(Tok, diag::warn_pragma_expected_colon) << "defaultmap modifier";
    // Get a defaultmap kind
    Arg.push_back(getOpenACCSimpleClauseType(
        Kind, Tok.isAnnotation() ? "" : PP.getSpelling(Tok)));
    KLoc.push_back(Tok.getLocation());
    if (Tok.isNot(tok::r_paren) && Tok.isNot(tok::comma) &&
        Tok.isNot(tok::annot_pragma_openacc_end))
      ConsumeAnyToken();
  } else {
    assert(Kind == ACCC_if);
    KLoc.push_back(Tok.getLocation());
    TentativeParsingAction TPA(*this);
    Arg.push_back(ParseOpenACCDirectiveKind(*this));
    if (Arg.back() != ACCD_unknown) {
      ConsumeToken();
      if (Tok.is(tok::colon) && getLangOpts().OpenACC > 40) {
        TPA.Commit();
        DelimLoc = ConsumeToken();
      } else {
        TPA.Revert();
        Arg.back() = ACCD_unknown;
      }
    } else
      TPA.Revert();
  }

  bool NeedAnExpression = (Kind == ACCC_schedule && DelimLoc.isValid()) ||
                          (Kind == ACCC_dist_schedule && DelimLoc.isValid()) ||
                          Kind == ACCC_if;
  if (NeedAnExpression) {
    SourceLocation ELoc = Tok.getLocation();
    ExprResult LHS(ParseCastExpression(false, false, NotTypeCast));
    Val = ParseRHSOfBinaryExpression(LHS, prec::Conditional);
    Val = Actions.ActOnFinishFullExpr(Val.get(), ELoc);
  }

  // Parse ')'.
  T.consumeClose();

  if (NeedAnExpression && Val.isInvalid())
    return nullptr;

  if (ParseOnly)
    return nullptr;
  return Actions.ActOnOpenACCSingleExprWithArgClause(
      Kind, Arg, Val.get(), Loc, T.getOpenLocation(), KLoc, DelimLoc,
      T.getCloseLocation());
}

static bool ParseReductionId(Parser &P, CXXScopeSpec &ReductionIdScopeSpec,
                             UnqualifiedId &ReductionId) {
  SourceLocation TemplateKWLoc;
  if (ReductionIdScopeSpec.isEmpty()) {
    auto OOK = OO_None;
    switch (P.getCurToken().getKind()) {
    case tok::plus:
      OOK = OO_Plus;
      break;
    case tok::minus:
      OOK = OO_Minus;
      break;
    case tok::star:
      OOK = OO_Star;
      break;
    case tok::amp:
      OOK = OO_Amp;
      break;
    case tok::pipe:
      OOK = OO_Pipe;
      break;
    case tok::caret:
      OOK = OO_Caret;
      break;
    case tok::ampamp:
      OOK = OO_AmpAmp;
      break;
    case tok::pipepipe:
      OOK = OO_PipePipe;
      break;
    default:
      break;
    }
    if (OOK != OO_None) {
      SourceLocation OpLoc = P.ConsumeToken();
      SourceLocation SymbolLocations[] = {OpLoc, OpLoc, SourceLocation()};
      ReductionId.setOperatorFunctionId(OpLoc, OOK, SymbolLocations);
      return false;
    }
  }
  return P.ParseUnqualifiedId(ReductionIdScopeSpec, /*EnteringContext*/ false,
                              /*AllowDestructorName*/ false,
                              /*AllowConstructorName*/ false,
                              /*AllowDeductionGuide*/ false,
                              nullptr, TemplateKWLoc, ReductionId);
}

/// Parses clauses with list.
bool Parser::ParseOpenACCVarList(OpenACCDirectiveKind DKind,
                                OpenACCClauseKind Kind,
                                SmallVectorImpl<Expr *> &Vars,
                                OpenACCVarListDataTy &Data) {
  UnqualifiedId UnqualifiedReductionId;
  bool InvalidReductionId = false;
  bool MapTypeModifierSpecified = false;

  // Parse '('.
  BalancedDelimiterTracker T(*this, tok::l_paren, tok::annot_pragma_openacc_end);
  if (T.expectAndConsume(diag::err_expected_lparen_after,
                         getOpenACCClauseName(Kind)))
    return true;

  bool NeedRParenForLinear = false;
  BalancedDelimiterTracker LinearT(*this, tok::l_paren,
                                  tok::annot_pragma_openacc_end);
  // Handle reduction-identifier for reduction clause.
  if (Kind == ACCC_reduction || Kind == ACCC_task_reduction ||
      Kind == ACCC_in_reduction) {
    ColonProtectionRAIIObject ColonRAII(*this);
    if (getLangOpts().CPlusPlus)
      ParseOptionalCXXScopeSpecifier(Data.ReductionIdScopeSpec,
                                     /*ObjectType=*/nullptr,
                                     /*EnteringContext=*/false);
    InvalidReductionId = ParseReductionId(*this, Data.ReductionIdScopeSpec,
                                          UnqualifiedReductionId);
    if (InvalidReductionId) {
      SkipUntil(tok::colon, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    }
    if (Tok.is(tok::colon))
      Data.ColonLoc = ConsumeToken();
    else
      Diag(Tok, diag::warn_pragma_expected_colon) << "reduction identifier";
    if (!InvalidReductionId)
      Data.ReductionId =
          Actions.GetNameFromUnqualifiedId(UnqualifiedReductionId);
  } else if (Kind == ACCC_depend) {
  // Handle dependency type for depend clause.
    ColonProtectionRAIIObject ColonRAII(*this);
    Data.DepKind =
        static_cast<OpenACCDependClauseKind>(getOpenACCSimpleClauseType(
            Kind, Tok.is(tok::identifier) ? PP.getSpelling(Tok) : ""));
    Data.DepLinMapLoc = Tok.getLocation();

    if (Data.DepKind == ACCC_DEPEND_unknown) {
      SkipUntil(tok::colon, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    } else {
      ConsumeToken();
      // Special processing for depend(source) clause.
      if (DKind == ACCD_ordered && Data.DepKind == ACCC_DEPEND_source) {
        // Parse ')'.
        T.consumeClose();
        return false;
      }
    }
    if (Tok.is(tok::colon))
      Data.ColonLoc = ConsumeToken();
    else {
      Diag(Tok, DKind == ACCD_ordered ? diag::warn_pragma_acc_expected_colon_r_paren
                                      : diag::warn_pragma_expected_colon)
          << "dependency type";
    }
  } else if (Kind == ACCC_linear) {
    // Try to parse modifier if any.
    if (Tok.is(tok::identifier) && PP.LookAhead(0).is(tok::l_paren)) {
      Data.LinKind = static_cast<OpenACCLinearClauseKind>(
          getOpenACCSimpleClauseType(Kind, PP.getSpelling(Tok)));
      Data.DepLinMapLoc = ConsumeToken();
      LinearT.consumeOpen();
      NeedRParenForLinear = true;
    }
  } else if (Kind == ACCC_map) {
    // Handle map type for map clause.
    ColonProtectionRAIIObject ColonRAII(*this);

    /// The map clause modifier token can be either a identifier or the C++
    /// delete keyword.
    auto &&IsMapClauseModifierToken = [](const Token &Tok) -> bool {
      return Tok.isOneOf(tok::identifier, tok::kw_delete);
    };

    // The first identifier may be a list item, a map-type or a
    // map-type-modifier. The map modifier can also be delete which has the same
    // spelling of the C++ delete keyword.
    Data.MapType =
        IsMapClauseModifierToken(Tok)
            ? static_cast<OpenACCMapClauseKind>(
                  getOpenACCSimpleClauseType(Kind, PP.getSpelling(Tok)))
            : ACCC_MAP_unknown;
    Data.DepLinMapLoc = Tok.getLocation();
    bool ColonExpected = false;

    if (IsMapClauseModifierToken(Tok)) {
      if (PP.LookAhead(0).is(tok::colon)) {
        if (Data.MapType == ACCC_MAP_unknown)
          Diag(Tok, diag::err_acc_unknown_map_type);
        else if (Data.MapType == ACCC_MAP_always)
          Diag(Tok, diag::err_acc_map_type_missing);
        ConsumeToken();
      } else if (PP.LookAhead(0).is(tok::comma)) {
        if (IsMapClauseModifierToken(PP.LookAhead(1)) &&
            PP.LookAhead(2).is(tok::colon)) {
          Data.MapTypeModifier = Data.MapType;
          if (Data.MapTypeModifier != ACCC_MAP_always) {
            Diag(Tok, diag::err_acc_unknown_map_type_modifier);
            Data.MapTypeModifier = ACCC_MAP_unknown;
          } else
            MapTypeModifierSpecified = true;

          ConsumeToken();
          ConsumeToken();

          Data.MapType =
              IsMapClauseModifierToken(Tok)
                  ? static_cast<OpenACCMapClauseKind>(
                        getOpenACCSimpleClauseType(Kind, PP.getSpelling(Tok)))
                  : ACCC_MAP_unknown;
          if (Data.MapType == ACCC_MAP_unknown ||
              Data.MapType == ACCC_MAP_always)
            Diag(Tok, diag::err_acc_unknown_map_type);
          ConsumeToken();
        } else {
          Data.MapType = ACCC_MAP_tofrom;
          Data.IsMapTypeImplicit = true;
        }
      } else if (IsMapClauseModifierToken(PP.LookAhead(0))) {
        if (PP.LookAhead(1).is(tok::colon)) {
          Data.MapTypeModifier = Data.MapType;
          if (Data.MapTypeModifier != ACCC_MAP_always) {
            Diag(Tok, diag::err_acc_unknown_map_type_modifier);
            Data.MapTypeModifier = ACCC_MAP_unknown;
          } else
            MapTypeModifierSpecified = true;

          ConsumeToken();

          Data.MapType =
              IsMapClauseModifierToken(Tok)
                  ? static_cast<OpenACCMapClauseKind>(
                        getOpenACCSimpleClauseType(Kind, PP.getSpelling(Tok)))
                  : ACCC_MAP_unknown;
          if (Data.MapType == ACCC_MAP_unknown ||
              Data.MapType == ACCC_MAP_always)
            Diag(Tok, diag::err_acc_unknown_map_type);
          ConsumeToken();
        } else {
          Data.MapType = ACCC_MAP_tofrom;
          Data.IsMapTypeImplicit = true;
        }
      } else {
        Data.MapType = ACCC_MAP_tofrom;
        Data.IsMapTypeImplicit = true;
      }
    } else {
      Data.MapType = ACCC_MAP_tofrom;
      Data.IsMapTypeImplicit = true;
    }

    if (Tok.is(tok::colon))
      Data.ColonLoc = ConsumeToken();
    else if (ColonExpected)
      Diag(Tok, diag::warn_pragma_expected_colon) << "map type";
  }

  bool IsComma =
      (Kind != ACCC_reduction && Kind != ACCC_task_reduction &&
       Kind != ACCC_in_reduction && Kind != ACCC_depend && Kind != ACCC_map) ||
      (Kind == ACCC_reduction && !InvalidReductionId) ||
      (Kind == ACCC_map && Data.MapType != ACCC_MAP_unknown &&
       (!MapTypeModifierSpecified ||
        Data.MapTypeModifier == ACCC_MAP_always)) ||
      (Kind == ACCC_depend && Data.DepKind != ACCC_DEPEND_unknown);
  const bool MayHaveTail = (Kind == ACCC_linear || Kind == ACCC_aligned);
  while (IsComma || (Tok.isNot(tok::r_paren) && Tok.isNot(tok::colon) &&
                     Tok.isNot(tok::annot_pragma_openacc_end))) {
    ColonProtectionRAIIObject ColonRAII(*this, MayHaveTail);
    // Parse variable
    ExprResult VarExpr =
        Actions.CorrectDelayedTyposInExpr(ParseAssignmentExpression());
    if (VarExpr.isUsable())
      Vars.push_back(VarExpr.get());
    else {
      SkipUntil(tok::comma, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
    }
    // Skip ',' if any
    IsComma = Tok.is(tok::comma);
    if (IsComma)
      ConsumeToken();
    else if (Tok.isNot(tok::r_paren) &&
             Tok.isNot(tok::annot_pragma_openacc_end) &&
             (!MayHaveTail || Tok.isNot(tok::colon)))
      Diag(Tok, diag::err_acc_expected_punc)
          << ((Kind == ACCC_flush) ? getOpenACCDirectiveName(ACCD_flush)
                                   : getOpenACCClauseName(Kind))
          << (Kind == ACCC_flush);
  }

  // Parse ')' for linear clause with modifier.
  if (NeedRParenForLinear)
    LinearT.consumeClose();

  // Parse ':' linear-step (or ':' alignment).
  const bool MustHaveTail = MayHaveTail && Tok.is(tok::colon);
  if (MustHaveTail) {
    Data.ColonLoc = Tok.getLocation();
    SourceLocation ELoc = ConsumeToken();
    ExprResult Tail = ParseAssignmentExpression();
    Tail = Actions.ActOnFinishFullExpr(Tail.get(), ELoc);
    if (Tail.isUsable())
      Data.TailExpr = Tail.get();
    else
      SkipUntil(tok::comma, tok::r_paren, tok::annot_pragma_openacc_end,
                StopBeforeMatch);
  }

  // Parse ')'.
  T.consumeClose();
  if ((Kind == ACCC_depend && Data.DepKind != ACCC_DEPEND_unknown &&
       Vars.empty()) ||
      (Kind != ACCC_depend && Kind != ACCC_map && Vars.empty()) ||
      (MustHaveTail && !Data.TailExpr) || InvalidReductionId)
    return true;
  return false;
}

/// \brief Parsing of OpenACC clause 'private', 'firstprivate', 'lastprivate',
/// 'shared', 'copyin', 'copyprivate', 'flush', 'reduction', 'task_reduction' or
/// 'in_reduction'.
///
///    private-clause:
///       'private' '(' list ')'
///    firstprivate-clause:
///       'firstprivate' '(' list ')'
///    lastprivate-clause:
///       'lastprivate' '(' list ')'
///    shared-clause:
///       'shared' '(' list ')'
///    linear-clause:
///       'linear' '(' linear-list [ ':' linear-step ] ')'
///    aligned-clause:
///       'aligned' '(' list [ ':' alignment ] ')'
///    reduction-clause:
///       'reduction' '(' reduction-identifier ':' list ')'
///    task_reduction-clause:
///       'task_reduction' '(' reduction-identifier ':' list ')'
///    in_reduction-clause:
///       'in_reduction' '(' reduction-identifier ':' list ')'
///    copyprivate-clause:
///       'copyprivate' '(' list ')'
///    flush-clause:
///       'flush' '(' list ')'
///    depend-clause:
///       'depend' '(' in | out | inout : list | source ')'
///    map-clause:
///       'map' '(' [ [ always , ]
///          to | from | tofrom | alloc | release | delete ':' ] list ')';
///    to-clause:
///       'to' '(' list ')'
///    from-clause:
///       'from' '(' list ')'
///    use_device_ptr-clause:
///       'use_device_ptr' '(' list ')'
///    is_device_ptr-clause:
///       'is_device_ptr' '(' list ')'
///
/// For 'linear' clause linear-list may have the following forms:
///  list
///  modifier(list)
/// where modifier is 'val' (C) or 'ref', 'val' or 'uval'(C++).
ACCClause *Parser::ParseOpenACCVarListClause(OpenACCDirectiveKind DKind,
                                            OpenACCClauseKind Kind,
                                            bool ParseOnly) {
  SourceLocation Loc = Tok.getLocation();
  SourceLocation LOpen = ConsumeToken();
  SmallVector<Expr *, 4> Vars;
  OpenACCVarListDataTy Data;

  if (ParseOpenACCVarList(DKind, Kind, Vars, Data))
    return nullptr;

  if (ParseOnly)
    return nullptr;
  return Actions.ActOnOpenACCVarListClause(
      Kind, Vars, Data.TailExpr, Loc, LOpen, Data.ColonLoc, Tok.getLocation(),
      Data.ReductionIdScopeSpec, Data.ReductionId, Data.DepKind, Data.LinKind,
      Data.MapTypeModifier, Data.MapType, Data.IsMapTypeImplicit,
      Data.DepLinMapLoc);
}

