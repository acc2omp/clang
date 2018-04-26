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


/*
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
*/
} // namespace



// Map token string to extended OMP token kind that are
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


// TODO acc2mp
// Move this function from here
/// \brief Parsing of declarative or executable OpenACC directives.
///
///       threadprivate-directive:
///         annot_pragma_openacc 'threadprivate' simple-variable-list
///         annot_pragma_openacc_end
///
///       declare-reduction-directive:
///         annot_pragma_openacc 'declare' 'reduction' '(' <reduction_id> ':'
///         <type> {',' <type>} ':' <expression> ')' ['initializer' '('
///         ('omp_priv' '=' <expression>|<function_call>) ')']
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

  llvm::outs()<<"ParseOpenACCDeclarativeOrExecutableDirective ...\n";
  /*
  assert(Tok.is(tok::annot_pragma_openacc) && "Not an OpenACC directive!");
  ParenBraceBracketBalancer BalancerRAIIObj(*this);
  SmallVector<OMPClause *, 5> Clauses;
  SmallVector<llvm::PointerIntPair<OMPClause *, 1, bool>, OMPC_unknown + 1>
  FirstClauses(OMPC_unknown + 1);
  unsigned ScopeFlags = Scope::FnScope | Scope::DeclScope |
                        Scope::CompoundStmtScope | Scope::OpenMPDirectiveScope;
  SourceLocation Loc = ConsumeAnnotationToken(), EndLoc;

  auto DKind = ParseOpenACCDirectiveKind(*this);
  OpenACCDirectiveKind CancelRegion = ACCD_unknown;

  // Name of critical directive.
  DeclarationNameInfo DirName;
  StmtResult Directive = StmtError();
  bool HasAssociatedStatement = true;
  bool FlushHasClause = false;

  switch(DKind) {
    case ACCD_parallel:
       llvm::outs()<<"<<Parallel ACC directive Detected>>\n";
       break;
    default:
       llvm::outs()<<"<<Parallel ACC directive Detected>>\n";
       break;
  }
  */
  SkipUntil(tok::annot_pragma_openacc_end);
  return StmtError();
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

  while (Tok.isNot(tok::annot_pragma_openacc_end))
    ConsumeAnyToken();
  ConsumeAnyToken();
  return nullptr;
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
    Diag(Tok, diag::err_omp_unexpected_clause) << getOpenACCClauseName(CKind)
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
      Diag(Tok, diag::err_omp_more_one_clause)
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
      Diag(Tok, diag::err_omp_more_one_clause)
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
      Diag(Tok, diag::err_omp_more_one_clause)
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
      Diag(Tok, diag::err_omp_more_one_clause)
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
    Diag(Tok, diag::warn_omp_extra_tokens_at_eol)
        << getOpenACCDirectiveName(DKind);
    SkipUntil(tok::annot_pragma_openacc_end, StopBeforeMatch);
    break;
  case ACCC_threadprivate:
  case ACCC_uniform:
    if (!WrongDirective)
      Diag(Tok, diag::err_omp_unexpected_clause)
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

