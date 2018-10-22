//===--- CGStmtOpenACC.cpp - Emit LLVM Code from Statements ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This contains code to emit OpenACC nodes as LLVM code.
//
//===----------------------------------------------------------------------===//

#include "CGCleanup.h"
#include "CGOpenACCRuntime.h"
#include "CodeGenFunction.h"
#include "CodeGenModule.h"
#include "TargetInfo.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtOpenACC.h"
#include "clang/AST/DeclOpenACC.h"
#include "llvm/IR/CallSite.h"
using namespace clang;
using namespace CodeGen;

namespace {
/// Lexical scope for OpenACC executable constructs, that handles correct codegen
/// for captured expressions.
class ACCLexicalScope : public CodeGenFunction::LexicalScope {
  void emitPreInitStmt(CodeGenFunction &CGF, const ACCExecutableDirective &S) {
    for (const auto *C : S.clauses()) {
      if (auto *CPI = ACCClauseWithPreInit::get(C)) {
        if (auto *PreInit = cast_or_null<DeclStmt>(CPI->getPreInitStmt())) {
          for (const auto *I : PreInit->decls()) {
            if (!I->hasAttr<ACCCaptureNoInitAttr>())
              CGF.EmitVarDecl(cast<VarDecl>(*I));
            else {
              CodeGenFunction::AutoVarEmission Emission =
                  CGF.EmitAutoVarAlloca(cast<VarDecl>(*I));
              CGF.EmitAutoVarCleanups(Emission);
            }
          }
        }
      }
    }
  }
  CodeGenFunction::ACCPrivateScope InlinedShareds;

  static bool isCapturedVar(CodeGenFunction &CGF, const VarDecl *VD) {
    return CGF.LambdaCaptureFields.lookup(VD) ||
           (CGF.CapturedStmtInfo && CGF.CapturedStmtInfo->lookup(VD)) ||
           (CGF.CurCodeDecl && isa<BlockDecl>(CGF.CurCodeDecl));
  }

public:
  ACCLexicalScope(
      CodeGenFunction &CGF, const ACCExecutableDirective &S,
      const llvm::Optional<OpenACCDirectiveKind> CapturedRegion = llvm::None,
      const bool EmitPreInitStmt = true)
      : CodeGenFunction::LexicalScope(CGF, S.getSourceRange()),
        InlinedShareds(CGF) {
    if (EmitPreInitStmt)
      emitPreInitStmt(CGF, S);
    if (!CapturedRegion.hasValue())
      return;
    assert(S.hasAssociatedStmt() &&
           "Expected associated statement for inlined directive.");
    const CapturedStmt *CS = S.getCapturedStmt(*CapturedRegion);
    for (auto &C : CS->captures()) {
      if (C.capturesVariable() || C.capturesVariableByCopy()) {
        auto *VD = C.getCapturedVar();
        assert(VD == VD->getCanonicalDecl() &&
               "Canonical decl must be captured.");
        DeclRefExpr DRE(
            const_cast<VarDecl *>(VD),
            isCapturedVar(CGF, VD) || (CGF.CapturedStmtInfo &&
                                       InlinedShareds.isGlobalVarCaptured(VD)),
            VD->getType().getNonReferenceType(), VK_LValue, C.getLocation());
        InlinedShareds.addPrivate(VD, [&CGF, &DRE]() -> Address {
          return CGF.EmitLValue(&DRE).getAddress();
        });
      }
    }
    (void)InlinedShareds.Privatize();
  }
};

/// Lexical scope for OpenACC parallel construct, that handles correct codegen
/// for captured expressions.
class ACCParallelScope final : public ACCLexicalScope {
  bool EmitPreInitStmt(const ACCExecutableDirective &S) {
    OpenACCDirectiveKind Kind = S.getDirectiveKind();
    return !(isOpenACCTargetExecutionDirective(Kind) ||
             isOpenACCLoopBoundSharingDirective(Kind)) &&
           isOpenACCParallelDirective(Kind);
  }

public:
  ACCParallelScope(CodeGenFunction &CGF, const ACCExecutableDirective &S)
      : ACCLexicalScope(CGF, S, /*CapturedRegion=*/llvm::None,
                        EmitPreInitStmt(S)) {}
};

/// Lexical scope for OpenACC teams construct, that handles correct codegen
/// for captured expressions.
class ACCGangScope final : public ACCLexicalScope {
  bool EmitPreInitStmt(const ACCExecutableDirective &S) {
    OpenACCDirectiveKind Kind = S.getDirectiveKind();
    return !isOpenACCTargetExecutionDirective(Kind) &&
           isOpenACCGangDirective(Kind);
  }

public:
  ACCGangScope(CodeGenFunction &CGF, const ACCExecutableDirective &S)
      : ACCLexicalScope(CGF, S, /*CapturedRegion=*/llvm::None,
                        EmitPreInitStmt(S)) {}
};

/// Private scope for OpenACC loop-based directives, that supports capturing
/// of used expression from loop statement.
class ACCLoopScope : public CodeGenFunction::RunCleanupsScope {
  void emitPreInitStmt(CodeGenFunction &CGF, const ACCLoopLikeDirective &S) {
    CodeGenFunction::ACCPrivateScope PreCondScope(CGF);
    for (auto *E : S.counters()) {
      const auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
      (void)PreCondScope.addPrivate(VD, [&CGF, VD]() {
        return CGF.CreateMemTemp(VD->getType().getNonReferenceType());
      });
    }
    (void)PreCondScope.Privatize();
    if (auto *LD = dyn_cast<ACCLoopLikeDirective>(&S)) {
      if (auto *PreInits = cast_or_null<DeclStmt>(LD->getPreInits())) {
        for (const auto *I : PreInits->decls())
          CGF.EmitVarDecl(cast<VarDecl>(*I));
      }
    }
  }

public:
  ACCLoopScope(CodeGenFunction &CGF, const ACCLoopLikeDirective &S)
      : CodeGenFunction::RunCleanupsScope(CGF) {
    emitPreInitStmt(CGF, S);
  }
};

class ACCVectorLexicalScope : public CodeGenFunction::LexicalScope {
  CodeGenFunction::ACCPrivateScope InlinedShareds;

  static bool isCapturedVar(CodeGenFunction &CGF, const VarDecl *VD) {
    return CGF.LambdaCaptureFields.lookup(VD) ||
           (CGF.CapturedStmtInfo && CGF.CapturedStmtInfo->lookup(VD)) ||
           (CGF.CurCodeDecl && isa<BlockDecl>(CGF.CurCodeDecl) &&
            cast<BlockDecl>(CGF.CurCodeDecl)->capturesVariable(VD));
  }

public:
  ACCVectorLexicalScope(CodeGenFunction &CGF, const ACCExecutableDirective &S)
      : CodeGenFunction::LexicalScope(CGF, S.getSourceRange()),
        InlinedShareds(CGF) {
    for (const auto *C : S.clauses()) {
      if (auto *CPI = ACCClauseWithPreInit::get(C)) {
        if (auto *PreInit = cast_or_null<DeclStmt>(CPI->getPreInitStmt())) {
          for (const auto *I : PreInit->decls()) {
            if (!I->hasAttr<ACCCaptureNoInitAttr>())
              CGF.EmitVarDecl(cast<VarDecl>(*I));
            else {
              CodeGenFunction::AutoVarEmission Emission =
                  CGF.EmitAutoVarAlloca(cast<VarDecl>(*I));
              CGF.EmitAutoVarCleanups(Emission);
            }
          }
        }
      } else if (const auto *UDP = dyn_cast<ACCUseDevicePtrClause>(C)) {
        for (const Expr *E : UDP->varlists()) {
          const Decl *D = cast<DeclRefExpr>(E)->getDecl();
          if (const auto *OED = dyn_cast<ACCCapturedExprDecl>(D))
            CGF.EmitVarDecl(*OED);
        }
      }
    }
    if (!isOpenACCVectorDirective(S.getDirectiveKind()))
      CGF.EmitACCPrivateClause(S, InlinedShareds);
    if (const auto *TG = dyn_cast<ACCTaskgroupDirective>(&S)) {
      if (const Expr *E = TG->getReductionRef())
        CGF.EmitVarDecl(*cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl()));
    }
    const auto *CS = cast_or_null<CapturedStmt>(S.getAssociatedStmt());
    while (CS) {
      for (auto &C : CS->captures()) {
        if (C.capturesVariable() || C.capturesVariableByCopy()) {
          auto *VD = C.getCapturedVar();
          assert(VD == VD->getCanonicalDecl() &&
                 "Canonical decl must be captured.");
          DeclRefExpr DRE(const_cast<VarDecl *>(VD),
                          isCapturedVar(CGF, VD) ||
                              (CGF.CapturedStmtInfo &&
                               InlinedShareds.isGlobalVarCaptured(VD)),
                          VD->getType().getNonReferenceType(), VK_LValue,
                          C.getLocation());
          InlinedShareds.addPrivate(VD, [&CGF, &DRE]() -> Address {
            return CGF.EmitLValue(&DRE).getAddress();
          });
        }
      }
      CS = dyn_cast<CapturedStmt>(CS->getCapturedStmt());
    }
    (void)InlinedShareds.Privatize();
  }
};

} // namespace

static void emitCommonACCTargetDirective(CodeGenFunction &CGF,
                                         const ACCExecutableDirective &S,
                                         const ACCRegionCodeGenTy &CodeGen);

LValue CodeGenFunction::EmitACCSharedLValue(const Expr *E) {
  if (auto *OrigDRE = dyn_cast<DeclRefExpr>(E)) {
    if (auto *OrigVD = dyn_cast<VarDecl>(OrigDRE->getDecl())) {
      OrigVD = OrigVD->getCanonicalDecl();
      bool IsCaptured =
          LambdaCaptureFields.lookup(OrigVD) ||
          (CapturedStmtInfo && CapturedStmtInfo->lookup(OrigVD)) ||
          (CurCodeDecl && isa<BlockDecl>(CurCodeDecl));
      DeclRefExpr DRE(const_cast<VarDecl *>(OrigVD), IsCaptured,
                      OrigDRE->getType(), VK_LValue, OrigDRE->getExprLoc());
      return EmitLValue(&DRE);
    }
  }
  return EmitLValue(E);
}

llvm::Value *CodeGenFunction::getACCTypeSize(QualType Ty) {
  auto &C = getContext();
  llvm::Value *Size = nullptr;
  auto SizeInChars = C.getTypeSizeInChars(Ty);
  if (SizeInChars.isZero()) {
    // getACCTypeSizeInChars() returns 0 for a VLA.
    while (auto *VAT = C.getAsVariableArrayType(Ty)) {
      auto VlaSize = getVLASize(VAT);
      Ty = VlaSize.Type;
      Size = Size ? Builder.CreateNUWMul(Size, VlaSize.NumElts)
                  : VlaSize.NumElts;
    }
    SizeInChars = C.getTypeSizeInChars(Ty);
    if (SizeInChars.isZero())
      return llvm::ConstantInt::get(SizeTy, /*V=*/0);
    Size = Builder.CreateNUWMul(Size, CGM.getSize(SizeInChars));
  } else
    Size = CGM.getSize(SizeInChars);
  return Size;
}

void CodeGenFunction::GenerateOpenACCCapturedVars(
    const CapturedStmt &S, SmallVectorImpl<llvm::Value *> &CapturedVars) {
  const RecordDecl *RD = S.getCapturedRecordDecl();
  auto CurField = RD->field_begin();
  auto CurCap = S.captures().begin();
  for (CapturedStmt::const_capture_init_iterator I = S.capture_init_begin(),
                                                 E = S.capture_init_end();
       I != E; ++I, ++CurField, ++CurCap) {
    if (CurField->hasCapturedVLAType()) {
      auto VAT = CurField->getCapturedVLAType();
      auto *Val = VLASizeMap[VAT->getSizeExpr()];
      CapturedVars.push_back(Val);
    } else if (CurCap->capturesThis())
      CapturedVars.push_back(CXXThisValue);
    else if (CurCap->capturesVariableByCopy()) {
      llvm::Value *CV = EmitLoadOfScalar(EmitLValue(*I), CurCap->getLocation());

      // If the field is not a pointer, we need to save the actual value
      // and load it as a void pointer.
      if (!CurField->getType()->isAnyPointerType()) {
        auto &Ctx = getContext();
        auto DstAddr = CreateMemTemp(
            Ctx.getUIntPtrType(),
            Twine(CurCap->getCapturedVar()->getName()) + ".casted");
        LValue DstLV = MakeAddrLValue(DstAddr, Ctx.getUIntPtrType());

        auto *SrcAddrVal = EmitScalarConversion(
            DstAddr.getPointer(), Ctx.getPointerType(Ctx.getUIntPtrType()),
            Ctx.getPointerType(CurField->getType()), CurCap->getLocation());
        LValue SrcLV =
            MakeNaturalAlignAddrLValue(SrcAddrVal, CurField->getType());

        // Store the value using the source type pointer.
        EmitStoreThroughLValue(RValue::get(CV), SrcLV);

        // Load the value using the destination type pointer.
        CV = EmitLoadOfScalar(DstLV, CurCap->getLocation());
      }
      CapturedVars.push_back(CV);
    } else {
      assert(CurCap->capturesVariable() && "Expected capture by reference.");
      CapturedVars.push_back(EmitLValue(*I).getAddress().getPointer());
    }
  }
}

static Address castValueFromUintptr(CodeGenFunction &CGF, SourceLocation Loc,
                                    QualType DstType, StringRef Name,
                                    LValue AddrLV,
                                    bool isReferenceType = false) {
  ASTContext &Ctx = CGF.getContext();

  auto *CastedPtr = CGF.EmitScalarConversion(AddrLV.getAddress().getPointer(),
                                             Ctx.getUIntPtrType(),
                                             Ctx.getPointerType(DstType), Loc);
  auto TmpAddr =
      CGF.MakeNaturalAlignAddrLValue(CastedPtr, Ctx.getPointerType(DstType))
          .getAddress();

  // If we are dealing with references we need to return the address of the
  // reference instead of the reference of the value.
  if (isReferenceType) {
    QualType RefType = Ctx.getLValueReferenceType(DstType);
    auto *RefVal = TmpAddr.getPointer();
    TmpAddr = CGF.CreateMemTemp(RefType, Twine(Name) + ".ref");
    auto TmpLVal = CGF.MakeAddrLValue(TmpAddr, RefType);
    CGF.EmitStoreThroughLValue(RValue::get(RefVal), TmpLVal, /*isInit*/ true);
  }

  return TmpAddr;
}

static QualType getCanonicalParamType(ASTContext &C, QualType T) {
  if (T->isLValueReferenceType()) {
    return C.getLValueReferenceType(
        getCanonicalParamType(C, T.getNonReferenceType()),
        /*SpelledAsLValue=*/false);
  }
  if (T->isPointerType())
    return C.getPointerType(getCanonicalParamType(C, T->getPointeeType()));
  if (auto *A = T->getAsArrayTypeUnsafe()) {
    if (auto *VLA = dyn_cast<VariableArrayType>(A))
      return getCanonicalParamType(C, VLA->getElementType());
    else if (!A->isVariablyModifiedType())
      return C.getCanonicalType(T);
  }
  return C.getCanonicalParamType(T);
}

namespace {
  /// Contains required data for proper outlined function codegen.
  struct FunctionOptions {
    /// Captured statement for which the function is generated.
    const CapturedStmt *S = nullptr;
    /// true if cast to/from  UIntPtr is required for variables captured by
    /// value.
    const bool UIntPtrCastRequired = true;
    /// true if only casted arguments must be registered as local args or VLA
    /// sizes.
    const bool RegisterCastedArgsOnly = false;
    /// Name of the generated function.
    const StringRef FunctionName;
    explicit FunctionOptions(const CapturedStmt *S, bool UIntPtrCastRequired,
                             bool RegisterCastedArgsOnly,
                             StringRef FunctionName)
        : S(S), UIntPtrCastRequired(UIntPtrCastRequired),
          RegisterCastedArgsOnly(UIntPtrCastRequired && RegisterCastedArgsOnly),
          FunctionName(FunctionName) {}
  };
}

static llvm::Function *emitOutlinedFunctionPrologue(
    CodeGenFunction &CGF, FunctionArgList &Args,
    llvm::MapVector<const Decl *, std::pair<const VarDecl *, Address>>
        &LocalAddrs,
    llvm::DenseMap<const Decl *, std::pair<const Expr *, llvm::Value *>>
        &VLASizes,
    llvm::Value *&CXXThisValue, const FunctionOptions &FO) {
  const CapturedDecl *CD = FO.S->getCapturedDecl();
  const RecordDecl *RD = FO.S->getCapturedRecordDecl();
  assert(CD->hasBody() && "missing CapturedDecl body");

  CXXThisValue = nullptr;
  // Build the argument list.
  CodeGenModule &CGM = CGF.CGM;
  ASTContext &Ctx = CGM.getContext();
  FunctionArgList TargetArgs;
  Args.append(CD->param_begin(),
              std::next(CD->param_begin(), CD->getContextParamPosition()));
  TargetArgs.append(
      CD->param_begin(),
      std::next(CD->param_begin(), CD->getContextParamPosition()));
  auto I = FO.S->captures().begin();
  FunctionDecl *DebugFunctionDecl = nullptr;
  if (!FO.UIntPtrCastRequired) {
    FunctionProtoType::ExtProtoInfo EPI;
    DebugFunctionDecl = FunctionDecl::Create(
        Ctx, Ctx.getTranslationUnitDecl(), FO.S->getLocStart(),
        SourceLocation(), DeclarationName(), Ctx.VoidTy,
        Ctx.getTrivialTypeSourceInfo(
            Ctx.getFunctionType(Ctx.VoidTy, llvm::None, EPI)),
        SC_Static, /*isInlineSpecified=*/false, /*hasWrittenPrototype=*/false);
  }
  for (auto *FD : RD->fields()) {
    QualType ArgType = FD->getType();
    IdentifierInfo *II = nullptr;
    VarDecl *CapVar = nullptr;

    // If this is a capture by copy and the type is not a pointer, the outlined
    // function argument type should be uintptr and the value properly casted to
    // uintptr. This is necessary given that the runtime library is only able to
    // deal with pointers. We can pass in the same way the VLA type sizes to the
    // outlined function.
    if ((I->capturesVariableByCopy() && !ArgType->isAnyPointerType()) ||
        I->capturesVariableArrayType()) {
      if (FO.UIntPtrCastRequired)
        ArgType = Ctx.getUIntPtrType();
    }

    if (I->capturesVariable() || I->capturesVariableByCopy()) {
      CapVar = I->getCapturedVar();
      II = CapVar->getIdentifier();
    } else if (I->capturesThis())
      II = &Ctx.Idents.get("this");
    else {
      assert(I->capturesVariableArrayType());
      II = &Ctx.Idents.get("vla");
    }
    if (ArgType->isVariablyModifiedType())
      ArgType = getCanonicalParamType(Ctx, ArgType);
    VarDecl *Arg;
    if (DebugFunctionDecl && (CapVar || I->capturesThis())) {
      Arg = ParmVarDecl::Create(
          Ctx, DebugFunctionDecl,
          CapVar ? CapVar->getLocStart() : FD->getLocStart(),
          CapVar ? CapVar->getLocation() : FD->getLocation(), II, ArgType,
          /*TInfo=*/nullptr, SC_None, /*DefArg=*/nullptr);
    } else {
      Arg = ImplicitParamDecl::Create(Ctx, /*DC=*/nullptr, FD->getLocation(),
                                      II, ArgType, ImplicitParamDecl::Other);
    }
    Args.emplace_back(Arg);
    // Do not cast arguments if we emit function with non-original types.
    TargetArgs.emplace_back(
        FO.UIntPtrCastRequired
            ? Arg
            : CGM.getOpenACCRuntime().translateParameter(FD, Arg));
    ++I;
  }
  Args.append(
      std::next(CD->param_begin(), CD->getContextParamPosition() + 1),
      CD->param_end());
  TargetArgs.append(
      std::next(CD->param_begin(), CD->getContextParamPosition() + 1),
      CD->param_end());

  // Create the function declaration.
  const CGFunctionInfo &FuncInfo =
      CGM.getTypes().arrangeBuiltinFunctionDeclaration(Ctx.VoidTy, TargetArgs);
  llvm::FunctionType *FuncLLVMTy = CGM.getTypes().GetFunctionType(FuncInfo);

  llvm::Function *F =
      llvm::Function::Create(FuncLLVMTy, llvm::GlobalValue::InternalLinkage,
                             FO.FunctionName, &CGM.getModule());
  CGM.SetInternalFunctionAttributes(CD, F, FuncInfo);
  if (CD->isNothrow())
    F->setDoesNotThrow();

  // Generate the function.
  CGF.StartFunction(CD, Ctx.VoidTy, F, FuncInfo, TargetArgs,
                    FO.S->getLocStart(), CD->getBody()->getLocStart());
  unsigned Cnt = CD->getContextParamPosition();
  I = FO.S->captures().begin();
  for (auto *FD : RD->fields()) {
    // Do not map arguments if we emit function with non-original types.
    Address LocalAddr(Address::invalid());
    if (!FO.UIntPtrCastRequired && Args[Cnt] != TargetArgs[Cnt]) {
      LocalAddr = CGM.getOpenACCRuntime().getParameterAddress(CGF, Args[Cnt],
                                                             TargetArgs[Cnt]);
    } else {
      LocalAddr = CGF.GetAddrOfLocalVar(Args[Cnt]);
    }
    // If we are capturing a pointer by copy we don't need to do anything, just
    // use the value that we get from the arguments.
    if (I->capturesVariableByCopy() && FD->getType()->isAnyPointerType()) {
      const VarDecl *CurVD = I->getCapturedVar();
      // If the variable is a reference we need to materialize it here.
      if (CurVD->getType()->isReferenceType()) {
        Address RefAddr = CGF.CreateMemTemp(
            CurVD->getType(), CGM.getPointerAlign(), ".materialized_ref");
        CGF.EmitStoreOfScalar(LocalAddr.getPointer(), RefAddr,
                              /*Volatile=*/false, CurVD->getType());
        LocalAddr = RefAddr;
      }
      if (!FO.RegisterCastedArgsOnly)
        LocalAddrs.insert({Args[Cnt], {CurVD, LocalAddr}});
      ++Cnt;
      ++I;
      continue;
    }

    LValue ArgLVal = CGF.MakeAddrLValue(LocalAddr, Args[Cnt]->getType(),
                                        AlignmentSource::Decl);
    if (FD->hasCapturedVLAType()) {
      if (FO.UIntPtrCastRequired) {
        ArgLVal = CGF.MakeAddrLValue(
            castValueFromUintptr(CGF, I->getLocation(), FD->getType(),
                                 Args[Cnt]->getName(), ArgLVal),
            FD->getType(), AlignmentSource::Decl);
      }
      auto *ExprArg = CGF.EmitLoadOfScalar(ArgLVal, I->getLocation());
      auto VAT = FD->getCapturedVLAType();
      VLASizes.insert({Args[Cnt], {VAT->getSizeExpr(), ExprArg}});
    } else if (I->capturesVariable()) {
      auto *Var = I->getCapturedVar();
      QualType VarTy = Var->getType();
      Address ArgAddr = ArgLVal.getAddress();
      if (!VarTy->isReferenceType()) {
        if (ArgLVal.getType()->isLValueReferenceType()) {
          ArgAddr = CGF.EmitLoadOfReference(ArgLVal);
        } else if (!VarTy->isVariablyModifiedType() || !VarTy->isPointerType()) {
          assert(ArgLVal.getType()->isPointerType());
          ArgAddr = CGF.EmitLoadOfPointer(
              ArgAddr, ArgLVal.getType()->castAs<PointerType>());
        }
      }
      if (!FO.RegisterCastedArgsOnly) {
        LocalAddrs.insert(
            {Args[Cnt],
             {Var, Address(ArgAddr.getPointer(), Ctx.getDeclAlign(Var))}});
      }
    } else if (I->capturesVariableByCopy()) {
      assert(!FD->getType()->isAnyPointerType() &&
             "Not expecting a captured pointer.");
      auto *Var = I->getCapturedVar();
      QualType VarTy = Var->getType();
      LocalAddrs.insert(
          {Args[Cnt],
           {Var, FO.UIntPtrCastRequired
                     ? castValueFromUintptr(CGF, I->getLocation(),
                                            FD->getType(), Args[Cnt]->getName(),
                                            ArgLVal, VarTy->isReferenceType())
                     : ArgLVal.getAddress()}});
    } else {
      // If 'this' is captured, load it into CXXThisValue.
      assert(I->capturesThis());
      CXXThisValue = CGF.EmitLoadOfScalar(ArgLVal, I->getLocation());
      LocalAddrs.insert({Args[Cnt], {nullptr, ArgLVal.getAddress()}});
    }
    ++Cnt;
    ++I;
  }

  return F;
}

llvm::Function *
CodeGenFunction::GenerateOpenACCCapturedStmtFunction(const CapturedStmt &S) {
  assert(
      CapturedStmtInfo &&
      "CapturedStmtInfo should be set when generating the captured function");
  const CapturedDecl *CD = S.getCapturedDecl();
  // Build the argument list.
  bool NeedWrapperFunction =
      getDebugInfo() &&
      CGM.getCodeGenOpts().getDebugInfo() >= codegenoptions::LimitedDebugInfo;
  FunctionArgList Args;
  llvm::MapVector<const Decl *, std::pair<const VarDecl *, Address>> LocalAddrs;
  llvm::DenseMap<const Decl *, std::pair<const Expr *, llvm::Value *>> VLASizes;
  SmallString<256> Buffer;
  llvm::raw_svector_ostream Out(Buffer);
  Out << CapturedStmtInfo->getHelperName();
  if (NeedWrapperFunction)
    Out << "_debug__";
  FunctionOptions FO(&S, !NeedWrapperFunction, /*RegisterCastedArgsOnly=*/false,
                     Out.str());
  llvm::Function *F = emitOutlinedFunctionPrologue(*this, Args, LocalAddrs,
                                                   VLASizes, CXXThisValue, FO);
  for (const auto &LocalAddrPair : LocalAddrs) {
    if (LocalAddrPair.second.first) {
      setAddrOfLocalVar(LocalAddrPair.second.first,
                        LocalAddrPair.second.second);
    }
  }
  for (const auto &VLASizePair : VLASizes)
    VLASizeMap[VLASizePair.second.first] = VLASizePair.second.second;
  PGO.assignRegionCounters(GlobalDecl(CD), F);
  CapturedStmtInfo->EmitBody(*this, CD->getBody());
  FinishFunction(CD->getBodyRBrace());
  if (!NeedWrapperFunction)
    return F;

  FunctionOptions WrapperFO(&S, /*UIntPtrCastRequired=*/true,
                            /*RegisterCastedArgsOnly=*/true,
                            CapturedStmtInfo->getHelperName());
  CodeGenFunction WrapperCGF(CGM, /*suppressNewContext=*/true);
  Args.clear();
  LocalAddrs.clear();
  VLASizes.clear();
  llvm::Function *WrapperF =
      emitOutlinedFunctionPrologue(WrapperCGF, Args, LocalAddrs, VLASizes,
                                   WrapperCGF.CXXThisValue, WrapperFO);
  llvm::SmallVector<llvm::Value *, 4> CallArgs;
  for (const auto *Arg : Args) {
    llvm::Value *CallArg;
    auto I = LocalAddrs.find(Arg);
    if (I != LocalAddrs.end()) {
      LValue LV = WrapperCGF.MakeAddrLValue(
          I->second.second,
          I->second.first ? I->second.first->getType() : Arg->getType(),
          AlignmentSource::Decl);
      CallArg = WrapperCGF.EmitLoadOfScalar(LV, S.getLocStart());
    } else {
      auto EI = VLASizes.find(Arg);
      if (EI != VLASizes.end())
        CallArg = EI->second.second;
      else {
        LValue LV = WrapperCGF.MakeAddrLValue(WrapperCGF.GetAddrOfLocalVar(Arg),
                                              Arg->getType(),
                                              AlignmentSource::Decl);
        CallArg = WrapperCGF.EmitLoadOfScalar(LV, S.getLocStart());
      }
    }
    CallArgs.emplace_back(WrapperCGF.EmitFromMemory(CallArg, Arg->getType()));
  }
  CGM.getOpenACCRuntime().emitOutlinedFunctionCall(WrapperCGF, S.getLocStart(),
                                                  F, CallArgs);
  WrapperCGF.FinishFunction();
  return WrapperF;
}

//===----------------------------------------------------------------------===//
//                              OpenACC Directive Emission
//===----------------------------------------------------------------------===//
void CodeGenFunction::EmitACCAggregateAssign(
    Address DestAddr, Address SrcAddr, QualType OriginalType,
    const llvm::function_ref<void(Address, Address)> &CopyGen) {
  // Perform element-by-element initialization.
  QualType ElementTy;

  // Drill down to the base element type on both arrays.
  auto ArrayTy = OriginalType->getAsArrayTypeUnsafe();
  auto NumElements = emitArrayLength(ArrayTy, ElementTy, DestAddr);
  SrcAddr = Builder.CreateElementBitCast(SrcAddr, DestAddr.getElementType());

  auto SrcBegin = SrcAddr.getPointer();
  auto DestBegin = DestAddr.getPointer();
  // Cast from pointer to array type to pointer to single element.
  auto DestEnd = Builder.CreateGEP(DestBegin, NumElements);
  // The basic structure here is a while-do loop.
  auto BodyBB = createBasicBlock("acc.arraycpy.body");
  auto DoneBB = createBasicBlock("acc.arraycpy.done");
  auto IsEmpty =
      Builder.CreateICmpEQ(DestBegin, DestEnd, "acc.arraycpy.isempty");
  Builder.CreateCondBr(IsEmpty, DoneBB, BodyBB);

  // Enter the loop body, making that address the current address.
  auto EntryBB = Builder.GetInsertBlock();
  EmitBlock(BodyBB);

  CharUnits ElementSize = getContext().getTypeSizeInChars(ElementTy);

  llvm::PHINode *SrcElementPHI =
    Builder.CreatePHI(SrcBegin->getType(), 2, "acc.arraycpy.srcElementPast");
  SrcElementPHI->addIncoming(SrcBegin, EntryBB);
  Address SrcElementCurrent =
      Address(SrcElementPHI,
              SrcAddr.getAlignment().alignmentOfArrayElement(ElementSize));

  llvm::PHINode *DestElementPHI =
    Builder.CreatePHI(DestBegin->getType(), 2, "acc.arraycpy.destElementPast");
  DestElementPHI->addIncoming(DestBegin, EntryBB);
  Address DestElementCurrent =
    Address(DestElementPHI,
            DestAddr.getAlignment().alignmentOfArrayElement(ElementSize));

  // Emit copy.
  CopyGen(DestElementCurrent, SrcElementCurrent);

  // Shift the address forward by one element.
  auto DestElementNext = Builder.CreateConstGEP1_32(
      DestElementPHI, /*Idx0=*/1, "acc.arraycpy.dest.element");
  auto SrcElementNext = Builder.CreateConstGEP1_32(
      SrcElementPHI, /*Idx0=*/1, "acc.arraycpy.src.element");
  // Check whether we've reached the end.
  auto Done =
      Builder.CreateICmpEQ(DestElementNext, DestEnd, "acc.arraycpy.done");
  Builder.CreateCondBr(Done, DoneBB, BodyBB);
  DestElementPHI->addIncoming(DestElementNext, Builder.GetInsertBlock());
  SrcElementPHI->addIncoming(SrcElementNext, Builder.GetInsertBlock());

  // Done.
  EmitBlock(DoneBB, /*IsFinished=*/true);
}

void CodeGenFunction::EmitACCCopy(QualType OriginalType, Address DestAddr,
                                  Address SrcAddr, const VarDecl *DestVD,
                                  const VarDecl *SrcVD, const Expr *Copy) {
  if (OriginalType->isArrayType()) {
    auto *BO = dyn_cast<BinaryOperator>(Copy);
    if (BO && BO->getOpcode() == BO_Assign) {
      // Perform simple memcpy for simple copying.
      LValue Dest = MakeAddrLValue(DestAddr, OriginalType);
      LValue Src = MakeAddrLValue(SrcAddr, OriginalType);
      EmitAggregateAssign(Dest, Src, OriginalType);
    } else {
      // For arrays with complex element types perform element by element
      // copying.
      EmitACCAggregateAssign(
          DestAddr, SrcAddr, OriginalType,
          [this, Copy, SrcVD, DestVD](Address DestElement, Address SrcElement) {
            // Working with the single array element, so have to remap
            // destination and source variables to corresponding array
            // elements.
            CodeGenFunction::ACCPrivateScope Remap(*this);
            Remap.addPrivate(DestVD, [DestElement]() -> Address {
              return DestElement;
            });
            Remap.addPrivate(
                SrcVD, [SrcElement]() -> Address { return SrcElement; });
            (void)Remap.Privatize();
            EmitIgnoredExpr(Copy);
          });
    }
  } else {
    // Remap pseudo source variable to private copy.
    CodeGenFunction::ACCPrivateScope Remap(*this);
    Remap.addPrivate(SrcVD, [SrcAddr]() -> Address { return SrcAddr; });
    Remap.addPrivate(DestVD, [DestAddr]() -> Address { return DestAddr; });
    (void)Remap.Privatize();
    // Emit copying of the whole variable.
    EmitIgnoredExpr(Copy);
  }
}

bool CodeGenFunction::EmitACCFirstprivateClause(const ACCExecutableDirective &D,
                                                ACCPrivateScope &PrivateScope) {
  if (!HaveInsertPoint())
    return false;
  bool FirstprivateIsLastprivate = false;
  llvm::DenseSet<const VarDecl *> Lastprivates;
  for (const auto *C : D.getClausesOfKind<ACCLastprivateClause>()) {
    for (const auto *D : C->varlists())
      Lastprivates.insert(
          cast<VarDecl>(cast<DeclRefExpr>(D)->getDecl())->getCanonicalDecl());
  }
  llvm::DenseSet<const VarDecl *> EmittedAsFirstprivate;
  llvm::SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
  getOpenACCCaptureRegions(CaptureRegions, D.getDirectiveKind());
  // Force emission of the firstprivate copy if the directive does not emit
  // outlined function, like acc for, acc vector, acc distribute etc.
  bool MustEmitFirstprivateCopy =
      CaptureRegions.size() == 1 && CaptureRegions.back() == ACCD_unknown;
  for (const auto *C : D.getClausesOfKind<ACCFirstprivateClause>()) {
    auto IRef = C->varlist_begin();
    auto InitsRef = C->inits().begin();
    for (auto IInit : C->private_copies()) {
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      bool ThisFirstprivateIsLastprivate =
          Lastprivates.count(OrigVD->getCanonicalDecl()) > 0;
      auto *FD = CapturedStmtInfo->lookup(OrigVD);
      if (!MustEmitFirstprivateCopy && !ThisFirstprivateIsLastprivate && FD &&
          !FD->getType()->isReferenceType()) {
        EmittedAsFirstprivate.insert(OrigVD->getCanonicalDecl());
        ++IRef;
        ++InitsRef;
        continue;
      }
      FirstprivateIsLastprivate =
          FirstprivateIsLastprivate || ThisFirstprivateIsLastprivate;
      if (EmittedAsFirstprivate.insert(OrigVD->getCanonicalDecl()).second) {
        auto *VD = cast<VarDecl>(cast<DeclRefExpr>(IInit)->getDecl());
        auto *VDInit = cast<VarDecl>(cast<DeclRefExpr>(*InitsRef)->getDecl());
        bool IsRegistered;
        DeclRefExpr DRE(const_cast<VarDecl *>(OrigVD),
                        /*RefersToEnclosingVariableOrCapture=*/FD != nullptr,
                        (*IRef)->getType(), VK_LValue, (*IRef)->getExprLoc());
        LValue OriginalLVal = EmitLValue(&DRE);
        Address OriginalAddr = OriginalLVal.getAddress();
        QualType Type = VD->getType();
        if (Type->isArrayType()) {
          // Emit VarDecl with copy init for arrays.
          // Get the address of the original variable captured in current
          // captured region.
          IsRegistered = PrivateScope.addPrivate(OrigVD, [&]() -> Address {
            auto Emission = EmitAutoVarAlloca(*VD);
            auto *Init = VD->getInit();
            if (!isa<CXXConstructExpr>(Init) || isTrivialInitializer(Init)) {
              // Perform simple memcpy.
              LValue Dest = MakeAddrLValue(Emission.getAllocatedAddress(),
                                           Type);
              EmitAggregateAssign(Dest, OriginalLVal, Type);
            } else {
              EmitACCAggregateAssign(
                  Emission.getAllocatedAddress(), OriginalAddr, Type,
                  [this, VDInit, Init](Address DestElement,
                                       Address SrcElement) {
                    // Clean up any temporaries needed by the initialization.
                    RunCleanupsScope InitScope(*this);
                    // Emit initialization for single element.
                    setAddrOfLocalVar(VDInit, SrcElement);
                    EmitAnyExprToMem(Init, DestElement,
                                     Init->getType().getQualifiers(),
                                     /*IsInitializer*/ false);
                    LocalDeclMap.erase(VDInit);
                  });
            }
            EmitAutoVarCleanups(Emission);
            return Emission.getAllocatedAddress();
          });
        } else {
          IsRegistered = PrivateScope.addPrivate(OrigVD, [&]() -> Address {
            // Emit private VarDecl with copy init.
            // Remap temp VDInit variable to the address of the original
            // variable
            // (for proper handling of captured global variables).
            setAddrOfLocalVar(VDInit, OriginalAddr);
            EmitDecl(*VD);
            LocalDeclMap.erase(VDInit);
            return GetAddrOfLocalVar(VD);
          });
        }
        assert(IsRegistered &&
               "firstprivate var already registered as private");
        // Silence the warning about unused variable.
        (void)IsRegistered;
      }
      ++IRef;
      ++InitsRef;
    }
  }
  return FirstprivateIsLastprivate && !EmittedAsFirstprivate.empty();
}

void CodeGenFunction::EmitACCPrivateClause(
    const ACCExecutableDirective &D,
    CodeGenFunction::ACCPrivateScope &PrivateScope) {
  if (!HaveInsertPoint())
    return;
  llvm::DenseSet<const VarDecl *> EmittedAsPrivate;
  for (const auto *C : D.getClausesOfKind<ACCPrivateClause>()) {
    auto IRef = C->varlist_begin();
    for (auto IInit : C->private_copies()) {
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      if (EmittedAsPrivate.insert(OrigVD->getCanonicalDecl()).second) {
        auto VD = cast<VarDecl>(cast<DeclRefExpr>(IInit)->getDecl());
        bool IsRegistered =
            PrivateScope.addPrivate(OrigVD, [&]() -> Address {
              // Emit private VarDecl with copy init.
              EmitDecl(*VD);
              return GetAddrOfLocalVar(VD);
            });
        assert(IsRegistered && "private var already registered as private");
        // Silence the warning about unused variable.
        (void)IsRegistered;
      }
      ++IRef;
    }
  }
}

/* bool CodeGenFunction::EmitACCCopyinClause(const ACCExecutableDirective &D) { */
/*   if (!HaveInsertPoint()) */
/*     return false; */
/*   // threadprivate_var1 = master_threadprivate_var1; */
/*   // operator=(threadprivate_var2, master_threadprivate_var2); */
/*   // ... */
/*   // __kmpc_barrier(&loc, global_tid); */
/*   llvm::DenseSet<const VarDecl *> CopiedVars; */
/*   llvm::BasicBlock *CopyBegin = nullptr, *CopyEnd = nullptr; */
/*   for (const auto *C : D.getClausesOfKind<ACCCopyinClause>()) { */
/*     auto IRef = C->varlist_begin(); */
/*     auto ISrcRef = C->source_exprs().begin(); */
/*     auto IDestRef = C->destination_exprs().begin(); */
/*     for (auto *AssignOp : C->assignment_ops()) { */
/*       auto *VD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl()); */
/*       QualType Type = VD->getType(); */
/*       if (CopiedVars.insert(VD->getCanonicalDecl()).second) { */
/*         // Get the address of the master variable. If we are emitting code with */
/*         // TLS support, the address is passed from the master as field in the */
/*         // captured declaration. */
/*         Address MasterAddr = Address::invalid(); */
/*         if (getLangOpts().OpenACCUseTLS && */
/*             getContext().getTargetInfo().isTLSSupported()) { */
/*           assert(CapturedStmtInfo->lookup(VD) && */
/*                  "Copyin threadprivates should have been captured!"); */
/*           DeclRefExpr DRE(const_cast<VarDecl *>(VD), true, (*IRef)->getType(), */
/*                           VK_LValue, (*IRef)->getExprLoc()); */
/*           MasterAddr = EmitLValue(&DRE).getAddress(); */
/*           LocalDeclMap.erase(VD); */
/*         } else { */
/*           MasterAddr = */
/*             Address(VD->isStaticLocal() ? CGM.getStaticLocalDeclAddress(VD) */
/*                                         : CGM.GetAddrOfGlobal(VD), */
/*                     getContext().getDeclAlign(VD)); */
/*         } */
/*         // Get the address of the threadprivate variable. */
/*         Address PrivateAddr = EmitLValue(*IRef).getAddress(); */
/*         if (CopiedVars.size() == 1) { */
/*           // At first check if current thread is a master thread. If it is, no */
/*           // need to copy data. */
/*           CopyBegin = createBasicBlock("copyin.not.master"); */
/*           CopyEnd = createBasicBlock("copyin.not.master.end"); */
/*           Builder.CreateCondBr( */
/*               Builder.CreateICmpNE( */
/*                   Builder.CreatePtrToInt(MasterAddr.getPointer(), CGM.IntPtrTy), */
/*                   Builder.CreatePtrToInt(PrivateAddr.getPointer(), CGM.IntPtrTy)), */
/*               CopyBegin, CopyEnd); */
/*           EmitBlock(CopyBegin); */
/*         } */
/*         auto *SrcVD = cast<VarDecl>(cast<DeclRefExpr>(*ISrcRef)->getDecl()); */
/*         auto *DestVD = cast<VarDecl>(cast<DeclRefExpr>(*IDestRef)->getDecl()); */
/*         EmitACCCopy(Type, PrivateAddr, MasterAddr, DestVD, SrcVD, AssignOp); */
/*       } */
/*       ++IRef; */
/*       ++ISrcRef; */
/*       ++IDestRef; */
/*     } */
/*   } */
/*   if (CopyEnd) { */
/*     // Exit out of copying procedure for non-master thread. */
/*     EmitBlock(CopyEnd, IsFinished=true);  */
/*     return true; */
/*   } */
/*   return false; */
/* } */

bool CodeGenFunction::EmitACCLastprivateClauseInit(
    const ACCExecutableDirective &D, ACCPrivateScope &PrivateScope) {
  if (!HaveInsertPoint())
    return false;
  bool HasAtLeastOneLastprivate = false;
  llvm::DenseSet<const VarDecl *> VectorLCVs;
  if (isOpenACCVectorDirective(D.getDirectiveKind())) {
    auto *LoopDirective = cast<ACCLoopLikeDirective>(&D);
    for (auto *C : LoopDirective->counters()) {
      VectorLCVs.insert(
          cast<VarDecl>(cast<DeclRefExpr>(C)->getDecl())->getCanonicalDecl());
    }
  }
  llvm::DenseSet<const VarDecl *> AlreadyEmittedVars;
  for (const auto *C : D.getClausesOfKind<ACCLastprivateClause>()) {
    HasAtLeastOneLastprivate = true;
    if (isOpenACCTaskLoopDirective(D.getDirectiveKind()) &&
        !getLangOpts().OpenACCVector)
      break;
    auto IRef = C->varlist_begin();
    auto IDestRef = C->destination_exprs().begin();
    for (auto *IInit : C->private_copies()) {
      // Keep the address of the original variable for future update at the end
      // of the loop.
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      // Taskloops do not require additional initialization, it is done in
      // runtime support library.
      if (AlreadyEmittedVars.insert(OrigVD->getCanonicalDecl()).second) {
        auto *DestVD = cast<VarDecl>(cast<DeclRefExpr>(*IDestRef)->getDecl());
        PrivateScope.addPrivate(DestVD, [this, OrigVD, IRef]() -> Address {
          DeclRefExpr DRE(
              const_cast<VarDecl *>(OrigVD),
              /*RefersToEnclosingVariableOrCapture=*/CapturedStmtInfo->lookup(
                  OrigVD) != nullptr,
              (*IRef)->getType(), VK_LValue, (*IRef)->getExprLoc());
          return EmitLValue(&DRE).getAddress();
        });
        // Check if the variable is also a firstprivate: in this case IInit is
        // not generated. Initialization of this variable will happen in codegen
        // for 'firstprivate' clause.
        if (IInit && !VectorLCVs.count(OrigVD->getCanonicalDecl())) {
          auto *VD = cast<VarDecl>(cast<DeclRefExpr>(IInit)->getDecl());
          bool IsRegistered = PrivateScope.addPrivate(OrigVD, [&]() -> Address {
            // Emit private VarDecl with copy init.
            EmitDecl(*VD);
            return GetAddrOfLocalVar(VD);
          });
          assert(IsRegistered &&
                 "lastprivate var already registered as private");
          (void)IsRegistered;
        }
      }
      ++IRef;
      ++IDestRef;
    }
  }
  return HasAtLeastOneLastprivate;
}

void CodeGenFunction::EmitACCLastprivateClauseFinal(
    const ACCExecutableDirective &D, bool NoFinals,
    llvm::Value *IsLastIterCond) {
  if (!HaveInsertPoint())
    return;
  // Emit following code:
  // if (<IsLastIterCond>) {
  //   orig_var1 = private_orig_var1;
  //   ...
  //   orig_varn = private_orig_varn;
  // }
  llvm::BasicBlock *ThenBB = nullptr;
  llvm::BasicBlock *DoneBB = nullptr;
  if (IsLastIterCond) {
    ThenBB = createBasicBlock(".acc.lastprivate.then");
    DoneBB = createBasicBlock(".acc.lastprivate.done");
    Builder.CreateCondBr(IsLastIterCond, ThenBB, DoneBB);
    EmitBlock(ThenBB);
  }
  llvm::DenseSet<const VarDecl *> AlreadyEmittedVars;
  llvm::DenseMap<const VarDecl *, const Expr *> LoopCountersAndUpdates;
  if (auto *LoopDirective = dyn_cast<ACCLoopLikeDirective>(&D)) {
    auto IC = LoopDirective->counters().begin();
    for (auto F : LoopDirective->finals()) {
      auto *D =
          cast<VarDecl>(cast<DeclRefExpr>(*IC)->getDecl())->getCanonicalDecl();
      if (NoFinals)
        AlreadyEmittedVars.insert(D);
      else
        LoopCountersAndUpdates[D] = F;
      ++IC;
    }
  }
  for (const auto *C : D.getClausesOfKind<ACCLastprivateClause>()) {
    auto IRef = C->varlist_begin();
    auto ISrcRef = C->source_exprs().begin();
    auto IDestRef = C->destination_exprs().begin();
    for (auto *AssignOp : C->assignment_ops()) {
      auto *PrivateVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      QualType Type = PrivateVD->getType();
      auto *CanonicalVD = PrivateVD->getCanonicalDecl();
      if (AlreadyEmittedVars.insert(CanonicalVD).second) {
        // If lastprivate variable is a loop control variable for loop-based
        // directive, update its value before copyin back to original
        // variable.
        if (auto *FinalExpr = LoopCountersAndUpdates.lookup(CanonicalVD))
          EmitIgnoredExpr(FinalExpr);
        auto *SrcVD = cast<VarDecl>(cast<DeclRefExpr>(*ISrcRef)->getDecl());
        auto *DestVD = cast<VarDecl>(cast<DeclRefExpr>(*IDestRef)->getDecl());
        // Get the address of the original variable.
        Address OriginalAddr = GetAddrOfLocalVar(DestVD);
        // Get the address of the private variable.
        Address PrivateAddr = GetAddrOfLocalVar(PrivateVD);
        if (auto RefTy = PrivateVD->getType()->getAs<ReferenceType>())
          PrivateAddr =
              Address(Builder.CreateLoad(PrivateAddr),
                      getNaturalTypeAlignment(RefTy->getPointeeType()));
        EmitACCCopy(Type, OriginalAddr, PrivateAddr, DestVD, SrcVD, AssignOp);
      }
      ++IRef;
      ++ISrcRef;
      ++IDestRef;
    }
    if (auto *PostUpdate = C->getPostUpdateExpr())
      EmitIgnoredExpr(PostUpdate);
  }
  if (IsLastIterCond)
    EmitBlock(DoneBB, /*IsFinished=*/true);
}

void CodeGenFunction::EmitACCReductionClauseInit(
    const ACCExecutableDirective &D,
    CodeGenFunction::ACCPrivateScope &PrivateScope) {
  if (!HaveInsertPoint())
    return;
  SmallVector<const Expr *, 4> Shareds;
  SmallVector<const Expr *, 4> Privates;
  SmallVector<const Expr *, 4> ReductionOps;
  SmallVector<const Expr *, 4> LHSs;
  SmallVector<const Expr *, 4> RHSs;
  for (const auto *C : D.getClausesOfKind<ACCReductionClause>()) {
    auto IPriv = C->privates().begin();
    auto IRed = C->reduction_ops().begin();
    auto ILHS = C->lhs_exprs().begin();
    auto IRHS = C->rhs_exprs().begin();
    for (const auto *Ref : C->varlists()) {
      Shareds.emplace_back(Ref);
      Privates.emplace_back(*IPriv);
      ReductionOps.emplace_back(*IRed);
      LHSs.emplace_back(*ILHS);
      RHSs.emplace_back(*IRHS);
      std::advance(IPriv, 1);
      std::advance(IRed, 1);
      std::advance(ILHS, 1);
      std::advance(IRHS, 1);
    }
  }
  ACCReductionCodeGen RedCG(Shareds, Privates, ReductionOps);
  unsigned Count = 0;
  auto ILHS = LHSs.begin();
  auto IRHS = RHSs.begin();
  auto IPriv = Privates.begin();
  for (const auto *IRef : Shareds) {
    auto *PrivateVD = cast<VarDecl>(cast<DeclRefExpr>(*IPriv)->getDecl());
    // Emit private VarDecl with reduction init.
    RedCG.emitSharedLValue(*this, Count);
    RedCG.emitAggregateType(*this, Count);
    auto Emission = EmitAutoVarAlloca(*PrivateVD);
    RedCG.emitInitialization(*this, Count, Emission.getAllocatedAddress(),
                             RedCG.getSharedLValue(Count),
                             [&Emission](CodeGenFunction &CGF) {
                               CGF.EmitAutoVarInit(Emission);
                               return true;
                             });
    EmitAutoVarCleanups(Emission);
    Address BaseAddr = RedCG.adjustPrivateAddress(
        *this, Count, Emission.getAllocatedAddress());
    bool IsRegistered = PrivateScope.addPrivate(
        RedCG.getBaseDecl(Count), [BaseAddr]() -> Address { return BaseAddr; });
    assert(IsRegistered && "private var already registered as private");
    // Silence the warning about unused variable.
    (void)IsRegistered;

    auto *LHSVD = cast<VarDecl>(cast<DeclRefExpr>(*ILHS)->getDecl());
    auto *RHSVD = cast<VarDecl>(cast<DeclRefExpr>(*IRHS)->getDecl());
    QualType Type = PrivateVD->getType();
    bool isaOMPACCArraySectionExpr = isa<OMPACCArraySectionExpr>(IRef);
    if (isaOMPACCArraySectionExpr && Type->isVariablyModifiedType()) {
      // Store the address of the original variable associated with the LHS
      // implicit variable.
      PrivateScope.addPrivate(LHSVD, [&RedCG, Count]() -> Address {
        return RedCG.getSharedLValue(Count).getAddress();
      });
      PrivateScope.addPrivate(RHSVD, [this, PrivateVD]() -> Address {
        return GetAddrOfLocalVar(PrivateVD);
      });
    } else if ((isaOMPACCArraySectionExpr && Type->isScalarType()) ||
               isa<ArraySubscriptExpr>(IRef)) {
      // Store the address of the original variable associated with the LHS
      // implicit variable.
      PrivateScope.addPrivate(LHSVD, [&RedCG, Count]() -> Address {
        return RedCG.getSharedLValue(Count).getAddress();
      });
      PrivateScope.addPrivate(RHSVD, [this, PrivateVD, RHSVD]() -> Address {
        return Builder.CreateElementBitCast(GetAddrOfLocalVar(PrivateVD),
                                            ConvertTypeForMem(RHSVD->getType()),
                                            "rhs.begin");
      });
    } else {
      QualType Type = PrivateVD->getType();
      bool IsArray = getContext().getAsArrayType(Type) != nullptr;
      Address OriginalAddr = RedCG.getSharedLValue(Count).getAddress();
      // Store the address of the original variable associated with the LHS
      // implicit variable.
      if (IsArray) {
        OriginalAddr = Builder.CreateElementBitCast(
            OriginalAddr, ConvertTypeForMem(LHSVD->getType()), "lhs.begin");
      }
      PrivateScope.addPrivate(
          LHSVD, [OriginalAddr]() -> Address { return OriginalAddr; });
      PrivateScope.addPrivate(
          RHSVD, [this, PrivateVD, RHSVD, IsArray]() -> Address {
            return IsArray
                       ? Builder.CreateElementBitCast(
                             GetAddrOfLocalVar(PrivateVD),
                             ConvertTypeForMem(RHSVD->getType()), "rhs.begin")
                       : GetAddrOfLocalVar(PrivateVD);
          });
    }
    ++ILHS;
    ++IRHS;
    ++IPriv;
    ++Count;
  }
}

void CodeGenFunction::EmitACCReductionClauseFinal(
    const ACCExecutableDirective &D, const OpenACCDirectiveKind ReductionKind) {
  if (!HaveInsertPoint())
    return;
  llvm::SmallVector<const Expr *, 8> Privates;
  llvm::SmallVector<const Expr *, 8> LHSExprs;
  llvm::SmallVector<const Expr *, 8> RHSExprs;
  llvm::SmallVector<const Expr *, 8> ReductionOps;
  bool HasAtLeastOneReduction = false;
  for (const auto *C : D.getClausesOfKind<ACCReductionClause>()) {
    HasAtLeastOneReduction = true;
    Privates.append(C->privates().begin(), C->privates().end());
    LHSExprs.append(C->lhs_exprs().begin(), C->lhs_exprs().end());
    RHSExprs.append(C->rhs_exprs().begin(), C->rhs_exprs().end());
    ReductionOps.append(C->reduction_ops().begin(), C->reduction_ops().end());
  }
  if (HasAtLeastOneReduction) {
    bool WithNowait = D.getSingleClause<ACCNowaitClause>() ||
                      isOpenACCParallelDirective(D.getDirectiveKind()) ||
                      ReductionKind == ACCD_vector;
    bool SimpleReduction = ReductionKind == ACCD_vector;
    // Emit nowait reduction if nowait clause is present or directive is a
    // parallel directive (it always has implicit barrier).
    CGM.getOpenACCRuntime().emitReduction(
        *this, D.getLocEnd(), Privates, LHSExprs, RHSExprs, ReductionOps,
        {WithNowait, SimpleReduction, ReductionKind});
  }
}

static void emitPostUpdateForReductionClause(
    CodeGenFunction &CGF, const ACCExecutableDirective &D,
    const llvm::function_ref<llvm::Value *(CodeGenFunction &)> &CondGen) {
  if (!CGF.HaveInsertPoint())
    return;
  llvm::BasicBlock *DoneBB = nullptr;
  for (const auto *C : D.getClausesOfKind<ACCReductionClause>()) {
    if (auto *PostUpdate = C->getPostUpdateExpr()) {
      if (!DoneBB) {
        if (auto *Cond = CondGen(CGF)) {
          // If the first post-update expression is found, emit conditional
          // block if it was requested.
          auto *ThenBB = CGF.createBasicBlock(".acc.reduction.pu");
          DoneBB = CGF.createBasicBlock(".acc.reduction.pu.done");
          CGF.Builder.CreateCondBr(Cond, ThenBB, DoneBB);
          CGF.EmitBlock(ThenBB);
        }
      }
      CGF.EmitIgnoredExpr(PostUpdate);
    }
  }
  if (DoneBB)
    CGF.EmitBlock(DoneBB, /*IsFinished=*/true);
}

namespace {
/// Codegen lambda for appending distribute lower and upper bounds to outlined
/// parallel function. This is necessary for combined constructs such as
/// 'distribute parallel for'
typedef llvm::function_ref<void(CodeGenFunction &,
                                const ACCExecutableDirective &,
                                llvm::SmallVectorImpl<llvm::Value *> &)>
    CodeGenBoundParametersTy;
} // anonymous namespace

static void emitCommonACCParallelDirective(
    CodeGenFunction &CGF, const ACCExecutableDirective &S,
    OpenACCDirectiveKind InnermostKind, const ACCRegionCodeGenTy &CodeGen,
    const CodeGenBoundParametersTy &CodeGenBoundParameters) {
  const CapturedStmt *CS = S.getCapturedStmt(ACCD_parallel);
  auto OutlinedFn = CGF.CGM.getOpenACCRuntime().emitParallelOutlinedFunction(
      S, *CS->getCapturedDecl()->param_begin(), InnermostKind, CodeGen);
  if (const auto *NumThreadsClause = S.getSingleClause<ACCNumThreadsClause>()) {
    CodeGenFunction::RunCleanupsScope NumThreadsScope(CGF);
    auto NumThreads = CGF.EmitScalarExpr(NumThreadsClause->getNumThreads(),
                                         /*IgnoreResultAssign*/ true);
    CGF.CGM.getOpenACCRuntime().emitNumThreadsClause(
        CGF, NumThreads, NumThreadsClause->getLocStart());
  }
  if (const auto *ProcBindClause = S.getSingleClause<ACCProcBindClause>()) {
    CodeGenFunction::RunCleanupsScope ProcBindScope(CGF);
    CGF.CGM.getOpenACCRuntime().emitProcBindClause(
        CGF, ProcBindClause->getProcBindKind(), ProcBindClause->getLocStart());
  }
  const Expr *IfCond = nullptr;
  for (const auto *C : S.getClausesOfKind<ACCIfClause>()) {
    if (C->getNameModifier() == ACCD_unknown ||
        C->getNameModifier() == ACCD_parallel) {
      IfCond = C->getCondition();
      break;
    }
  }

  ACCParallelScope Scope(CGF, S);
  llvm::SmallVector<llvm::Value *, 16> CapturedVars;
  // Combining 'distribute' with 'for' requires sharing each 'distribute' chunk
  // lower and upper bounds with the pragma 'for' chunking mechanism.
  // The following lambda takes care of appending the lower and upper bound
  // parameters when necessary
  CodeGenBoundParameters(CGF, S, CapturedVars);
  CGF.GenerateOpenACCCapturedVars(*CS, CapturedVars);
  CGF.CGM.getOpenACCRuntime().emitParallelCall(CGF, S.getLocStart(), OutlinedFn,
                                              CapturedVars, IfCond);
}

static void emitEmptyBoundParameters(CodeGenFunction &,
                                     const ACCExecutableDirective &,
                                     llvm::SmallVectorImpl<llvm::Value *> &) {}

void CodeGenFunction::EmitACCParallelDirective(const ACCParallelDirective &S) {
  // Emit parallel region as a standalone region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
   // bool Copyins = CGF.EmitACCCopyinClause(S);
   // (void)CGF.EmitACCFirstprivateClause(S, PrivateScope);
   // if (Copyins) {
   //   // Emit implicit barrier to synchronize threads and avoid data races on
   //   // propagation master's thread values of threadprivate variables to local
   //   // instances of that variables of all other implicit threads.
   //   CGF.CGM.getOpenACCRuntime().emitBarrierCall(
   //       CGF, S.getLocStart(), ACCD_unknown, /*EmitChecks=*/false,
   //       /*ForceSimpleCall=*/true);
   // }
    CGF.EmitACCPrivateClause(S, PrivateScope);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.EmitStmt(S.getCapturedStmt(ACCD_parallel)->getCapturedStmt());
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_parallel);
  };
  emitCommonACCParallelDirective(*this, S, ACCD_parallel, CodeGen,
                                 emitEmptyBoundParameters);
  emitPostUpdateForReductionClause(
      *this, S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
}

void CodeGenFunction::EmitACCLoopBody(const ACCLoopLikeDirective &D,
                                      JumpDest LoopExit) {
  RunCleanupsScope BodyScope(*this);
  // Update counters values on current iteration.
  for (auto I : D.updates()) {
    EmitIgnoredExpr(I);
  }
  // Update the linear variables.
  // In distribute directives only loop counters may be marked as linear, no
  // need to generate the code for them.
  if (!isOpenACCDistributeDirective(D.getDirectiveKind())) {
    for (const auto *C : D.getClausesOfKind<ACCLinearClause>()) {
      for (auto *U : C->updates())
        EmitIgnoredExpr(U);
    }
  }

  // On a continue in the body, jump to the end.
  auto Continue = getJumpDestInCurrentScope("acc.body.continue");
  BreakContinueStack.push_back(BreakContinue(LoopExit, Continue));
  // Emit loop body.
  EmitStmt(D.getBody());
  // The end (updates/cleanups).
  EmitBlock(Continue.getBlock());
  BreakContinueStack.pop_back();
}

void CodeGenFunction::EmitACCInnerLoop(
    const Stmt &S, bool RequiresCleanup, const Expr *LoopCond,
    const Expr *IncExpr,
    const llvm::function_ref<void(CodeGenFunction &)> &BodyGen,
    const llvm::function_ref<void(CodeGenFunction &)> &PostIncGen) {
  auto LoopExit = getJumpDestInCurrentScope("acc.inner.for.end");

  // Start the loop with a block that tests the condition.
  auto CondBlock = createBasicBlock("acc.inner.for.cond");
  EmitBlock(CondBlock);
  const SourceRange &R = S.getSourceRange();
  LoopStack.push(CondBlock, SourceLocToDebugLoc(R.getBegin()),
                 SourceLocToDebugLoc(R.getEnd()));

  // If there are any cleanups between here and the loop-exit scope,
  // create a block to stage a loop exit along.
  auto ExitBlock = LoopExit.getBlock();
  if (RequiresCleanup)
    ExitBlock = createBasicBlock("acc.inner.for.cond.cleanup");

  auto LoopBody = createBasicBlock("acc.inner.for.body");

  // Emit condition.
  EmitBranchOnBoolExpr(LoopCond, LoopBody, ExitBlock, getProfileCount(&S));
  if (ExitBlock != LoopExit.getBlock()) {
    EmitBlock(ExitBlock);
    EmitBranchThroughCleanup(LoopExit);
  }

  EmitBlock(LoopBody);
  incrementProfileCounter(&S);

  // Create a block for the increment.
  auto Continue = getJumpDestInCurrentScope("acc.inner.for.inc");
  BreakContinueStack.push_back(BreakContinue(LoopExit, Continue));

  BodyGen(*this);

  // Emit "IV = IV + 1" and a back-edge to the condition block.
  EmitBlock(Continue.getBlock());
  EmitIgnoredExpr(IncExpr);
  PostIncGen(*this);
  BreakContinueStack.pop_back();
  EmitBranch(CondBlock);
  LoopStack.pop();
  // Emit the fall-through block.
  EmitBlock(LoopExit.getBlock());
}

bool CodeGenFunction::EmitACCLinearClauseInit(const ACCLoopLikeDirective &D) {
  if (!HaveInsertPoint())
    return false;
  // Emit inits for the linear variables.
  bool HasLinears = false;
  for (const auto *C : D.getClausesOfKind<ACCLinearClause>()) {
    for (auto *Init : C->inits()) {
      HasLinears = true;
      auto *VD = cast<VarDecl>(cast<DeclRefExpr>(Init)->getDecl());
      if (auto *Ref = dyn_cast<DeclRefExpr>(VD->getInit()->IgnoreImpCasts())) {
        AutoVarEmission Emission = EmitAutoVarAlloca(*VD);
        auto *OrigVD = cast<VarDecl>(Ref->getDecl());
        DeclRefExpr DRE(const_cast<VarDecl *>(OrigVD),
                        CapturedStmtInfo->lookup(OrigVD) != nullptr,
                        VD->getInit()->getType(), VK_LValue,
                        VD->getInit()->getExprLoc());
        EmitExprAsInit(&DRE, VD, MakeAddrLValue(Emission.getAllocatedAddress(),
                                                VD->getType()),
                       /*capturedByInit=*/false);
        EmitAutoVarCleanups(Emission);
      } else
        EmitVarDecl(*VD);
    }
    // Emit the linear steps for the linear clauses.
    // If a step is not constant, it is pre-calculated before the loop.
    if (auto CS = cast_or_null<BinaryOperator>(C->getCalcStep()))
      if (auto SaveRef = cast<DeclRefExpr>(CS->getLHS())) {
        EmitVarDecl(*cast<VarDecl>(SaveRef->getDecl()));
        // Emit calculation of the linear step.
        EmitIgnoredExpr(CS);
      }
  }
  return HasLinears;
}

void CodeGenFunction::EmitACCLinearClauseFinal(
    const ACCLoopLikeDirective &D,
    const llvm::function_ref<llvm::Value *(CodeGenFunction &)> &CondGen) {
  if (!HaveInsertPoint())
    return;
  llvm::BasicBlock *DoneBB = nullptr;
  // Emit the final values of the linear variables.
  for (const auto *C : D.getClausesOfKind<ACCLinearClause>()) {
    auto IC = C->varlist_begin();
    for (auto *F : C->finals()) {
      if (!DoneBB) {
        if (auto *Cond = CondGen(*this)) {
          // If the first post-update expression is found, emit conditional
          // block if it was requested.
          auto *ThenBB = createBasicBlock(".acc.linear.pu");
          DoneBB = createBasicBlock(".acc.linear.pu.done");
          Builder.CreateCondBr(Cond, ThenBB, DoneBB);
          EmitBlock(ThenBB);
        }
      }
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IC)->getDecl());
      DeclRefExpr DRE(const_cast<VarDecl *>(OrigVD),
                      CapturedStmtInfo->lookup(OrigVD) != nullptr,
                      (*IC)->getType(), VK_LValue, (*IC)->getExprLoc());
      Address OrigAddr = EmitLValue(&DRE).getAddress();
      CodeGenFunction::ACCPrivateScope VarScope(*this);
      VarScope.addPrivate(OrigVD, [OrigAddr]() -> Address { return OrigAddr; });
      (void)VarScope.Privatize();
      EmitIgnoredExpr(F);
      ++IC;
    }
    if (auto *PostUpdate = C->getPostUpdateExpr())
      EmitIgnoredExpr(PostUpdate);
  }
  if (DoneBB)
    EmitBlock(DoneBB, /*IsFinished=*/true);
}

static void emitAlignedClause(CodeGenFunction &CGF,
                              const ACCExecutableDirective &D) {
  if (!CGF.HaveInsertPoint())
    return;
  for (const auto *Clause : D.getClausesOfKind<ACCAlignedClause>()) {
    unsigned ClauseAlignment = 0;
    if (auto AlignmentExpr = Clause->getAlignment()) {
      auto AlignmentCI =
          cast<llvm::ConstantInt>(CGF.EmitScalarExpr(AlignmentExpr));
      ClauseAlignment = static_cast<unsigned>(AlignmentCI->getZExtValue());
    }
    for (auto E : Clause->varlists()) {
      unsigned Alignment = ClauseAlignment;
      if (Alignment == 0) {
        // OpenACC [2.8.1, Description]
        // If no optional parameter is specified, implementation-defined default
        // alignments for Vector instructions on the target platforms are assumed.
        Alignment =
            CGF.getContext()
                .toCharUnitsFromBits(CGF.getContext().getOpenACCDefaultVectorAlign(
                    E->getType()->getPointeeType()))
                .getQuantity();
      }
      assert((Alignment == 0 || llvm::isPowerOf2_32(Alignment)) &&
             "alignment is not power of 2");
      if (Alignment != 0) {
        llvm::Value *PtrValue = CGF.EmitScalarExpr(E);
        CGF.EmitAlignmentAssumption(PtrValue, Alignment);
      }
    }
  }
}

void CodeGenFunction::EmitACCPrivateLoopCounters(
    const ACCLoopLikeDirective &S, CodeGenFunction::ACCPrivateScope &LoopScope) {
  if (!HaveInsertPoint())
    return;
  auto I = S.private_counters().begin();
  for (auto *E : S.counters()) {
    auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
    auto *PrivateVD = cast<VarDecl>(cast<DeclRefExpr>(*I)->getDecl());
    (void)LoopScope.addPrivate(VD, [&]() -> Address {
      // Emit var without initialization.
      if (!LocalDeclMap.count(PrivateVD)) {
        auto VarEmission = EmitAutoVarAlloca(*PrivateVD);
        EmitAutoVarCleanups(VarEmission);
      }
      DeclRefExpr DRE(const_cast<VarDecl *>(PrivateVD),
                      /*RefersToEnclosingVariableOrCapture=*/false,
                      (*I)->getType(), VK_LValue, (*I)->getExprLoc());
      return EmitLValue(&DRE).getAddress();
    });
    if (LocalDeclMap.count(VD) || CapturedStmtInfo->lookup(VD) ||
        VD->hasGlobalStorage()) {
      (void)LoopScope.addPrivate(PrivateVD, [&]() -> Address {
        DeclRefExpr DRE(const_cast<VarDecl *>(VD),
                        LocalDeclMap.count(VD) || CapturedStmtInfo->lookup(VD),
                        E->getType(), VK_LValue, E->getExprLoc());
        return EmitLValue(&DRE).getAddress();
      });
    }
    ++I;
  }
}

static void emitPreCond(CodeGenFunction &CGF, const ACCLoopLikeDirective &S,
                        const Expr *Cond, llvm::BasicBlock *TrueBlock,
                        llvm::BasicBlock *FalseBlock, uint64_t TrueCount) {
  if (!CGF.HaveInsertPoint())
    return;
  {
    CodeGenFunction::ACCPrivateScope PreCondScope(CGF);
    CGF.EmitACCPrivateLoopCounters(S, PreCondScope);
    (void)PreCondScope.Privatize();
    // Get initial values of real counters.
    for (auto I : S.inits()) {
      CGF.EmitIgnoredExpr(I);
    }
  }
  // Check that loop is executed at least one time.
  CGF.EmitBranchOnBoolExpr(Cond, TrueBlock, FalseBlock, TrueCount);
}

void CodeGenFunction::EmitACCLinearClause(
    const ACCLoopLikeDirective &D, CodeGenFunction::ACCPrivateScope &PrivateScope) {
  if (!HaveInsertPoint())
    return;
  llvm::DenseSet<const VarDecl *> VectorLCVs;
  if (isOpenACCVectorDirective(D.getDirectiveKind())) {
    auto *LoopDirective = cast<ACCLoopLikeDirective>(&D);
    for (auto *C : LoopDirective->counters()) {
      VectorLCVs.insert(
          cast<VarDecl>(cast<DeclRefExpr>(C)->getDecl())->getCanonicalDecl());
    }
  }
  for (const auto *C : D.getClausesOfKind<ACCLinearClause>()) {
    auto CurPrivate = C->privates().begin();
    for (auto *E : C->varlists()) {
      auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
      auto *PrivateVD =
          cast<VarDecl>(cast<DeclRefExpr>(*CurPrivate)->getDecl());
      if (!VectorLCVs.count(VD->getCanonicalDecl())) {
        bool IsRegistered = PrivateScope.addPrivate(VD, [&]() -> Address {
          // Emit private VarDecl with copy init.
          EmitVarDecl(*PrivateVD);
          return GetAddrOfLocalVar(PrivateVD);
        });
        assert(IsRegistered && "linear var already registered as private");
        // Silence the warning about unused variable.
        (void)IsRegistered;
      } else
        EmitVarDecl(*PrivateVD);
      ++CurPrivate;
    }
  }
}

static void emitVectorlenSafelenClause(CodeGenFunction &CGF,
                                     const ACCExecutableDirective &D,
                                     bool IsMonotonic) {
  if (!CGF.HaveInsertPoint())
    return;
  if (const auto *C = D.getSingleClause<ACCVectorlenClause>()) {
    RValue Len = CGF.EmitAnyExpr(C->getVectorlen(), AggValueSlot::ignored(),
                                 /*ignoreResult=*/true);
    llvm::ConstantInt *Val = cast<llvm::ConstantInt>(Len.getScalarVal());
    CGF.LoopStack.setVectorizeWidth(Val->getZExtValue());
    // In presence of finite 'safelen', it may be unsafe to mark all
    // the memory instructions parallel, because loop-carried
    // dependences of 'safelen' iterations are possible.
    if (!IsMonotonic)
      CGF.LoopStack.setParallel(!D.getSingleClause<ACCSafelenClause>());
  } else if (const auto *C = D.getSingleClause<ACCSafelenClause>()) {
    RValue Len = CGF.EmitAnyExpr(C->getSafelen(), AggValueSlot::ignored(),
                                 /*ignoreResult=*/true);
    llvm::ConstantInt *Val = cast<llvm::ConstantInt>(Len.getScalarVal());
    CGF.LoopStack.setVectorizeWidth(Val->getZExtValue());
    // In presence of finite 'safelen', it may be unsafe to mark all
    // the memory instructions parallel, because loop-carried
    // dependences of 'safelen' iterations are possible.
    CGF.LoopStack.setParallel(false);
  }
}

void CodeGenFunction::EmitACCVectorInit(const ACCLoopLikeDirective &D,
                                      bool IsMonotonic) {
  // Walk clauses and process safelen/lastprivate.
  LoopStack.setParallel(!IsMonotonic);
  LoopStack.setVectorizeEnable(true);
  emitVectorlenSafelenClause(*this, D, IsMonotonic);
}

void CodeGenFunction::EmitACCVectorFinal(
    const ACCLoopLikeDirective &D,
    const llvm::function_ref<llvm::Value *(CodeGenFunction &)> &CondGen) {
  if (!HaveInsertPoint())
    return;
  llvm::BasicBlock *DoneBB = nullptr;
  auto IC = D.counters().begin();
  auto IPC = D.private_counters().begin();
  for (auto F : D.finals()) {
    auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>((*IC))->getDecl());
    auto *PrivateVD = cast<VarDecl>(cast<DeclRefExpr>((*IPC))->getDecl());
    auto *CED = dyn_cast<ACCCapturedExprDecl>(OrigVD);
    if (LocalDeclMap.count(OrigVD) || CapturedStmtInfo->lookup(OrigVD) ||
        OrigVD->hasGlobalStorage() || CED) {
      if (!DoneBB) {
        if (auto *Cond = CondGen(*this)) {
          // If the first post-update expression is found, emit conditional
          // block if it was requested.
          auto *ThenBB = createBasicBlock(".acc.final.then");
          DoneBB = createBasicBlock(".acc.final.done");
          Builder.CreateCondBr(Cond, ThenBB, DoneBB);
          EmitBlock(ThenBB);
        }
      }
      Address OrigAddr = Address::invalid();
      if (CED)
        OrigAddr = EmitLValue(CED->getInit()->IgnoreImpCasts()).getAddress();
      else {
        DeclRefExpr DRE(const_cast<VarDecl *>(PrivateVD),
                        /*RefersToEnclosingVariableOrCapture=*/false,
                        (*IPC)->getType(), VK_LValue, (*IPC)->getExprLoc());
        OrigAddr = EmitLValue(&DRE).getAddress();
      }
      ACCPrivateScope VarScope(*this);
      VarScope.addPrivate(OrigVD,
                          [OrigAddr]() -> Address { return OrigAddr; });
      (void)VarScope.Privatize();
      EmitIgnoredExpr(F);
    }
    ++IC;
    ++IPC;
  }
  if (DoneBB)
    EmitBlock(DoneBB, /*IsFinished=*/true);
}

static void emitACCLoopBodyWithStopPoint(CodeGenFunction &CGF,
                                         const ACCLoopLikeDirective &S,
                                         CodeGenFunction::JumpDest LoopExit) {
  CGF.EmitACCLoopBody(S, LoopExit);
  CGF.EmitStopPoint(&S);
}

/// Emit a helper variable and return corresponding lvalue.
static LValue EmitACCHelperVar(CodeGenFunction &CGF,
                               const DeclRefExpr *Helper) {
  auto VDecl = cast<VarDecl>(Helper->getDecl());
  CGF.EmitVarDecl(*VDecl);
  return CGF.EmitLValue(Helper);
}

static void emitACCVectorRegion(CodeGenFunction &CGF, const ACCLoopLikeDirective &S,
                              ACCPrePostActionTy &Action) {
  Action.Enter(CGF);
  assert(isOpenACCVectorDirective(S.getDirectiveKind()) &&
         "Expected vector directive");
  ACCLoopScope PreInitScope(CGF, S);
  // if (PreCond) {
  //   for (IV in 0..LastIteration) BODY;
  //   <Final counter/linear vars updates>;
  // }
  //
  if (isOpenACCDistributeDirective(S.getDirectiveKind()) ||
      isOpenACCWorksharingDirective(S.getDirectiveKind()) ||
      isOpenACCTaskLoopDirective(S.getDirectiveKind())) {
    (void)EmitACCHelperVar(CGF, cast<DeclRefExpr>(S.getLowerBoundVariable()));
    (void)EmitACCHelperVar(CGF, cast<DeclRefExpr>(S.getUpperBoundVariable()));
  }

  // Emit: if (PreCond) - begin.
  // If the condition constant folds and can be elided, avoid emitting the
  // whole loop.
  bool CondConstant;
  llvm::BasicBlock *ContBlock = nullptr;
  if (CGF.ConstantFoldsToSimpleInteger(S.getPreCond(), CondConstant)) {
    if (!CondConstant)
      return;
  } else {
    auto *ThenBlock = CGF.createBasicBlock("vector.if.then");
    ContBlock = CGF.createBasicBlock("vector.if.end");
    emitPreCond(CGF, S, S.getPreCond(), ThenBlock, ContBlock,
                CGF.getProfileCount(&S));
    CGF.EmitBlock(ThenBlock);
    CGF.incrementProfileCounter(&S);
  }

  // Emit the loop iteration variable.
  const Expr *IVExpr = S.getIterationVariable();
  const VarDecl *IVDecl = cast<VarDecl>(cast<DeclRefExpr>(IVExpr)->getDecl());
  CGF.EmitVarDecl(*IVDecl);
  CGF.EmitIgnoredExpr(S.getInit());

  // Emit the iterations count variable.
  // If it is not a variable, Sema decided to calculate iterations count on
  // each iteration (e.g., it is foldable into a constant).
  if (auto LIExpr = dyn_cast<DeclRefExpr>(S.getLastIteration())) {
    CGF.EmitVarDecl(*cast<VarDecl>(LIExpr->getDecl()));
    // Emit calculation of the iterations count.
    CGF.EmitIgnoredExpr(S.getCalcLastIteration());
  }

  CGF.EmitACCVectorInit(S);

  emitAlignedClause(CGF, S);
  (void)CGF.EmitACCLinearClauseInit(S);
  {
    CodeGenFunction::ACCPrivateScope LoopScope(CGF);
    CGF.EmitACCPrivateLoopCounters(S, LoopScope);
    CGF.EmitACCLinearClause(S, LoopScope);
    CGF.EmitACCPrivateClause(S, LoopScope);
    CGF.EmitACCReductionClauseInit(S, LoopScope);
    bool HasLastprivateClause = CGF.EmitACCLastprivateClauseInit(S, LoopScope);
    (void)LoopScope.Privatize();
    CGF.EmitACCInnerLoop(S, LoopScope.requiresCleanups(), S.getCond(),
                         S.getInc(),
                         [&S](CodeGenFunction &CGF) {
                           CGF.EmitACCLoopBody(S, CodeGenFunction::JumpDest());
                           CGF.EmitStopPoint(&S);
                         },
                         [](CodeGenFunction &) {});
    CGF.EmitACCVectorFinal(
        S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
    // Emit final copy of the lastprivate variables at the end of loops.
    if (HasLastprivateClause)
      CGF.EmitACCLastprivateClauseFinal(S, /*NoFinals=*/true);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_vector);
    emitPostUpdateForReductionClause(
        CGF, S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
  }
  CGF.EmitACCLinearClauseFinal(
      S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
  // Emit: if (PreCond) - end.
  if (ContBlock) {
    CGF.EmitBranch(ContBlock);
    CGF.EmitBlock(ContBlock, true);
  }
}

void CodeGenFunction::EmitACCVectorDirective(const ACCVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitACCVectorRegion(CGF, S, Action);
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_vector, CodeGen);
}

void CodeGenFunction::EmitACCOuterLoop(
    bool DynamicOrOrdered, bool IsMonotonic, const ACCLoopLikeDirective &S,
    CodeGenFunction::ACCPrivateScope &LoopScope,
    const CodeGenFunction::ACCLoopArguments &LoopArgs,
    const CodeGenFunction::ACCCodeGenLoopTy &CodeGenLoop,
    const CodeGenFunction::CodeGenOrderedTy &CodeGenOrdered) {
  auto &RT = CGM.getOpenACCRuntime();

  const Expr *IVExpr = S.getIterationVariable();
  const unsigned IVSize = getContext().getTypeSize(IVExpr->getType());
  const bool IVSigned = IVExpr->getType()->hasSignedIntegerRepresentation();

  auto LoopExit = getJumpDestInCurrentScope("acc.dispatch.end");

  // Start the loop with a block that tests the condition.
  auto CondBlock = createBasicBlock("acc.dispatch.cond");
  EmitBlock(CondBlock);
  const SourceRange &R = S.getSourceRange();
  LoopStack.push(CondBlock, SourceLocToDebugLoc(R.getBegin()),
                 SourceLocToDebugLoc(R.getEnd()));

  llvm::Value *BoolCondVal = nullptr;
  if (!DynamicOrOrdered) {
    // UB = min(UB, GlobalUB) or
    // UB = min(UB, PrevUB) for combined loop sharing constructs (e.g.
    // 'distribute parallel for')
    EmitIgnoredExpr(LoopArgs.EUB);
    // IV = LB
    EmitIgnoredExpr(LoopArgs.Init);
    // IV < UB
    BoolCondVal = EvaluateExprAsBool(LoopArgs.Cond);
  } else {
    BoolCondVal =
        RT.emitForNext(*this, S.getLocStart(), IVSize, IVSigned, LoopArgs.IL,
                       LoopArgs.LB, LoopArgs.UB, LoopArgs.ST);
  }

  // If there are any cleanups between here and the loop-exit scope,
  // create a block to stage a loop exit along.
  auto ExitBlock = LoopExit.getBlock();
  if (LoopScope.requiresCleanups())
    ExitBlock = createBasicBlock("acc.dispatch.cleanup");

  auto LoopBody = createBasicBlock("acc.dispatch.body");
  Builder.CreateCondBr(BoolCondVal, LoopBody, ExitBlock);
  if (ExitBlock != LoopExit.getBlock()) {
    EmitBlock(ExitBlock);
    EmitBranchThroughCleanup(LoopExit);
  }
  EmitBlock(LoopBody);

  // Emit "IV = LB" (in case of static schedule, we have already calculated new
  // LB for loop condition and emitted it above).
  if (DynamicOrOrdered)
    EmitIgnoredExpr(LoopArgs.Init);

  // Create a block for the increment.
  auto Continue = getJumpDestInCurrentScope("acc.dispatch.inc");
  BreakContinueStack.push_back(BreakContinue(LoopExit, Continue));

  // Generate !llvm.loop.parallel metadata for loads and stores for loops
  // with dynamic/guided scheduling and without ordered clause.
  if (!isOpenACCVectorDirective(S.getDirectiveKind()))
    LoopStack.setParallel(!IsMonotonic);
  else
    EmitACCVectorInit(S, IsMonotonic);

  SourceLocation Loc = S.getLocStart();

  // when 'distribute' is not combined with a 'for':
  // while (idx <= UB) { BODY; ++idx; }
  // when 'distribute' is combined with a 'for'
  // (e.g. 'distribute parallel for')
  // while (idx <= UB) { <CodeGen rest of pragma>; idx += ST; }
  EmitACCInnerLoop(
      S, LoopScope.requiresCleanups(), LoopArgs.Cond, LoopArgs.IncExpr,
      [&S, LoopExit, &CodeGenLoop](CodeGenFunction &CGF) {
        CodeGenLoop(CGF, S, LoopExit);
      },
      [IVSize, IVSigned, Loc, &CodeGenOrdered](CodeGenFunction &CGF) {
        CodeGenOrdered(CGF, Loc, IVSize, IVSigned);
      });

  EmitBlock(Continue.getBlock());
  BreakContinueStack.pop_back();
  if (!DynamicOrOrdered) {
    // Emit "LB = LB + Stride", "UB = UB + Stride".
    EmitIgnoredExpr(LoopArgs.NextLB);
    EmitIgnoredExpr(LoopArgs.NextUB);
  }

  EmitBranch(CondBlock);
  LoopStack.pop();
  // Emit the fall-through block.
  EmitBlock(LoopExit.getBlock());

  // Tell the runtime we are done.
  auto &&CodeGen = [DynamicOrOrdered, &S](CodeGenFunction &CGF) {
    if (!DynamicOrOrdered)
      CGF.CGM.getOpenACCRuntime().emitForStaticFinish(CGF, S.getLocEnd(),
                                                     S.getDirectiveKind());
  };
  ACCCancelStack.emitExit(*this, S.getDirectiveKind(), CodeGen);
}

void CodeGenFunction::EmitACCForOuterLoop(
    const OpenACCScheduleTy &ScheduleKind, bool IsMonotonic,
    const ACCLoopLikeDirective &S, ACCPrivateScope &LoopScope, bool Ordered,
    const ACCLoopArguments &LoopArgs,
    const ACCCodeGenDispatchBoundsTy &CGDispatchBounds) {
  auto &RT = CGM.getOpenACCRuntime();

  // Dynamic scheduling of the outer loop (dynamic, guided, auto, runtime).
  const bool DynamicOrOrdered =
      Ordered || RT.isDynamic(ScheduleKind.Schedule);

  assert((Ordered ||
          !RT.isStaticNonchunked(ScheduleKind.Schedule,
                                 LoopArgs.Chunk != nullptr)) &&
         "static non-chunked schedule does not need outer loop");

  // Emit outer loop.
  //
  // OpenACC [2.7.1, Loop Construct, Description, table 2-1]
  // When schedule(dynamic,chunk_size) is specified, the iterations are
  // distributed to threads in the team in chunks as the threads request them.
  // Each thread executes a chunk of iterations, then requests another chunk,
  // until no chunks remain to be distributed. Each chunk contains chunk_size
  // iterations, except for the last chunk to be distributed, which may have
  // fewer iterations. When no chunk_size is specified, it defaults to 1.
  //
  // When schedule(guided,chunk_size) is specified, the iterations are assigned
  // to threads in the team in chunks as the executing threads request them.
  // Each thread executes a chunk of iterations, then requests another chunk,
  // until no chunks remain to be assigned. For a chunk_size of 1, the size of
  // each chunk is proportional to the number of unassigned iterations divided
  // by the number of threads in the team, decreasing to 1. For a chunk_size
  // with value k (greater than 1), the size of each chunk is determined in the
  // same way, with the restriction that the chunks do not contain fewer than k
  // iterations (except for the last chunk to be assigned, which may have fewer
  // than k iterations).
  //
  // When schedule(auto) is specified, the decision regarding scheduling is
  // delegated to the compiler and/or runtime system. The programmer gives the
  // implementation the freedom to choose any possible mapping of iterations to
  // threads in the team.
  //
  // When schedule(runtime) is specified, the decision regarding scheduling is
  // deferred until run time, and the schedule and chunk size are taken from the
  // run-sched-var ICV. If the ICV is set to auto, the schedule is
  // implementation defined
  //
  // while(__kmpc_dispatch_next(&LB, &UB)) {
  //   idx = LB;
  //   while (idx <= UB) { BODY; ++idx;
  //   __kmpc_dispatch_fini_(4|8)[u](); // For ordered loops only.
  //   } // inner loop
  // }
  //
  // OpenACC [2.7.1, Loop Construct, Description, table 2-1]
  // When schedule(static, chunk_size) is specified, iterations are divided into
  // chunks of size chunk_size, and the chunks are assigned to the threads in
  // the team in a round-robin fashion in the order of the thread number.
  //
  // while(UB = min(UB, GlobalUB), idx = LB, idx < UB) {
  //   while (idx <= UB) { BODY; ++idx; } // inner loop
  //   LB = LB + ST;
  //   UB = UB + ST;
  // }
  //

  const Expr *IVExpr = S.getIterationVariable();
  const unsigned IVSize = getContext().getTypeSize(IVExpr->getType());
  const bool IVSigned = IVExpr->getType()->hasSignedIntegerRepresentation();

  if (DynamicOrOrdered) {
    auto DispatchBounds = CGDispatchBounds(*this, S, LoopArgs.LB, LoopArgs.UB);
    llvm::Value *LBVal = DispatchBounds.first;
    llvm::Value *UBVal = DispatchBounds.second;
    CGOpenACCRuntime::DispatchRTInput DipatchRTInputValues = {LBVal, UBVal,
                                                             LoopArgs.Chunk};
    RT.emitForDispatchInit(*this, S.getLocStart(), ScheduleKind, IVSize,
                           IVSigned, Ordered, DipatchRTInputValues);
  } else {
    CGOpenACCRuntime::StaticRTInput StaticInit(
        IVSize, IVSigned, Ordered, LoopArgs.IL, LoopArgs.LB, LoopArgs.UB,
        LoopArgs.ST, LoopArgs.Chunk);
    RT.emitForStaticInit(*this, S.getLocStart(), S.getDirectiveKind(),
                         ScheduleKind, StaticInit);
  }

  auto &&CodeGenOrdered = [Ordered](CodeGenFunction &CGF, SourceLocation Loc,
                                    const unsigned IVSize,
                                    const bool IVSigned) {
    if (Ordered) {
      CGF.CGM.getOpenACCRuntime().emitForOrderedIterationEnd(CGF, Loc, IVSize,
                                                            IVSigned);
    }
  };

  ACCLoopArguments OuterLoopArgs(LoopArgs.LB, LoopArgs.UB, LoopArgs.ST,
                                 LoopArgs.IL, LoopArgs.Chunk, LoopArgs.EUB);
  OuterLoopArgs.IncExpr = S.getInc();
  OuterLoopArgs.Init = S.getInit();
  OuterLoopArgs.Cond = S.getCond();
  OuterLoopArgs.NextLB = S.getNextLowerBound();
  OuterLoopArgs.NextUB = S.getNextUpperBound();
  EmitACCOuterLoop(DynamicOrOrdered, IsMonotonic, S, LoopScope, OuterLoopArgs,
                   emitACCLoopBodyWithStopPoint, CodeGenOrdered);
}

static void emitEmptyOrdered(CodeGenFunction &, SourceLocation Loc,
                             const unsigned IVSize, const bool IVSigned) {}

void CodeGenFunction::EmitACCDistributeOuterLoop(
    OpenACCDistScheduleClauseKind ScheduleKind, const ACCLoopLikeDirective &S,
    ACCPrivateScope &LoopScope, const ACCLoopArguments &LoopArgs,
    const ACCCodeGenLoopTy &CodeGenLoopContent) {

  auto &RT = CGM.getOpenACCRuntime();

  // Emit outer loop.
  // Same behavior as a ACCForOuterLoop, except that schedule cannot be
  // dynamic
  //

  const Expr *IVExpr = S.getIterationVariable();
  const unsigned IVSize = getContext().getTypeSize(IVExpr->getType());
  const bool IVSigned = IVExpr->getType()->hasSignedIntegerRepresentation();

  CGOpenACCRuntime::StaticRTInput StaticInit(
      IVSize, IVSigned, /* Ordered = */ false, LoopArgs.IL, LoopArgs.LB,
      LoopArgs.UB, LoopArgs.ST, LoopArgs.Chunk);
  RT.emitDistributeStaticInit(*this, S.getLocStart(), ScheduleKind, StaticInit);

  // for combined 'distribute' and 'for' the increment expression of distribute
  // is store in DistInc. For 'distribute' alone, it is in Inc.
  Expr *IncExpr;
  if (isOpenACCLoopBoundSharingDirective(S.getDirectiveKind()))
    IncExpr = S.getDistInc();
  else
    IncExpr = S.getInc();

  // this routine is shared by 'acc distribute parallel for' and
  // 'acc distribute': select the right EUB expression depending on the
  // directive
  ACCLoopArguments OuterLoopArgs;
  OuterLoopArgs.LB = LoopArgs.LB;
  OuterLoopArgs.UB = LoopArgs.UB;
  OuterLoopArgs.ST = LoopArgs.ST;
  OuterLoopArgs.IL = LoopArgs.IL;
  OuterLoopArgs.Chunk = LoopArgs.Chunk;
  OuterLoopArgs.EUB = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                          ? S.getCombinedEnsureUpperBound()
                          : S.getEnsureUpperBound();
  OuterLoopArgs.IncExpr = IncExpr;
  OuterLoopArgs.Init = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                           ? S.getCombinedInit()
                           : S.getInit();
  OuterLoopArgs.Cond = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                           ? S.getCombinedCond()
                           : S.getCond();
  OuterLoopArgs.NextLB = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                             ? S.getCombinedNextLowerBound()
                             : S.getNextLowerBound();
  OuterLoopArgs.NextUB = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                             ? S.getCombinedNextUpperBound()
                             : S.getNextUpperBound();

  EmitACCOuterLoop(/* DynamicOrOrdered = */ false, /* IsMonotonic = */ false, S,
                   LoopScope, OuterLoopArgs, CodeGenLoopContent,
                   emitEmptyOrdered);
}

static std::pair<LValue, LValue>
emitDistributeParallelForInnerBounds(CodeGenFunction &CGF,
                                     const ACCExecutableDirective &S) {
  const ACCLoopLikeDirective &LS = cast<ACCLoopLikeDirective>(S);
  LValue LB =
      EmitACCHelperVar(CGF, cast<DeclRefExpr>(LS.getLowerBoundVariable()));
  LValue UB =
      EmitACCHelperVar(CGF, cast<DeclRefExpr>(LS.getUpperBoundVariable()));

  // When composing 'distribute' with 'for' (e.g. as in 'distribute
  // parallel for') we need to use the 'distribute'
  // chunk lower and upper bounds rather than the whole loop iteration
  // space. These are parameters to the outlined function for 'parallel'
  // and we copy the bounds of the previous schedule into the
  // the current ones.
  LValue PrevLB = CGF.EmitLValue(LS.getPrevLowerBoundVariable());
  LValue PrevUB = CGF.EmitLValue(LS.getPrevUpperBoundVariable());
  llvm::Value *PrevLBVal = CGF.EmitLoadOfScalar(
      PrevLB, LS.getPrevLowerBoundVariable()->getExprLoc());
  PrevLBVal = CGF.EmitScalarConversion(
      PrevLBVal, LS.getPrevLowerBoundVariable()->getType(),
      LS.getIterationVariable()->getType(),
      LS.getPrevLowerBoundVariable()->getExprLoc());
  llvm::Value *PrevUBVal = CGF.EmitLoadOfScalar(
      PrevUB, LS.getPrevUpperBoundVariable()->getExprLoc());
  PrevUBVal = CGF.EmitScalarConversion(
      PrevUBVal, LS.getPrevUpperBoundVariable()->getType(),
      LS.getIterationVariable()->getType(),
      LS.getPrevUpperBoundVariable()->getExprLoc());

  CGF.EmitStoreOfScalar(PrevLBVal, LB);
  CGF.EmitStoreOfScalar(PrevUBVal, UB);

  return {LB, UB};
}

/// if the 'for' loop has a dispatch schedule (e.g. dynamic, guided) then
/// we need to use the LB and UB expressions generated by the worksharing
/// code generation support, whereas in non combined situations we would
/// just emit 0 and the LastIteration expression
/// This function is necessary due to the difference of the LB and UB
/// types for the RT emission routines for 'for_static_init' and
/// 'for_dispatch_init'
static std::pair<llvm::Value *, llvm::Value *>
emitDistributeParallelForDispatchBounds(CodeGenFunction &CGF,
                                        const ACCExecutableDirective &S,
                                        Address LB, Address UB) {
  const ACCLoopLikeDirective &LS = cast<ACCLoopLikeDirective>(S);
  const Expr *IVExpr = LS.getIterationVariable();
  // when implementing a dynamic schedule for a 'for' combined with a
  // 'distribute' (e.g. 'distribute parallel for'), the 'for' loop
  // is not normalized as each team only executes its own assigned
  // distribute chunk
  QualType IteratorTy = IVExpr->getType();
  llvm::Value *LBVal =
      CGF.EmitLoadOfScalar(LB, /*Volatile=*/false, IteratorTy, S.getLocStart());
  llvm::Value *UBVal =
      CGF.EmitLoadOfScalar(UB, /*Volatile=*/false, IteratorTy, S.getLocStart());
  return {LBVal, UBVal};
}

static void emitDistributeParallelForDistributeInnerBoundParams(
    CodeGenFunction &CGF, const ACCExecutableDirective &S,
    llvm::SmallVectorImpl<llvm::Value *> &CapturedVars) {
  const auto &Dir = cast<ACCLoopLikeDirective>(S);
  LValue LB =
      CGF.EmitLValue(cast<DeclRefExpr>(Dir.getCombinedLowerBoundVariable()));
  auto LBCast = CGF.Builder.CreateIntCast(
      CGF.Builder.CreateLoad(LB.getAddress()), CGF.SizeTy, /*isSigned=*/false);
  CapturedVars.push_back(LBCast);
  LValue UB =
      CGF.EmitLValue(cast<DeclRefExpr>(Dir.getCombinedUpperBoundVariable()));

  auto UBCast = CGF.Builder.CreateIntCast(
      CGF.Builder.CreateLoad(UB.getAddress()), CGF.SizeTy, /*isSigned=*/false);
  CapturedVars.push_back(UBCast);
}

static void
emitInnerParallelForWhenCombined(CodeGenFunction &CGF,
                                 const ACCLoopLikeDirective &S,
                                 CodeGenFunction::JumpDest LoopExit) {
  auto &&CGInlinedWorksharingLoop = [&S](CodeGenFunction &CGF,
                                         ACCPrePostActionTy &) {
    bool HasCancel = false;
    if (!isOpenACCVectorDirective(S.getDirectiveKind())) {
      if (const auto *D = dyn_cast<ACCGangDistributeParallelLoopDirective>(&S))
        HasCancel = D->hasCancel();
      else if (const auto *D = dyn_cast<ACCDistributeParallelLoopDirective>(&S))
        HasCancel = D->hasCancel();
      else if (const auto *D =
                   dyn_cast<ACCTargetGangDistributeParallelLoopDirective>(&S))
        HasCancel = D->hasCancel();
    }
    CodeGenFunction::ACCCancelStackRAII CancelRegion(CGF, S.getDirectiveKind(),
                                                     HasCancel);
    CGF.EmitACCWorksharingLoop(S, S.getPrevEnsureUpperBound(),
                               emitDistributeParallelForInnerBounds,
                               emitDistributeParallelForDispatchBounds);
  };

  emitCommonACCParallelDirective(
      CGF, S,
      isOpenACCVectorDirective(S.getDirectiveKind()) ? ACCD_loop_vector : ACCD_loop,
      CGInlinedWorksharingLoop,
      emitDistributeParallelForDistributeInnerBoundParams);
}

void CodeGenFunction::EmitACCDistributeParallelLoopDirective(
    const ACCDistributeParallelLoopDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };
  ACCLexicalScope Scope(*this, S, ACCD_parallel);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_distribute, CodeGen);
}

void CodeGenFunction::EmitACCDistributeParallelLoopVectorDirective(
    const ACCDistributeParallelLoopVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };
  ACCLexicalScope Scope(*this, S, ACCD_parallel);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_distribute, CodeGen);
}

void CodeGenFunction::EmitACCDistributeVectorDirective(
    const ACCDistributeVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_vector, CodeGen);
}

void CodeGenFunction::EmitACCTargetVectorDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName, const ACCTargetVectorDirective &S) {
  // Emit SPMD target parallel for region as a standalone region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitACCVectorRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetVectorDirective(
    const ACCTargetVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitACCVectorRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

namespace {
  struct ScheduleKindModifiersTy {
    OpenACCScheduleClauseKind Kind;
    OpenACCScheduleClauseModifier M1;
    OpenACCScheduleClauseModifier M2;
    ScheduleKindModifiersTy(OpenACCScheduleClauseKind Kind,
                            OpenACCScheduleClauseModifier M1,
                            OpenACCScheduleClauseModifier M2)
        : Kind(Kind), M1(M1), M2(M2) {}
  };
} // namespace

bool CodeGenFunction::EmitACCWorksharingLoop(
    const ACCLoopLikeDirective &S, Expr *EUB,
    const ACCCodeGenLoopBoundsTy &CodeGenLoopBounds,
    const ACCCodeGenDispatchBoundsTy &CGDispatchBounds) {
  // Emit the loop iteration variable.
  auto IVExpr = cast<DeclRefExpr>(S.getIterationVariable());
  auto IVDecl = cast<VarDecl>(IVExpr->getDecl());
  EmitVarDecl(*IVDecl);

  // Emit the iterations count variable.
  // If it is not a variable, Sema decided to calculate iterations count on each
  // iteration (e.g., it is foldable into a constant).
  if (auto LIExpr = dyn_cast<DeclRefExpr>(S.getLastIteration())) {
    EmitVarDecl(*cast<VarDecl>(LIExpr->getDecl()));
    // Emit calculation of the iterations count.
    EmitIgnoredExpr(S.getCalcLastIteration());
  }

  auto &RT = CGM.getOpenACCRuntime();

  bool HasLastprivateClause;
  // Check pre-condition.
  {
    ACCLoopScope PreInitScope(*this, S);
    // Skip the entire loop if we don't meet the precondition.
    // If the condition constant folds and can be elided, avoid emitting the
    // whole loop.
    bool CondConstant;
    llvm::BasicBlock *ContBlock = nullptr;
    if (ConstantFoldsToSimpleInteger(S.getPreCond(), CondConstant)) {
      if (!CondConstant)
        return false;
    } else {
      auto *ThenBlock = createBasicBlock("acc.precond.then");
      ContBlock = createBasicBlock("acc.precond.end");
      emitPreCond(*this, S, S.getPreCond(), ThenBlock, ContBlock,
                  getProfileCount(&S));
      EmitBlock(ThenBlock);
      incrementProfileCounter(&S);
    }

    RunCleanupsScope DoacrossCleanupScope(*this);
    bool Ordered = false;
    if (auto *OrderedClause = S.getSingleClause<ACCOrderedClause>()) {
      if (OrderedClause->getNumForLoops())
        RT.emitDoacrossInit(*this, S);
      else
        Ordered = true;
    }

    llvm::DenseSet<const Expr *> EmittedFinals;
    emitAlignedClause(*this, S);
    bool HasLinears = EmitACCLinearClauseInit(S);
    // Emit helper vars inits.

    std::pair<LValue, LValue> Bounds = CodeGenLoopBounds(*this, S);
    LValue LB = Bounds.first;
    LValue UB = Bounds.second;
    LValue ST =
        EmitACCHelperVar(*this, cast<DeclRefExpr>(S.getStrideVariable()));
    LValue IL =
        EmitACCHelperVar(*this, cast<DeclRefExpr>(S.getIsLastIterVariable()));

    // Emit 'then' code.
    {
      ACCPrivateScope LoopScope(*this);
      if (EmitACCFirstprivateClause(S, LoopScope) || HasLinears) {
        // Emit implicit barrier to synchronize threads and avoid data races on
        // initialization of firstprivate variables and post-update of
        // lastprivate variables.
        CGM.getOpenACCRuntime().emitBarrierCall(
            *this, S.getLocStart(), ACCD_unknown, /*EmitChecks=*/false,
            /*ForceSimpleCall=*/true);
      }
      EmitACCPrivateClause(S, LoopScope);
      HasLastprivateClause = EmitACCLastprivateClauseInit(S, LoopScope);
      EmitACCReductionClauseInit(S, LoopScope);
      EmitACCPrivateLoopCounters(S, LoopScope);
      EmitACCLinearClause(S, LoopScope);
      (void)LoopScope.Privatize();

      // Detect the loop schedule kind and chunk.
      llvm::Value *Chunk = nullptr;
      OpenACCScheduleTy ScheduleKind;
      if (auto *C = S.getSingleClause<ACCScheduleClause>()) {
        ScheduleKind.Schedule = C->getScheduleKind();
        ScheduleKind.M1 = C->getFirstScheduleModifier();
        ScheduleKind.M2 = C->getSecondScheduleModifier();
        if (const auto *Ch = C->getChunkSize()) {
          Chunk = EmitScalarExpr(Ch);
          Chunk = EmitScalarConversion(Chunk, Ch->getType(),
                                       S.getIterationVariable()->getType(),
                                       S.getLocStart());
        }
      }
      const unsigned IVSize = getContext().getTypeSize(IVExpr->getType());
      const bool IVSigned = IVExpr->getType()->hasSignedIntegerRepresentation();
      // OpenACC 4.5, 2.7.1 Loop Construct, Description.
      // If the static schedule kind is specified or if the ordered clause is
      // specified, and if no monotonic modifier is specified, the effect will
      // be as if the monotonic modifier was specified.
      if (RT.isStaticNonchunked(ScheduleKind.Schedule,
                                /* Chunked */ Chunk != nullptr) &&
          !Ordered) {
        if (isOpenACCVectorDirective(S.getDirectiveKind()))
          EmitACCVectorInit(S, /*IsMonotonic=*/true);
        // OpenACC [2.7.1, Loop Construct, Description, table 2-1]
        // When no chunk_size is specified, the iteration space is divided into
        // chunks that are approximately equal in size, and at most one chunk is
        // distributed to each thread. Note that the size of the chunks is
        // unspecified in this case.
        CGOpenACCRuntime::StaticRTInput StaticInit(
            IVSize, IVSigned, Ordered, IL.getAddress(), LB.getAddress(),
            UB.getAddress(), ST.getAddress());
        RT.emitForStaticInit(*this, S.getLocStart(), S.getDirectiveKind(),
                             ScheduleKind, StaticInit);
        auto LoopExit =
            getJumpDestInCurrentScope(createBasicBlock("acc.loop.exit"));
        // UB = min(UB, GlobalUB);
        EmitIgnoredExpr(S.getEnsureUpperBound());
        // IV = LB;
        EmitIgnoredExpr(S.getInit());
        // while (idx <= UB) { BODY; ++idx; }
        EmitACCInnerLoop(S, LoopScope.requiresCleanups(), S.getCond(),
                         S.getInc(),
                         [&S, LoopExit](CodeGenFunction &CGF) {
                           CGF.EmitACCLoopBody(S, LoopExit);
                           CGF.EmitStopPoint(&S);
                         },
                         [](CodeGenFunction &) {});
        EmitBlock(LoopExit.getBlock());
        // Tell the runtime we are done.
        auto &&CodeGen = [&S](CodeGenFunction &CGF) {
          CGF.CGM.getOpenACCRuntime().emitForStaticFinish(CGF, S.getLocEnd(),
                                                         S.getDirectiveKind());
        };
        ACCCancelStack.emitExit(*this, S.getDirectiveKind(), CodeGen);
      } else {
        const bool IsMonotonic =
            Ordered || ScheduleKind.Schedule == ACCC_SCHEDULE_static ||
            ScheduleKind.Schedule == ACCC_SCHEDULE_unknown ||
            ScheduleKind.M1 == ACCC_SCHEDULE_MODIFIER_monotonic ||
            ScheduleKind.M2 == ACCC_SCHEDULE_MODIFIER_monotonic;
        // Emit the outer loop, which requests its work chunk [LB..UB] from
        // runtime and runs the inner loop to process it.
        const ACCLoopArguments LoopArguments(LB.getAddress(), UB.getAddress(),
                                             ST.getAddress(), IL.getAddress(),
                                             Chunk, EUB);
        EmitACCForOuterLoop(ScheduleKind, IsMonotonic, S, LoopScope, Ordered,
                            LoopArguments, CGDispatchBounds);
      }
      if (isOpenACCVectorDirective(S.getDirectiveKind())) {
        EmitACCVectorFinal(S,
                         [&](CodeGenFunction &CGF) -> llvm::Value * {
                           return CGF.Builder.CreateIsNotNull(
                               CGF.EmitLoadOfScalar(IL, S.getLocStart()));
                         });
      }
      EmitACCReductionClauseFinal(
          S, /*ReductionKind=*/isOpenACCVectorDirective(S.getDirectiveKind())
                 ? /*Parallel and Vector*/ ACCD_parallel_loop_vector
                 : /*Parallel only*/ ACCD_parallel);
      // Emit post-update of the reduction variables if IsLastIter != 0.
      emitPostUpdateForReductionClause(
          *this, S, [&](CodeGenFunction &CGF) -> llvm::Value * {
            return CGF.Builder.CreateIsNotNull(
                CGF.EmitLoadOfScalar(IL, S.getLocStart()));
          });
      // Emit final copy of the lastprivate variables if IsLastIter != 0.
      if (HasLastprivateClause)
        EmitACCLastprivateClauseFinal(
            S, isOpenACCVectorDirective(S.getDirectiveKind()),
            Builder.CreateIsNotNull(EmitLoadOfScalar(IL, S.getLocStart())));
    }
    EmitACCLinearClauseFinal(S, [&](CodeGenFunction &CGF) -> llvm::Value * {
      return CGF.Builder.CreateIsNotNull(
          CGF.EmitLoadOfScalar(IL, S.getLocStart()));
    });
    DoacrossCleanupScope.ForceCleanup();
    // We're now done with the loop, so jump to the continuation block.
    if (ContBlock) {
      EmitBranch(ContBlock);
      EmitBlock(ContBlock, true);
    }
  }
  return HasLastprivateClause;
}

/// The following two functions generate expressions for the loop lower
/// and upper bounds in case of static and dynamic (dispatch) schedule
/// of the associated 'for' or 'distribute' loop.
static std::pair<LValue, LValue>
emitForLoopBounds(CodeGenFunction &CGF, const ACCExecutableDirective &S) {
  const ACCLoopLikeDirective &LS = cast<ACCLoopLikeDirective>(S);
  LValue LB =
      EmitACCHelperVar(CGF, cast<DeclRefExpr>(LS.getLowerBoundVariable()));
  LValue UB =
      EmitACCHelperVar(CGF, cast<DeclRefExpr>(LS.getUpperBoundVariable()));
  return {LB, UB};
}

/// When dealing with dispatch schedules (e.g. dynamic, guided) we do not
/// consider the lower and upper bound expressions generated by the
/// worksharing loop support, but we use 0 and the iteration space size as
/// constants
static std::pair<llvm::Value *, llvm::Value *>
emitDispatchForLoopBounds(CodeGenFunction &CGF, const ACCExecutableDirective &S,
                          Address LB, Address UB) {
  const ACCLoopLikeDirective &LS = cast<ACCLoopLikeDirective>(S);
  const Expr *IVExpr = LS.getIterationVariable();
  const unsigned IVSize = CGF.getContext().getTypeSize(IVExpr->getType());
  llvm::Value *LBVal = CGF.Builder.getIntN(IVSize, 0);
  llvm::Value *UBVal = CGF.EmitScalarExpr(LS.getLastIteration());
  return {LBVal, UBVal};
}

void CodeGenFunction::EmitACCLoopDirective(const ACCLoopDirective &S) {
  bool HasLastprivates = false;
  auto &&CodeGen = [&S, &HasLastprivates](CodeGenFunction &CGF,
                                          ACCPrePostActionTy &) {
    ACCCancelStackRAII CancelRegion(CGF, ACCD_loop, S.hasCancel());
    HasLastprivates = CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(),
                                                 emitForLoopBounds,
                                                 emitDispatchForLoopBounds);
  };
  {
    ACCLexicalScope Scope(*this, S, ACCD_unknown);
    CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_loop, CodeGen,
                                                S.hasCancel());
  }

  // Emit an implicit barrier at the end.
  if (!S.getSingleClause<ACCNowaitClause>() || HasLastprivates) {
    CGM.getOpenACCRuntime().emitBarrierCall(*this, S.getLocStart(), ACCD_loop);
  }
}

void CodeGenFunction::EmitACCLoopVectorDirective(const ACCLoopVectorDirective &S) {
  bool HasLastprivates = false;
  auto &&CodeGen = [&S, &HasLastprivates](CodeGenFunction &CGF,
                                          ACCPrePostActionTy &) {
    HasLastprivates = CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(),
                                                 emitForLoopBounds,
                                                 emitDispatchForLoopBounds);
  };
  {
    ACCLexicalScope Scope(*this, S, ACCD_unknown);
    CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_vector, CodeGen);
  }

  // Emit an implicit barrier at the end.
  if (!S.getSingleClause<ACCNowaitClause>() || HasLastprivates) {
    CGM.getOpenACCRuntime().emitBarrierCall(*this, S.getLocStart(), ACCD_loop);
  }
}

static LValue createSectionLVal(CodeGenFunction &CGF, QualType Ty,
                                const Twine &Name,
                                llvm::Value *Init = nullptr) {
  auto LVal = CGF.MakeAddrLValue(CGF.CreateMemTemp(Ty, Name), Ty);
  if (Init)
    CGF.EmitStoreThroughLValue(RValue::get(Init), LVal, /*isInit*/ true);
  return LVal;
}

void CodeGenFunction::EmitSections(const ACCExecutableDirective &S) {
  const Stmt *Stmt = S.getInnermostCapturedStmt()->getCapturedStmt();
  const auto *CS = dyn_cast<CompoundStmt>(Stmt);
  bool HasLastprivates = false;
  auto &&CodeGen = [&S, Stmt, CS, &HasLastprivates](CodeGenFunction &CGF,
                                                    ACCPrePostActionTy &) {
    auto &C = CGF.CGM.getContext();
    auto KmpInt32Ty = C.getIntTypeForBitwidth(/*DestWidth=*/32, /*Signed=*/1);
    // Emit helper vars inits.
    LValue LB = createSectionLVal(CGF, KmpInt32Ty, ".acc.sections.lb.",
                                  CGF.Builder.getInt32(0));
    auto *GlobalUBVal = CS != nullptr ? CGF.Builder.getInt32(CS->size() - 1)
                                      : CGF.Builder.getInt32(0);
    LValue UB =
        createSectionLVal(CGF, KmpInt32Ty, ".acc.sections.ub.", GlobalUBVal);
    LValue ST = createSectionLVal(CGF, KmpInt32Ty, ".acc.sections.st.",
                                  CGF.Builder.getInt32(1));
    LValue IL = createSectionLVal(CGF, KmpInt32Ty, ".acc.sections.il.",
                                  CGF.Builder.getInt32(0));
    // Loop counter.
    LValue IV = createSectionLVal(CGF, KmpInt32Ty, ".acc.sections.iv.");
    OpaqueValueExpr IVRefExpr(S.getLocStart(), KmpInt32Ty, VK_LValue);
    CodeGenFunction::OpaqueValueMapping OpaqueIV(CGF, &IVRefExpr, IV);
    OpaqueValueExpr UBRefExpr(S.getLocStart(), KmpInt32Ty, VK_LValue);
    CodeGenFunction::OpaqueValueMapping OpaqueUB(CGF, &UBRefExpr, UB);
    // Generate condition for loop.
    BinaryOperator Cond(&IVRefExpr, &UBRefExpr, BO_LE, C.BoolTy, VK_RValue,
                        OK_Ordinary, S.getLocStart(), FPOptions());
    // Increment for loop counter.
    UnaryOperator Inc(&IVRefExpr, UO_PreInc, KmpInt32Ty, VK_RValue, OK_Ordinary,
                      S.getLocStart(), true);
    auto BodyGen = [Stmt, CS, &S, &IV](CodeGenFunction &CGF) {
      // Iterate through all sections and emit a switch construct:
      // switch (IV) {
      //   case 0:
      //     <SectionStmt[0]>;
      //     break;
      // ...
      //   case <NumSection> - 1:
      //     <SectionStmt[<NumSection> - 1]>;
      //     break;
      // }
      // .acc.sections.exit:
      auto *ExitBB = CGF.createBasicBlock(".acc.sections.exit");
      auto *SwitchStmt =
          CGF.Builder.CreateSwitch(CGF.EmitLoadOfScalar(IV, S.getLocStart()),
                                   ExitBB, CS == nullptr ? 1 : CS->size());
      if (CS) {
        unsigned CaseNumber = 0;
        for (auto *SubStmt : CS->children()) {
          auto CaseBB = CGF.createBasicBlock(".acc.sections.case");
          CGF.EmitBlock(CaseBB);
          SwitchStmt->addCase(CGF.Builder.getInt32(CaseNumber), CaseBB);
          CGF.EmitStmt(SubStmt);
          CGF.EmitBranch(ExitBB);
          ++CaseNumber;
        }
      } else {
        auto CaseBB = CGF.createBasicBlock(".acc.sections.case");
        CGF.EmitBlock(CaseBB);
        SwitchStmt->addCase(CGF.Builder.getInt32(0), CaseBB);
        CGF.EmitStmt(Stmt);
        CGF.EmitBranch(ExitBB);
      }
      CGF.EmitBlock(ExitBB, /*IsFinished=*/true);
    };

    CodeGenFunction::ACCPrivateScope LoopScope(CGF);
    if (CGF.EmitACCFirstprivateClause(S, LoopScope)) {
      // Emit implicit barrier to synchronize threads and avoid data races on
      // initialization of firstprivate variables and post-update of lastprivate
      // variables.
      CGF.CGM.getOpenACCRuntime().emitBarrierCall(
          CGF, S.getLocStart(), ACCD_unknown, /*EmitChecks=*/false,
          /*ForceSimpleCall=*/true);
    }
    CGF.EmitACCPrivateClause(S, LoopScope);
    HasLastprivates = CGF.EmitACCLastprivateClauseInit(S, LoopScope);
    CGF.EmitACCReductionClauseInit(S, LoopScope);
    (void)LoopScope.Privatize();

    // Emit static non-chunked loop.
    OpenACCScheduleTy ScheduleKind;
    ScheduleKind.Schedule = ACCC_SCHEDULE_static;
    CGOpenACCRuntime::StaticRTInput StaticInit(
        /*IVSize=*/32, /*IVSigned=*/true, /*Ordered=*/false, IL.getAddress(),
        LB.getAddress(), UB.getAddress(), ST.getAddress());
    CGF.CGM.getOpenACCRuntime().emitForStaticInit(
        CGF, S.getLocStart(), S.getDirectiveKind(), ScheduleKind, StaticInit);
    // UB = min(UB, GlobalUB);
    auto *UBVal = CGF.EmitLoadOfScalar(UB, S.getLocStart());
    auto *MinUBGlobalUB = CGF.Builder.CreateSelect(
        CGF.Builder.CreateICmpSLT(UBVal, GlobalUBVal), UBVal, GlobalUBVal);
    CGF.EmitStoreOfScalar(MinUBGlobalUB, UB);
    // IV = LB;
    CGF.EmitStoreOfScalar(CGF.EmitLoadOfScalar(LB, S.getLocStart()), IV);
    // while (idx <= UB) { BODY; ++idx; }
    CGF.EmitACCInnerLoop(S, /*RequiresCleanup=*/false, &Cond, &Inc, BodyGen,
                         [](CodeGenFunction &) {});
    // Tell the runtime we are done.
    auto &&CodeGen = [&S](CodeGenFunction &CGF) {
      CGF.CGM.getOpenACCRuntime().emitForStaticFinish(CGF, S.getLocEnd(),
                                                     S.getDirectiveKind());
    };
    CGF.ACCCancelStack.emitExit(CGF, S.getDirectiveKind(), CodeGen);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_parallel);
    // Emit post-update of the reduction variables if IsLastIter != 0.
    emitPostUpdateForReductionClause(
        CGF, S, [&](CodeGenFunction &CGF) -> llvm::Value * {
          return CGF.Builder.CreateIsNotNull(
              CGF.EmitLoadOfScalar(IL, S.getLocStart()));
        });

    // Emit final copy of the lastprivate variables if IsLastIter != 0.
    if (HasLastprivates)
      CGF.EmitACCLastprivateClauseFinal(
          S, /*NoFinals=*/false,
          CGF.Builder.CreateIsNotNull(
              CGF.EmitLoadOfScalar(IL, S.getLocStart())));
  };

  bool HasCancel = false;
  if (auto *OSD = dyn_cast<ACCSectionsDirective>(&S))
    HasCancel = OSD->hasCancel();
  else if (auto *OPSD = dyn_cast<ACCParallelSectionsDirective>(&S))
    HasCancel = OPSD->hasCancel();
  ACCCancelStackRAII CancelRegion(*this, S.getDirectiveKind(), HasCancel);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_sections, CodeGen,
                                              HasCancel);
  // Emit barrier for lastprivates only if 'sections' directive has 'nowait'
  // clause. Otherwise the barrier will be generated by the codegen for the
  // directive.
  if (HasLastprivates && S.getSingleClause<ACCNowaitClause>()) {
    // Emit implicit barrier to synchronize threads and avoid data races on
    // initialization of firstprivate variables.
    CGM.getOpenACCRuntime().emitBarrierCall(*this, S.getLocStart(),
                                           ACCD_unknown);
  }
}

void CodeGenFunction::EmitACCSectionsDirective(const ACCSectionsDirective &S) {
  {
    ACCLexicalScope Scope(*this, S, ACCD_unknown);
    EmitSections(S);
  }
  // Emit an implicit barrier at the end.
  if (!S.getSingleClause<ACCNowaitClause>()) {
    CGM.getOpenACCRuntime().emitBarrierCall(*this, S.getLocStart(),
                                           ACCD_sections);
  }
}

void CodeGenFunction::EmitACCSectionDirective(const ACCSectionDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_section, CodeGen,
                                              S.hasCancel());
}

void CodeGenFunction::EmitACCSingleDirective(const ACCSingleDirective &S) {
  llvm::SmallVector<const Expr *, 8> CopyprivateVars;
  llvm::SmallVector<const Expr *, 8> DestExprs;
  llvm::SmallVector<const Expr *, 8> SrcExprs;
  llvm::SmallVector<const Expr *, 8> AssignmentOps;
  // Check if there are any 'copyprivate' clauses associated with this
  // 'single' construct.
  // Build a list of copyprivate variables along with helper expressions
  // (<source>, <destination>, <destination>=<source> expressions)
  for (const auto *C : S.getClausesOfKind<ACCCopyprivateClause>()) {
    CopyprivateVars.append(C->varlists().begin(), C->varlists().end());
    DestExprs.append(C->destination_exprs().begin(),
                     C->destination_exprs().end());
    SrcExprs.append(C->source_exprs().begin(), C->source_exprs().end());
    AssignmentOps.append(C->assignment_ops().begin(),
                         C->assignment_ops().end());
  }
  // Emit code for 'single' region along with 'copyprivate' clauses
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    Action.Enter(CGF);
    ACCPrivateScope SingleScope(CGF);
    (void)CGF.EmitACCFirstprivateClause(S, SingleScope);
    CGF.EmitACCPrivateClause(S, SingleScope);
    (void)SingleScope.Privatize();
    CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
  };
  {
    ACCLexicalScope Scope(*this, S, ACCD_unknown);
    CGM.getOpenACCRuntime().emitSingleRegion(*this, CodeGen, S.getLocStart(),
                                            CopyprivateVars, DestExprs,
                                            SrcExprs, AssignmentOps);
  }
  // Emit an implicit barrier at the end (to avoid data race on firstprivate
  // init or if no 'nowait' clause was specified and no 'copyprivate' clause).
  if (!S.getSingleClause<ACCNowaitClause>() && CopyprivateVars.empty()) {
    CGM.getOpenACCRuntime().emitBarrierCall(
        *this, S.getLocStart(),
        S.getSingleClause<ACCNowaitClause>() ? ACCD_unknown : ACCD_single);
  }
}

void CodeGenFunction::EmitACCMasterDirective(const ACCMasterDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    Action.Enter(CGF);
    CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitMasterRegion(*this, CodeGen, S.getLocStart());
}

void CodeGenFunction::EmitACCCriticalDirective(const ACCCriticalDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    Action.Enter(CGF);
    CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
  };
  Expr *Hint = nullptr;
  if (auto *HintClause = S.getSingleClause<ACCHintClause>())
    Hint = HintClause->getHint();
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitCriticalRegion(*this,
                                            S.getDirectiveName().getAsString(),
                                            CodeGen, S.getLocStart(), Hint);
}

void CodeGenFunction::EmitACCParallelLoopDirective(
    const ACCParallelLoopDirective &S) {
  llvm::outs() << "I am generating an OpenACC Parallel Loop code\n";
  // Emit directive as a combined directive that consists of two implicit
  // directives: 'parallel' with 'for' directive.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    ACCCancelStackRAII CancelRegion(CGF, ACCD_parallel_loop, S.hasCancel());
    CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(), emitForLoopBounds,
                               emitDispatchForLoopBounds);
  };
  emitCommonACCParallelDirective(*this, S, ACCD_loop, CodeGen,
                                 emitEmptyBoundParameters);
}

void CodeGenFunction::EmitACCParallelLoopVectorDirective(
    const ACCParallelLoopVectorDirective &S) {
  // Emit directive as a combined directive that consists of two implicit
  // directives: 'parallel' with 'for' directive.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(), emitForLoopBounds,
                               emitDispatchForLoopBounds);
  };
  emitCommonACCParallelDirective(*this, S, ACCD_vector, CodeGen,
                                 emitEmptyBoundParameters);
}

void CodeGenFunction::EmitACCParallelSectionsDirective(
    const ACCParallelSectionsDirective &S) {
  // Emit directive as a combined directive that consists of two implicit
  // directives: 'parallel' with 'sections' directive.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitSections(S);
  };
  emitCommonACCParallelDirective(*this, S, ACCD_sections, CodeGen,
                                 emitEmptyBoundParameters);
}

void CodeGenFunction::EmitACCTaskBasedDirective(
    const ACCExecutableDirective &S, const OpenACCDirectiveKind CapturedRegion,
    const ACCRegionCodeGenTy &BodyGen, const ACCTaskGenTy &TaskGen,
    ACCTaskDataTy &Data) {
  // Emit outlined function for task construct.
  const CapturedStmt *CS = S.getCapturedStmt(CapturedRegion);
  auto *I = CS->getCapturedDecl()->param_begin();
  auto *PartId = std::next(I);
  auto *TaskT = std::next(I, 4);
  // Check if the task is final
  if (const auto *Clause = S.getSingleClause<ACCFinalClause>()) {
    // If the condition constant folds and can be elided, try to avoid emitting
    // the condition and the dead arm of the if/else.
    auto *Cond = Clause->getCondition();
    bool CondConstant;
    if (ConstantFoldsToSimpleInteger(Cond, CondConstant))
      Data.Final.setInt(CondConstant);
    else
      Data.Final.setPointer(EvaluateExprAsBool(Cond));
  } else {
    // By default the task is not final.
    Data.Final.setInt(/*IntVal=*/false);
  }
  // Check if the task has 'priority' clause.
  if (const auto *Clause = S.getSingleClause<ACCPriorityClause>()) {
    auto *Prio = Clause->getPriority();
    Data.Priority.setInt(/*IntVal=*/true);
    Data.Priority.setPointer(EmitScalarConversion(
        EmitScalarExpr(Prio), Prio->getType(),
        getContext().getIntTypeForBitwidth(/*DestWidth=*/32, /*Signed=*/1),
        Prio->getExprLoc()));
  }
  // The first function argument for tasks is a thread id, the second one is a
  // part id (0 for tied tasks, >=0 for untied task).
  llvm::DenseSet<const VarDecl *> EmittedAsPrivate;
  // Get list of private variables.
  for (const auto *C : S.getClausesOfKind<ACCPrivateClause>()) {
    auto IRef = C->varlist_begin();
    for (auto *IInit : C->private_copies()) {
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      if (EmittedAsPrivate.insert(OrigVD->getCanonicalDecl()).second) {
        Data.PrivateVars.push_back(*IRef);
        Data.PrivateCopies.push_back(IInit);
      }
      ++IRef;
    }
  }
  EmittedAsPrivate.clear();
  // Get list of firstprivate variables.
  for (const auto *C : S.getClausesOfKind<ACCFirstprivateClause>()) {
    auto IRef = C->varlist_begin();
    auto IElemInitRef = C->inits().begin();
    for (auto *IInit : C->private_copies()) {
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      if (EmittedAsPrivate.insert(OrigVD->getCanonicalDecl()).second) {
        Data.FirstprivateVars.push_back(*IRef);
        Data.FirstprivateCopies.push_back(IInit);
        Data.FirstprivateInits.push_back(*IElemInitRef);
      }
      ++IRef;
      ++IElemInitRef;
    }
  }
  // Get list of lastprivate variables (for taskloops).
  llvm::DenseMap<const VarDecl *, const DeclRefExpr *> LastprivateDstsOrigs;
  for (const auto *C : S.getClausesOfKind<ACCLastprivateClause>()) {
    auto IRef = C->varlist_begin();
    auto ID = C->destination_exprs().begin();
    for (auto *IInit : C->private_copies()) {
      auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*IRef)->getDecl());
      if (EmittedAsPrivate.insert(OrigVD->getCanonicalDecl()).second) {
        Data.LastprivateVars.push_back(*IRef);
        Data.LastprivateCopies.push_back(IInit);
      }
      LastprivateDstsOrigs.insert(
          {cast<VarDecl>(cast<DeclRefExpr>(*ID)->getDecl()),
           cast<DeclRefExpr>(*IRef)});
      ++IRef;
      ++ID;
    }
  }
  SmallVector<const Expr *, 4> LHSs;
  SmallVector<const Expr *, 4> RHSs;
  for (const auto *C : S.getClausesOfKind<ACCReductionClause>()) {
    auto IPriv = C->privates().begin();
    auto IRed = C->reduction_ops().begin();
    auto ILHS = C->lhs_exprs().begin();
    auto IRHS = C->rhs_exprs().begin();
    for (const auto *Ref : C->varlists()) {
      Data.ReductionVars.emplace_back(Ref);
      Data.ReductionCopies.emplace_back(*IPriv);
      Data.ReductionOps.emplace_back(*IRed);
      LHSs.emplace_back(*ILHS);
      RHSs.emplace_back(*IRHS);
      std::advance(IPriv, 1);
      std::advance(IRed, 1);
      std::advance(ILHS, 1);
      std::advance(IRHS, 1);
    }
  }
  Data.Reductions = CGM.getOpenACCRuntime().emitTaskReductionInit(
      *this, S.getLocStart(), LHSs, RHSs, Data);
  // Build list of dependences.
  for (const auto *C : S.getClausesOfKind<ACCDependClause>())
    for (auto *IRef : C->varlists())
      Data.Dependences.push_back(std::make_pair(C->getDependencyKind(), IRef));
  auto &&CodeGen = [&Data, &S, CS, &BodyGen, &LastprivateDstsOrigs,
                    CapturedRegion](CodeGenFunction &CGF,
                                    ACCPrePostActionTy &Action) {
    // Set proper addresses for generated private copies.
    ACCPrivateScope Scope(CGF);
    if (!Data.PrivateVars.empty() || !Data.FirstprivateVars.empty() ||
        !Data.LastprivateVars.empty()) {
      enum { PrivatesParam = 2, CopyFnParam = 3 };
      auto *CopyFn = CGF.Builder.CreateLoad(
          CGF.GetAddrOfLocalVar(CS->getCapturedDecl()->getParam(3)));
      auto *PrivatesPtr = CGF.Builder.CreateLoad(
          CGF.GetAddrOfLocalVar(CS->getCapturedDecl()->getParam(2)));
      // Map privates.
      llvm::SmallVector<std::pair<const VarDecl *, Address>, 16> PrivatePtrs;
      llvm::SmallVector<llvm::Value *, 16> CallArgs;
      CallArgs.push_back(PrivatesPtr);
      for (auto *E : Data.PrivateVars) {
        auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
        Address PrivatePtr = CGF.CreateMemTemp(
            CGF.getContext().getPointerType(E->getType()), ".priv.ptr.addr");
        PrivatePtrs.push_back(std::make_pair(VD, PrivatePtr));
        CallArgs.push_back(PrivatePtr.getPointer());
      }
      for (auto *E : Data.FirstprivateVars) {
        auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
        Address PrivatePtr =
            CGF.CreateMemTemp(CGF.getContext().getPointerType(E->getType()),
                              ".firstpriv.ptr.addr");
        PrivatePtrs.push_back(std::make_pair(VD, PrivatePtr));
        CallArgs.push_back(PrivatePtr.getPointer());
      }
      for (auto *E : Data.LastprivateVars) {
        auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
        Address PrivatePtr =
            CGF.CreateMemTemp(CGF.getContext().getPointerType(E->getType()),
                              ".lastpriv.ptr.addr");
        PrivatePtrs.push_back(std::make_pair(VD, PrivatePtr));
        CallArgs.push_back(PrivatePtr.getPointer());
      }
      CGF.CGM.getOpenACCRuntime().emitOutlinedFunctionCall(CGF, S.getLocStart(),
                                                          CopyFn, CallArgs);
      for (auto &&Pair : LastprivateDstsOrigs) {
        auto *OrigVD = cast<VarDecl>(Pair.second->getDecl());
        DeclRefExpr DRE(
            const_cast<VarDecl *>(OrigVD),
            /*RefersToEnclosingVariableOrCapture=*/CGF.CapturedStmtInfo->lookup(
                OrigVD) != nullptr,
            Pair.second->getType(), VK_LValue, Pair.second->getExprLoc());
        Scope.addPrivate(Pair.first, [&CGF, &DRE]() {
          return CGF.EmitLValue(&DRE).getAddress();
        });
      }
      for (auto &&Pair : PrivatePtrs) {
        Address Replacement(CGF.Builder.CreateLoad(Pair.second),
                            CGF.getContext().getDeclAlign(Pair.first));
        Scope.addPrivate(Pair.first, [Replacement]() { return Replacement; });
      }
    }
    if (Data.Reductions) {
      ACCLexicalScope LexScope(CGF, S, CapturedRegion);
      ACCReductionCodeGen RedCG(Data.ReductionVars, Data.ReductionCopies,
                             Data.ReductionOps);
      llvm::Value *ReductionsPtr = CGF.Builder.CreateLoad(
          CGF.GetAddrOfLocalVar(CS->getCapturedDecl()->getParam(9)));
      for (unsigned Cnt = 0, E = Data.ReductionVars.size(); Cnt < E; ++Cnt) {
        RedCG.emitSharedLValue(CGF, Cnt);
        RedCG.emitAggregateType(CGF, Cnt);
        Address Replacement = CGF.CGM.getOpenACCRuntime().getTaskReductionItem(
            CGF, S.getLocStart(), ReductionsPtr, RedCG.getSharedLValue(Cnt));
        Replacement =
            Address(CGF.EmitScalarConversion(
                        Replacement.getPointer(), CGF.getContext().VoidPtrTy,
                        CGF.getContext().getPointerType(
                            Data.ReductionCopies[Cnt]->getType()),
                        Data.ReductionCopies[Cnt]->getExprLoc()),
                    Replacement.getAlignment());
        Replacement = RedCG.adjustPrivateAddress(CGF, Cnt, Replacement);
        Scope.addPrivate(RedCG.getBaseDecl(Cnt),
                         [Replacement]() { return Replacement; });
        // FIXME: This must removed once the runtime library is fixed.
        // Emit required threadprivate variables for
        // initilizer/combiner/finalizer.
        CGF.CGM.getOpenACCRuntime().emitTaskReductionFixups(CGF, S.getLocStart(),
                                                           RedCG, Cnt);
      }
    }
    // Privatize all private variables except for in_reduction items.
    (void)Scope.Privatize();
    SmallVector<const Expr *, 4> InRedVars;
    SmallVector<const Expr *, 4> InRedPrivs;
    SmallVector<const Expr *, 4> InRedOps;
    SmallVector<const Expr *, 4> TaskgroupDescriptors;
    for (const auto *C : S.getClausesOfKind<ACCInReductionClause>()) {
      auto IPriv = C->privates().begin();
      auto IRed = C->reduction_ops().begin();
      auto ITD = C->taskgroup_descriptors().begin();
      for (const auto *Ref : C->varlists()) {
        InRedVars.emplace_back(Ref);
        InRedPrivs.emplace_back(*IPriv);
        InRedOps.emplace_back(*IRed);
        TaskgroupDescriptors.emplace_back(*ITD);
        std::advance(IPriv, 1);
        std::advance(IRed, 1);
        std::advance(ITD, 1);
      }
    }
    // Privatize in_reduction items here, because taskgroup descriptors must be
    // privatized earlier.
    ACCPrivateScope InRedScope(CGF);
    if (!InRedVars.empty()) {
      ACCReductionCodeGen RedCG(InRedVars, InRedPrivs, InRedOps);
      for (unsigned Cnt = 0, E = InRedVars.size(); Cnt < E; ++Cnt) {
        RedCG.emitSharedLValue(CGF, Cnt);
        RedCG.emitAggregateType(CGF, Cnt);
        // The taskgroup descriptor variable is always implicit firstprivate and
        // privatized already during procoessing of the firstprivates.
        llvm::Value *ReductionsPtr =
            CGF.EmitLoadOfScalar(CGF.EmitLValue(TaskgroupDescriptors[Cnt]),
                                 TaskgroupDescriptors[Cnt]->getExprLoc());
        Address Replacement = CGF.CGM.getOpenACCRuntime().getTaskReductionItem(
            CGF, S.getLocStart(), ReductionsPtr, RedCG.getSharedLValue(Cnt));
        Replacement = Address(
            CGF.EmitScalarConversion(
                Replacement.getPointer(), CGF.getContext().VoidPtrTy,
                CGF.getContext().getPointerType(InRedPrivs[Cnt]->getType()),
                InRedPrivs[Cnt]->getExprLoc()),
            Replacement.getAlignment());
        Replacement = RedCG.adjustPrivateAddress(CGF, Cnt, Replacement);
        InRedScope.addPrivate(RedCG.getBaseDecl(Cnt),
                              [Replacement]() { return Replacement; });
        // FIXME: This must removed once the runtime library is fixed.
        // Emit required threadprivate variables for
        // initilizer/combiner/finalizer.
        CGF.CGM.getOpenACCRuntime().emitTaskReductionFixups(CGF, S.getLocStart(),
                                                           RedCG, Cnt);
      }
    }
    (void)InRedScope.Privatize();

    Action.Enter(CGF);
    BodyGen(CGF);
  };
  auto *OutlinedFn = CGM.getOpenACCRuntime().emitTaskOutlinedFunction(
      S, *I, *PartId, *TaskT, S.getDirectiveKind(), CodeGen, Data.Tied,
      Data.NumberOfParts);
  ACCLexicalScope Scope(*this, S);
  TaskGen(*this, OutlinedFn, Data);
}

static ImplicitParamDecl *
createImplicitFirstprivateForType(ASTContext &C, ACCTaskDataTy &Data,
                                  QualType Ty, CapturedDecl *CD,
                                  SourceLocation Loc) {
  auto *OrigVD = ImplicitParamDecl::Create(C, CD, Loc, /*Id=*/nullptr, Ty,
                                           ImplicitParamDecl::Other);
  auto *OrigRef = DeclRefExpr::Create(
      C, NestedNameSpecifierLoc(), SourceLocation(), OrigVD,
      /*RefersToEnclosingVariableOrCapture=*/false, Loc, Ty, VK_LValue);
  auto *PrivateVD = ImplicitParamDecl::Create(C, CD, Loc, /*Id=*/nullptr, Ty,
                                              ImplicitParamDecl::Other);
  auto *PrivateRef = DeclRefExpr::Create(
      C, NestedNameSpecifierLoc(), SourceLocation(), PrivateVD,
      /*RefersToEnclosingVariableOrCapture=*/false, Loc, Ty, VK_LValue);
  QualType ElemType = C.getBaseElementType(Ty);
  auto *InitVD = ImplicitParamDecl::Create(C, CD, Loc, /*Id=*/nullptr, ElemType,
                                           ImplicitParamDecl::Other);
  auto *InitRef = DeclRefExpr::Create(
      C, NestedNameSpecifierLoc(), SourceLocation(), InitVD,
      /*RefersToEnclosingVariableOrCapture=*/false, Loc, ElemType, VK_LValue);
  PrivateVD->setInitStyle(VarDecl::CInit);
  PrivateVD->setInit(ImplicitCastExpr::Create(C, ElemType, CK_LValueToRValue,
                                              InitRef, /*BasePath=*/nullptr,
                                              VK_RValue));
  Data.FirstprivateVars.emplace_back(OrigRef);
  Data.FirstprivateCopies.emplace_back(PrivateRef);
  Data.FirstprivateInits.emplace_back(InitRef);
  return OrigVD;
}

void CodeGenFunction::EmitACCTargetTaskBasedDirective(
    const ACCExecutableDirective &S, const ACCRegionCodeGenTy &BodyGen,
    ACCDataInfo &InputInfo) {
  // Emit outlined function for task construct.
  auto CS = S.getCapturedStmt(ACCD_task);
  auto CapturedStruct = GenerateCapturedStmtArgument(*CS);
  auto SharedsTy = getContext().getRecordType(CS->getCapturedRecordDecl());
  auto *I = CS->getCapturedDecl()->param_begin();
  auto *PartId = std::next(I);
  auto *TaskT = std::next(I, 4);
  ACCTaskDataTy Data;
  // The task is not final.
  Data.Final.setInt(/*IntVal=*/false);
  // Get list of firstprivate variables.
  for (const auto *C : S.getClausesOfKind<ACCFirstprivateClause>()) {
    auto IRef = C->varlist_begin();
    auto IElemInitRef = C->inits().begin();
    for (auto *IInit : C->private_copies()) {
      Data.FirstprivateVars.push_back(*IRef);
      Data.FirstprivateCopies.push_back(IInit);
      Data.FirstprivateInits.push_back(*IElemInitRef);
      ++IRef;
      ++IElemInitRef;
    }
  }
  ACCPrivateScope TargetScope(*this);
  VarDecl *BPVD = nullptr;
  VarDecl *PVD = nullptr;
  VarDecl *SVD = nullptr;
  if (InputInfo.NumberOfTargetItems > 0) {
    auto *CD = CapturedDecl::Create(
        getContext(), getContext().getTranslationUnitDecl(), /*NumParams=*/0);
    llvm::APInt ArrSize(/*numBits=*/32, InputInfo.NumberOfTargetItems);
    QualType BaseAndPointersType = getContext().getConstantArrayType(
        getContext().VoidPtrTy, ArrSize, ArrayType::Normal,
        /*IndexTypeQuals=*/0);
    BPVD = createImplicitFirstprivateForType(
        getContext(), Data, BaseAndPointersType, CD, S.getLocStart());
    PVD = createImplicitFirstprivateForType(
        getContext(), Data, BaseAndPointersType, CD, S.getLocStart());
    QualType SizesType = getContext().getConstantArrayType(
        getContext().getSizeType(), ArrSize, ArrayType::Normal,
        /*IndexTypeQuals=*/0);
    SVD = createImplicitFirstprivateForType(getContext(), Data, SizesType, CD,
                                            S.getLocStart());
    TargetScope.addPrivate(
        BPVD, [&InputInfo]() { return InputInfo.BasePointersArray; });
    TargetScope.addPrivate(PVD,
                           [&InputInfo]() { return InputInfo.PointersArray; });
    TargetScope.addPrivate(SVD,
                           [&InputInfo]() { return InputInfo.SizesArray; });
  }
  (void)TargetScope.Privatize();
  // Build list of dependences.
  for (const auto *C : S.getClausesOfKind<ACCDependClause>())
    for (auto *IRef : C->varlists())
      Data.Dependences.push_back(std::make_pair(C->getDependencyKind(), IRef));
  auto &&CodeGen = [&Data, &S, CS, &BodyGen, BPVD, PVD, SVD,
                    &InputInfo](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    // Set proper addresses for generated private copies.
    ACCPrivateScope Scope(CGF);
    if (!Data.FirstprivateVars.empty()) {
      enum { PrivatesParam = 2, CopyFnParam = 3 };
      auto *CopyFn = CGF.Builder.CreateLoad(
          CGF.GetAddrOfLocalVar(CS->getCapturedDecl()->getParam(3)));
      auto *PrivatesPtr = CGF.Builder.CreateLoad(
          CGF.GetAddrOfLocalVar(CS->getCapturedDecl()->getParam(2)));
      // Map privates.
      llvm::SmallVector<std::pair<const VarDecl *, Address>, 16> PrivatePtrs;
      llvm::SmallVector<llvm::Value *, 16> CallArgs;
      CallArgs.push_back(PrivatesPtr);
      for (auto *E : Data.FirstprivateVars) {
        auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
        Address PrivatePtr =
            CGF.CreateMemTemp(CGF.getContext().getPointerType(E->getType()),
                              ".firstpriv.ptr.addr");
        PrivatePtrs.push_back(std::make_pair(VD, PrivatePtr));
        CallArgs.push_back(PrivatePtr.getPointer());
      }
      CGF.CGM.getOpenACCRuntime().emitOutlinedFunctionCall(CGF, S.getLocStart(),
                                                          CopyFn, CallArgs);
      for (auto &&Pair : PrivatePtrs) {
        Address Replacement(CGF.Builder.CreateLoad(Pair.second),
                            CGF.getContext().getDeclAlign(Pair.first));
        Scope.addPrivate(Pair.first, [Replacement]() { return Replacement; });
      }
    }
    // Privatize all private variables except for in_reduction items.
    (void)Scope.Privatize();
    if (InputInfo.NumberOfTargetItems > 0) {
      InputInfo.BasePointersArray = CGF.Builder.CreateConstArrayGEP(
          CGF.GetAddrOfLocalVar(BPVD), /*Index=*/0, CGF.getPointerSize());
      InputInfo.PointersArray = CGF.Builder.CreateConstArrayGEP(
          CGF.GetAddrOfLocalVar(PVD), /*Index=*/0, CGF.getPointerSize());
      InputInfo.SizesArray = CGF.Builder.CreateConstArrayGEP(
          CGF.GetAddrOfLocalVar(SVD), /*Index=*/0, CGF.getSizeSize());
    }

    Action.Enter(CGF);
    ACCLexicalScope LexScope(CGF, S, ACCD_task, /*EmitPreInitStmt=*/false);
    BodyGen(CGF);
  };
  auto *OutlinedFn = CGM.getOpenACCRuntime().emitTaskOutlinedFunction(
      S, *I, *PartId, *TaskT, S.getDirectiveKind(), CodeGen, /*Tied=*/true,
      Data.NumberOfParts);
  llvm::APInt TrueOrFalse(32, S.hasClausesOfKind<ACCNowaitClause>() ? 1 : 0);
  IntegerLiteral IfCond(getContext(), TrueOrFalse,
                        getContext().getIntTypeForBitwidth(32, /*Signed=*/0),
                        SourceLocation());

  CGM.getOpenACCRuntime().emitTaskCall(*this, S.getLocStart(), S, OutlinedFn,
                                      SharedsTy, CapturedStruct, &IfCond, Data);
}

void CodeGenFunction::EmitACCTaskDirective(const ACCTaskDirective &S) {
  // Emit outlined function for task construct.
  const CapturedStmt *CS = S.getCapturedStmt(ACCD_task);
  auto CapturedStruct = GenerateCapturedStmtArgument(*CS);
  auto SharedsTy = getContext().getRecordType(CS->getCapturedRecordDecl());
  const Expr *IfCond = nullptr;
  for (const auto *C : S.getClausesOfKind<ACCIfClause>()) {
    if (C->getNameModifier() == ACCD_unknown ||
        C->getNameModifier() == ACCD_task) {
      IfCond = C->getCondition();
      break;
    }
  }

  ACCTaskDataTy Data;
  // Check if we should emit tied or untied task.
  Data.Tied = !S.getSingleClause<ACCUntiedClause>();
  auto &&BodyGen = [CS](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitStmt(CS->getCapturedStmt());
  };
  auto &&TaskGen = [&S, SharedsTy, CapturedStruct,
                    IfCond](CodeGenFunction &CGF, llvm::Value *OutlinedFn,
                            const ACCTaskDataTy &Data) {
    CGF.CGM.getOpenACCRuntime().emitTaskCall(CGF, S.getLocStart(), S, OutlinedFn,
                                            SharedsTy, CapturedStruct, IfCond,
                                            Data);
  };
  EmitACCTaskBasedDirective(S, ACCD_task, BodyGen, TaskGen, Data);
}

void CodeGenFunction::EmitACCTaskyieldDirective(
    const ACCTaskyieldDirective &S) {
  CGM.getOpenACCRuntime().emitTaskyieldCall(*this, S.getLocStart());
}

void CodeGenFunction::EmitACCBarrierDirective(const ACCBarrierDirective &S) {
  CGM.getOpenACCRuntime().emitBarrierCall(*this, S.getLocStart(), ACCD_barrier);
}

void CodeGenFunction::EmitACCTaskwaitDirective(const ACCTaskwaitDirective &S) {
  CGM.getOpenACCRuntime().emitTaskwaitCall(*this, S.getLocStart());
}

void CodeGenFunction::EmitACCTaskgroupDirective(
    const ACCTaskgroupDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    Action.Enter(CGF);
    if (const Expr *E = S.getReductionRef()) {
      SmallVector<const Expr *, 4> LHSs;
      SmallVector<const Expr *, 4> RHSs;
      ACCTaskDataTy Data;
      for (const auto *C : S.getClausesOfKind<ACCTaskReductionClause>()) {
        auto IPriv = C->privates().begin();
        auto IRed = C->reduction_ops().begin();
        auto ILHS = C->lhs_exprs().begin();
        auto IRHS = C->rhs_exprs().begin();
        for (const auto *Ref : C->varlists()) {
          Data.ReductionVars.emplace_back(Ref);
          Data.ReductionCopies.emplace_back(*IPriv);
          Data.ReductionOps.emplace_back(*IRed);
          LHSs.emplace_back(*ILHS);
          RHSs.emplace_back(*IRHS);
          std::advance(IPriv, 1);
          std::advance(IRed, 1);
          std::advance(ILHS, 1);
          std::advance(IRHS, 1);
        }
      }
      llvm::Value *ReductionDesc =
          CGF.CGM.getOpenACCRuntime().emitTaskReductionInit(CGF, S.getLocStart(),
                                                           LHSs, RHSs, Data);
      const auto *VD = cast<VarDecl>(cast<DeclRefExpr>(E)->getDecl());
      CGF.EmitVarDecl(*VD);
      CGF.EmitStoreOfScalar(ReductionDesc, CGF.GetAddrOfLocalVar(VD),
                            /*Volatile=*/false, E->getType());
    }
    CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitTaskgroupRegion(*this, CodeGen, S.getLocStart());
}

void CodeGenFunction::EmitACCFlushDirective(const ACCFlushDirective &S) {
  CGM.getOpenACCRuntime().emitFlush(*this, [&]() -> ArrayRef<const Expr *> {
    if (const auto *FlushClause = S.getSingleClause<ACCFlushClause>()) {
      return llvm::makeArrayRef(FlushClause->varlist_begin(),
                                FlushClause->varlist_end());
    }
    return llvm::None;
  }(), S.getLocStart());
}

void CodeGenFunction::EmitACCDistributeLoop(const ACCLoopLikeDirective &S,
                                            const ACCCodeGenLoopTy &CodeGenLoop,
                                            Expr *IncExpr) {
  // Emit the loop iteration variable.
  auto IVExpr = cast<DeclRefExpr>(S.getIterationVariable());
  auto IVDecl = cast<VarDecl>(IVExpr->getDecl());
  EmitVarDecl(*IVDecl);

  // Emit the iterations count variable.
  // If it is not a variable, Sema decided to calculate iterations count on each
  // iteration (e.g., it is foldable into a constant).
  if (auto LIExpr = dyn_cast<DeclRefExpr>(S.getLastIteration())) {
    EmitVarDecl(*cast<VarDecl>(LIExpr->getDecl()));
    // Emit calculation of the iterations count.
    EmitIgnoredExpr(S.getCalcLastIteration());
  }

  auto &RT = CGM.getOpenACCRuntime();

  bool HasLastprivateClause = false;
  // Check pre-condition.
  {
    ACCLoopScope PreInitScope(*this, S);
    // Skip the entire loop if we don't meet the precondition.
    // If the condition constant folds and can be elided, avoid emitting the
    // whole loop.
    bool CondConstant;
    llvm::BasicBlock *ContBlock = nullptr;
    if (ConstantFoldsToSimpleInteger(S.getPreCond(), CondConstant)) {
      if (!CondConstant)
        return;
    } else {
      auto *ThenBlock = createBasicBlock("acc.precond.then");
      ContBlock = createBasicBlock("acc.precond.end");
      emitPreCond(*this, S, S.getPreCond(), ThenBlock, ContBlock,
                  getProfileCount(&S));
      EmitBlock(ThenBlock);
      incrementProfileCounter(&S);
    }

    emitAlignedClause(*this, S);
    // Emit 'then' code.
    {
      // Emit helper vars inits.

      LValue LB = EmitACCHelperVar(
          *this, cast<DeclRefExpr>(
                     (isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                          ? S.getCombinedLowerBoundVariable()
                          : S.getLowerBoundVariable())));
      LValue UB = EmitACCHelperVar(
          *this, cast<DeclRefExpr>(
                     (isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                          ? S.getCombinedUpperBoundVariable()
                          : S.getUpperBoundVariable())));
      LValue ST =
          EmitACCHelperVar(*this, cast<DeclRefExpr>(S.getStrideVariable()));
      LValue IL =
          EmitACCHelperVar(*this, cast<DeclRefExpr>(S.getIsLastIterVariable()));

      ACCPrivateScope LoopScope(*this);
      if (EmitACCFirstprivateClause(S, LoopScope)) {
        // Emit implicit barrier to synchronize threads and avoid data races
        // on initialization of firstprivate variables and post-update of
        // lastprivate variables.
        CGM.getOpenACCRuntime().emitBarrierCall(
            *this, S.getLocStart(), ACCD_unknown, /*EmitChecks=*/false,
            /*ForceSimpleCall=*/true);
      }
      EmitACCPrivateClause(S, LoopScope);
      if (isOpenACCVectorDirective(S.getDirectiveKind()) &&
          !isOpenACCParallelDirective(S.getDirectiveKind()) &&
          !isOpenACCGangDirective(S.getDirectiveKind()))
        EmitACCReductionClauseInit(S, LoopScope);
      HasLastprivateClause = EmitACCLastprivateClauseInit(S, LoopScope);
      EmitACCPrivateLoopCounters(S, LoopScope);
      (void)LoopScope.Privatize();

      // Detect the distribute schedule kind and chunk.
      llvm::Value *Chunk = nullptr;
      OpenACCDistScheduleClauseKind ScheduleKind = ACCC_DIST_SCHEDULE_unknown;
      if (auto *C = S.getSingleClause<ACCDistScheduleClause>()) {
        ScheduleKind = C->getDistScheduleKind();
        if (const auto *Ch = C->getChunkSize()) {
          Chunk = EmitScalarExpr(Ch);
          Chunk = EmitScalarConversion(Chunk, Ch->getType(),
                                       S.getIterationVariable()->getType(),
                                       S.getLocStart());
        }
      }
      const unsigned IVSize = getContext().getTypeSize(IVExpr->getType());
      const bool IVSigned = IVExpr->getType()->hasSignedIntegerRepresentation();

      // OpenACC [2.10.8, distribute Construct, Description]
      // If dist_schedule is specified, kind must be static. If specified,
      // iterations are divided into chunks of size chunk_size, chunks are
      // assigned to the teams of the league in a round-robin fashion in the
      // order of the team number. When no chunk_size is specified, the
      // iteration space is divided into chunks that are approximately equal
      // in size, and at most one chunk is distributed to each team of the
      // league. The size of the chunks is unspecified in this case.
      if (RT.isStaticNonchunked(ScheduleKind,
                                /* Chunked */ Chunk != nullptr)) {
        if (isOpenACCVectorDirective(S.getDirectiveKind()))
          EmitACCVectorInit(S, /*IsMonotonic=*/true);
        CGOpenACCRuntime::StaticRTInput StaticInit(
            IVSize, IVSigned, /* Ordered = */ false, IL.getAddress(),
            LB.getAddress(), UB.getAddress(), ST.getAddress());
        RT.emitDistributeStaticInit(*this, S.getLocStart(), ScheduleKind,
                                    StaticInit);
        auto LoopExit =
            getJumpDestInCurrentScope(createBasicBlock("acc.loop.exit"));
        // UB = min(UB, GlobalUB);
        EmitIgnoredExpr(isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                            ? S.getCombinedEnsureUpperBound()
                            : S.getEnsureUpperBound());
        // IV = LB;
        EmitIgnoredExpr(isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                            ? S.getCombinedInit()
                            : S.getInit());

        Expr *Cond = isOpenACCLoopBoundSharingDirective(S.getDirectiveKind())
                         ? S.getCombinedCond()
                         : S.getCond();

        // for distribute alone,  codegen
        // while (idx <= UB) { BODY; ++idx; }
        // when combined with 'for' (e.g. as in 'distribute parallel for')
        // while (idx <= UB) { <CodeGen rest of pragma>; idx += ST; }
        EmitACCInnerLoop(S, LoopScope.requiresCleanups(), Cond, IncExpr,
                         [&S, LoopExit, &CodeGenLoop](CodeGenFunction &CGF) {
                           CodeGenLoop(CGF, S, LoopExit);
                         },
                         [](CodeGenFunction &) {});
        EmitBlock(LoopExit.getBlock());
        // Tell the runtime we are done.
        RT.emitForStaticFinish(*this, S.getLocStart(), S.getDirectiveKind());
      } else {
        // Emit the outer loop, which requests its work chunk [LB..UB] from
        // runtime and runs the inner loop to process it.
        const ACCLoopArguments LoopArguments = {
            LB.getAddress(), UB.getAddress(), ST.getAddress(), IL.getAddress(),
            Chunk};
        EmitACCDistributeOuterLoop(ScheduleKind, S, LoopScope, LoopArguments,
                                   CodeGenLoop);
      }
      if (isOpenACCVectorDirective(S.getDirectiveKind())) {
        EmitACCVectorFinal(S, [&](CodeGenFunction &CGF) -> llvm::Value * {
          return CGF.Builder.CreateIsNotNull(
              CGF.EmitLoadOfScalar(IL, S.getLocStart()));
        });
      }
      OpenACCDirectiveKind ReductionKind = ACCD_unknown;
      if (isOpenACCParallelDirective(S.getDirectiveKind()) &&
          isOpenACCVectorDirective(S.getDirectiveKind())) {
        ReductionKind = ACCD_parallel_loop_vector;
      } else if (isOpenACCParallelDirective(S.getDirectiveKind())) {
        ReductionKind = ACCD_parallel_loop;
      } else if (isOpenACCVectorDirective(S.getDirectiveKind())) {
        ReductionKind = ACCD_vector;
      } else if (!isOpenACCGangDirective(S.getDirectiveKind()) &&
                 S.hasClausesOfKind<ACCReductionClause>()) {
        llvm_unreachable(
            "No reduction clauses is allowed in distribute directive.");
      }
      EmitACCReductionClauseFinal(S, ReductionKind);
      // Emit post-update of the reduction variables if IsLastIter != 0.
      emitPostUpdateForReductionClause(
          *this, S, [&](CodeGenFunction &CGF) -> llvm::Value * {
            return CGF.Builder.CreateIsNotNull(
                CGF.EmitLoadOfScalar(IL, S.getLocStart()));
          });
      // Emit final copy of the lastprivate variables if IsLastIter != 0.
      if (HasLastprivateClause) {
        EmitACCLastprivateClauseFinal(
            S, /*NoFinals=*/false,
            Builder.CreateIsNotNull(EmitLoadOfScalar(IL, S.getLocStart())));
      }
    }

    // We're now done with the loop, so jump to the continuation block.
    if (ContBlock) {
      EmitBranch(ContBlock);
      EmitBlock(ContBlock, true);
    }
  }
}

void CodeGenFunction::EmitACCDistributeDirective(
    const ACCDistributeDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {

    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_distribute, CodeGen);
}

static llvm::Function *emitOutlinedOrderedFunction(CodeGenModule &CGM,
                                                   const CapturedStmt *S) {
  CodeGenFunction CGF(CGM, /*suppressNewContext=*/true);
  CodeGenFunction::CGCapturedStmtInfo CapStmtInfo;
  CGF.CapturedStmtInfo = &CapStmtInfo;
  auto *Fn = CGF.GenerateOpenACCCapturedStmtFunction(*S);
  Fn->addFnAttr(llvm::Attribute::NoInline);
  return Fn;
}

void CodeGenFunction::EmitACCOrderedDirective(const ACCOrderedDirective &S) {
  if (S.hasClausesOfKind<ACCDependClause>()) {
    assert(!S.getAssociatedStmt() &&
           "No associated statement must be in ordered depend construct.");
    for (const auto *DC : S.getClausesOfKind<ACCDependClause>())
      CGM.getOpenACCRuntime().emitDoacrossOrdered(*this, DC);
    return;
  }
  auto *C = S.getSingleClause<ACCVectorClause>();
  auto &&CodeGen = [&S, C, this](CodeGenFunction &CGF,
                                 ACCPrePostActionTy &Action) {
    const CapturedStmt *CS = S.getInnermostCapturedStmt();
    if (C) {
      llvm::SmallVector<llvm::Value *, 16> CapturedVars;
      CGF.GenerateOpenACCCapturedVars(*CS, CapturedVars);
      auto *OutlinedFn = emitOutlinedOrderedFunction(CGM, CS);
      CGM.getOpenACCRuntime().emitOutlinedFunctionCall(CGF, S.getLocStart(),
                                                      OutlinedFn, CapturedVars);
    } else {
      Action.Enter(CGF);
      CGF.EmitStmt(CS->getCapturedStmt());
    }
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitOrderedRegion(*this, CodeGen, S.getLocStart(), !C);
}

static llvm::Value *convertToScalarValue(CodeGenFunction &CGF, RValue Val,
                                         QualType SrcType, QualType DestType,
                                         SourceLocation Loc) {
  assert(CGF.hasScalarEvaluationKind(DestType) &&
         "DestType must have scalar evaluation kind.");
  assert(!Val.isAggregate() && "Must be a scalar or complex.");
  return Val.isScalar()
             ? CGF.EmitScalarConversion(Val.getScalarVal(), SrcType, DestType,
                                        Loc)
             : CGF.EmitComplexToScalarConversion(Val.getComplexVal(), SrcType,
                                                 DestType, Loc);
}

static CodeGenFunction::ComplexPairTy
convertToComplexValue(CodeGenFunction &CGF, RValue Val, QualType SrcType,
                      QualType DestType, SourceLocation Loc) {
  assert(CGF.getEvaluationKind(DestType) == TEK_Complex &&
         "DestType must have complex evaluation kind.");
  CodeGenFunction::ComplexPairTy ComplexVal;
  if (Val.isScalar()) {
    // Convert the input element to the element type of the complex.
    auto DestElementType = DestType->castAs<ComplexType>()->getElementType();
    auto ScalarVal = CGF.EmitScalarConversion(Val.getScalarVal(), SrcType,
                                              DestElementType, Loc);
    ComplexVal = CodeGenFunction::ComplexPairTy(
        ScalarVal, llvm::Constant::getNullValue(ScalarVal->getType()));
  } else {
    assert(Val.isComplex() && "Must be a scalar or complex.");
    auto SrcElementType = SrcType->castAs<ComplexType>()->getElementType();
    auto DestElementType = DestType->castAs<ComplexType>()->getElementType();
    ComplexVal.first = CGF.EmitScalarConversion(
        Val.getComplexVal().first, SrcElementType, DestElementType, Loc);
    ComplexVal.second = CGF.EmitScalarConversion(
        Val.getComplexVal().second, SrcElementType, DestElementType, Loc);
  }
  return ComplexVal;
}

static void emitSimpleAtomicStore(CodeGenFunction &CGF, bool IsSeqCst,
                                  LValue LVal, RValue RVal) {
  if (LVal.isGlobalReg()) {
    CGF.EmitStoreThroughGlobalRegLValue(RVal, LVal);
  } else {
    CGF.EmitAtomicStore(RVal, LVal,
                        IsSeqCst ? llvm::AtomicOrdering::SequentiallyConsistent
                                 : llvm::AtomicOrdering::Monotonic,
                        LVal.isVolatile(), /*IsInit=*/false);
  }
}

void CodeGenFunction::emitACCSimpleStore(LValue LVal, RValue RVal,
                                         QualType RValTy, SourceLocation Loc) {
  switch (getEvaluationKind(LVal.getType())) {
  case TEK_Scalar:
    EmitStoreThroughLValue(RValue::get(convertToScalarValue(
                               *this, RVal, RValTy, LVal.getType(), Loc)),
                           LVal);
    break;
  case TEK_Complex:
    EmitStoreOfComplex(
        convertToComplexValue(*this, RVal, RValTy, LVal.getType(), Loc), LVal,
        /*isInit=*/false);
    break;
  case TEK_Aggregate:
    llvm_unreachable("Must be a scalar or complex.");
  }
}

static void EmitACCAtomicReadExpr(CodeGenFunction &CGF, bool IsSeqCst,
                                  const Expr *X, const Expr *V,
                                  SourceLocation Loc) {
  // v = x;
  assert(V->isLValue() && "V of 'acc atomic read' is not lvalue");
  assert(X->isLValue() && "X of 'acc atomic read' is not lvalue");
  LValue XLValue = CGF.EmitLValue(X);
  LValue VLValue = CGF.EmitLValue(V);
  RValue Res = XLValue.isGlobalReg()
                   ? CGF.EmitLoadOfLValue(XLValue, Loc)
                   : CGF.EmitAtomicLoad(
                         XLValue, Loc,
                         IsSeqCst ? llvm::AtomicOrdering::SequentiallyConsistent
                                  : llvm::AtomicOrdering::Monotonic,
                         XLValue.isVolatile());
  // OpenACC, 2.12.6, atomic Construct
  // Any atomic construct with a seq_cst clause forces the atomically
  // performed operation to include an implicit flush operation without a
  // list.
  if (IsSeqCst)
    CGF.CGM.getOpenACCRuntime().emitFlush(CGF, llvm::None, Loc);
  CGF.emitACCSimpleStore(VLValue, Res, X->getType().getNonReferenceType(), Loc);
}

static void EmitACCAtomicWriteExpr(CodeGenFunction &CGF, bool IsSeqCst,
                                   const Expr *X, const Expr *E,
                                   SourceLocation Loc) {
  // x = expr;
  assert(X->isLValue() && "X of 'acc atomic write' is not lvalue");
  emitSimpleAtomicStore(CGF, IsSeqCst, CGF.EmitLValue(X), CGF.EmitAnyExpr(E));
  // OpenACC, 2.12.6, atomic Construct
  // Any atomic construct with a seq_cst clause forces the atomically
  // performed operation to include an implicit flush operation without a
  // list.
  if (IsSeqCst)
    CGF.CGM.getOpenACCRuntime().emitFlush(CGF, llvm::None, Loc);
}

static std::pair<bool, RValue> emitACCAtomicRMW(CodeGenFunction &CGF, LValue X,
                                                RValue Update,
                                                BinaryOperatorKind BO,
                                                llvm::AtomicOrdering AO,
                                                bool IsXLHSInRHSPart) {
  auto &Context = CGF.CGM.getContext();
  // Allow atomicrmw only if 'x' and 'update' are integer values, lvalue for 'x'
  // expression is simple and atomic is allowed for the given type for the
  // target platform.
  if (BO == BO_Comma || !Update.isScalar() ||
      !Update.getScalarVal()->getType()->isIntegerTy() ||
      !X.isSimple() || (!isa<llvm::ConstantInt>(Update.getScalarVal()) &&
                        (Update.getScalarVal()->getType() !=
                         X.getAddress().getElementType())) ||
      !X.getAddress().getElementType()->isIntegerTy() ||
      !Context.getTargetInfo().hasBuiltinAtomic(
          Context.getTypeSize(X.getType()), Context.toBits(X.getAlignment())))
    return std::make_pair(false, RValue::get(nullptr));

  llvm::AtomicRMWInst::BinOp RMWOp;
  switch (BO) {
  case BO_Add:
    RMWOp = llvm::AtomicRMWInst::Add;
    break;
  case BO_Sub:
    if (!IsXLHSInRHSPart)
      return std::make_pair(false, RValue::get(nullptr));
    RMWOp = llvm::AtomicRMWInst::Sub;
    break;
  case BO_And:
    RMWOp = llvm::AtomicRMWInst::And;
    break;
  case BO_Or:
    RMWOp = llvm::AtomicRMWInst::Or;
    break;
  case BO_Xor:
    RMWOp = llvm::AtomicRMWInst::Xor;
    break;
  case BO_LT:
    RMWOp = X.getType()->hasSignedIntegerRepresentation()
                ? (IsXLHSInRHSPart ? llvm::AtomicRMWInst::Min
                                   : llvm::AtomicRMWInst::Max)
                : (IsXLHSInRHSPart ? llvm::AtomicRMWInst::UMin
                                   : llvm::AtomicRMWInst::UMax);
    break;
  case BO_GT:
    RMWOp = X.getType()->hasSignedIntegerRepresentation()
                ? (IsXLHSInRHSPart ? llvm::AtomicRMWInst::Max
                                   : llvm::AtomicRMWInst::Min)
                : (IsXLHSInRHSPart ? llvm::AtomicRMWInst::UMax
                                   : llvm::AtomicRMWInst::UMin);
    break;
  case BO_Assign:
    RMWOp = llvm::AtomicRMWInst::Xchg;
    break;
  case BO_Mul:
  case BO_Div:
  case BO_Rem:
  case BO_Shl:
  case BO_Shr:
  case BO_LAnd:
  case BO_LOr:
    return std::make_pair(false, RValue::get(nullptr));
  case BO_PtrMemD:
  case BO_PtrMemI:
  case BO_LE:
  case BO_GE:
  case BO_EQ:
  case BO_NE:
  case BO_Cmp:
  case BO_AddAssign:
  case BO_SubAssign:
  case BO_AndAssign:
  case BO_OrAssign:
  case BO_XorAssign:
  case BO_MulAssign:
  case BO_DivAssign:
  case BO_RemAssign:
  case BO_ShlAssign:
  case BO_ShrAssign:
  case BO_Comma:
    llvm_unreachable("Unsupported atomic update operation");
  }
  auto *UpdateVal = Update.getScalarVal();
  if (auto *IC = dyn_cast<llvm::ConstantInt>(UpdateVal)) {
    UpdateVal = CGF.Builder.CreateIntCast(
        IC, X.getAddress().getElementType(),
        X.getType()->hasSignedIntegerRepresentation());
  }
  auto *Res = CGF.Builder.CreateAtomicRMW(RMWOp, X.getPointer(), UpdateVal, AO);
  return std::make_pair(true, RValue::get(Res));
}

std::pair<bool, RValue> CodeGenFunction::EmitACCAtomicSimpleUpdateExpr(
    LValue X, RValue E, BinaryOperatorKind BO, bool IsXLHSInRHSPart,
    llvm::AtomicOrdering AO, SourceLocation Loc,
    const llvm::function_ref<RValue(RValue)> &CommonGen) {
  // Update expressions are allowed to have the following forms:
  // x binop= expr; -> xrval + expr;
  // x++, ++x -> xrval + 1;
  // x--, --x -> xrval - 1;
  // x = x binop expr; -> xrval binop expr
  // x = expr Op x; - > expr binop xrval;
  auto Res = emitACCAtomicRMW(*this, X, E, BO, AO, IsXLHSInRHSPart);
  if (!Res.first) {
    if (X.isGlobalReg()) {
      // Emit an update expression: 'xrval' binop 'expr' or 'expr' binop
      // 'xrval'.
      EmitStoreThroughLValue(CommonGen(EmitLoadOfLValue(X, Loc)), X);
    } else {
      // Perform compare-and-swap procedure.
      EmitAtomicUpdate(X, AO, CommonGen, X.getType().isVolatileQualified());
    }
  }
  return Res;
}

static void EmitACCAtomicUpdateExpr(CodeGenFunction &CGF, bool IsSeqCst,
                                    const Expr *X, const Expr *E,
                                    const Expr *UE, bool IsXLHSInRHSPart,
                                    SourceLocation Loc) {
  assert(isa<BinaryOperator>(UE->IgnoreImpCasts()) &&
         "Update expr in 'atomic update' must be a binary operator.");
  auto *BOUE = cast<BinaryOperator>(UE->IgnoreImpCasts());
  // Update expressions are allowed to have the following forms:
  // x binop= expr; -> xrval + expr;
  // x++, ++x -> xrval + 1;
  // x--, --x -> xrval - 1;
  // x = x binop expr; -> xrval binop expr
  // x = expr Op x; - > expr binop xrval;
  assert(X->isLValue() && "X of 'acc atomic update' is not lvalue");
  LValue XLValue = CGF.EmitLValue(X);
  RValue ExprRValue = CGF.EmitAnyExpr(E);
  auto AO = IsSeqCst ? llvm::AtomicOrdering::SequentiallyConsistent
                     : llvm::AtomicOrdering::Monotonic;
  auto *LHS = cast<OpaqueValueExpr>(BOUE->getLHS()->IgnoreImpCasts());
  auto *RHS = cast<OpaqueValueExpr>(BOUE->getRHS()->IgnoreImpCasts());
  auto *XRValExpr = IsXLHSInRHSPart ? LHS : RHS;
  auto *ERValExpr = IsXLHSInRHSPart ? RHS : LHS;
  auto Gen =
      [&CGF, UE, ExprRValue, XRValExpr, ERValExpr](RValue XRValue) -> RValue {
        CodeGenFunction::OpaqueValueMapping MapExpr(CGF, ERValExpr, ExprRValue);
        CodeGenFunction::OpaqueValueMapping MapX(CGF, XRValExpr, XRValue);
        return CGF.EmitAnyExpr(UE);
      };
  (void)CGF.EmitACCAtomicSimpleUpdateExpr(
      XLValue, ExprRValue, BOUE->getOpcode(), IsXLHSInRHSPart, AO, Loc, Gen);
  // OpenACC, 2.12.6, atomic Construct
  // Any atomic construct with a seq_cst clause forces the atomically
  // performed operation to include an implicit flush operation without a
  // list.
  if (IsSeqCst)
    CGF.CGM.getOpenACCRuntime().emitFlush(CGF, llvm::None, Loc);
}

static RValue convertToType(CodeGenFunction &CGF, RValue Value,
                            QualType SourceType, QualType ResType,
                            SourceLocation Loc) {
  switch (CGF.getEvaluationKind(ResType)) {
  case TEK_Scalar:
    return RValue::get(
        convertToScalarValue(CGF, Value, SourceType, ResType, Loc));
  case TEK_Complex: {
    auto Res = convertToComplexValue(CGF, Value, SourceType, ResType, Loc);
    return RValue::getComplex(Res.first, Res.second);
  }
  case TEK_Aggregate:
    break;
  }
  llvm_unreachable("Must be a scalar or complex.");
}

static void EmitACCAtomicCaptureExpr(CodeGenFunction &CGF, bool IsSeqCst,
                                     bool IsPostfixUpdate, const Expr *V,
                                     const Expr *X, const Expr *E,
                                     const Expr *UE, bool IsXLHSInRHSPart,
                                     SourceLocation Loc) {
  assert(X->isLValue() && "X of 'acc atomic capture' is not lvalue");
  assert(V->isLValue() && "V of 'acc atomic capture' is not lvalue");
  RValue NewVVal;
  LValue VLValue = CGF.EmitLValue(V);
  LValue XLValue = CGF.EmitLValue(X);
  RValue ExprRValue = CGF.EmitAnyExpr(E);
  auto AO = IsSeqCst ? llvm::AtomicOrdering::SequentiallyConsistent
                     : llvm::AtomicOrdering::Monotonic;
  QualType NewVValType;
  if (UE) {
    // 'x' is updated with some additional value.
    assert(isa<BinaryOperator>(UE->IgnoreImpCasts()) &&
           "Update expr in 'atomic capture' must be a binary operator.");
    auto *BOUE = cast<BinaryOperator>(UE->IgnoreImpCasts());
    // Update expressions are allowed to have the following forms:
    // x binop= expr; -> xrval + expr;
    // x++, ++x -> xrval + 1;
    // x--, --x -> xrval - 1;
    // x = x binop expr; -> xrval binop expr
    // x = expr Op x; - > expr binop xrval;
    auto *LHS = cast<OpaqueValueExpr>(BOUE->getLHS()->IgnoreImpCasts());
    auto *RHS = cast<OpaqueValueExpr>(BOUE->getRHS()->IgnoreImpCasts());
    auto *XRValExpr = IsXLHSInRHSPart ? LHS : RHS;
    NewVValType = XRValExpr->getType();
    auto *ERValExpr = IsXLHSInRHSPart ? RHS : LHS;
    auto &&Gen = [&CGF, &NewVVal, UE, ExprRValue, XRValExpr, ERValExpr,
                  IsPostfixUpdate](RValue XRValue) -> RValue {
      CodeGenFunction::OpaqueValueMapping MapExpr(CGF, ERValExpr, ExprRValue);
      CodeGenFunction::OpaqueValueMapping MapX(CGF, XRValExpr, XRValue);
      RValue Res = CGF.EmitAnyExpr(UE);
      NewVVal = IsPostfixUpdate ? XRValue : Res;
      return Res;
    };
    auto Res = CGF.EmitACCAtomicSimpleUpdateExpr(
        XLValue, ExprRValue, BOUE->getOpcode(), IsXLHSInRHSPart, AO, Loc, Gen);
    if (Res.first) {
      // 'atomicrmw' instruction was generated.
      if (IsPostfixUpdate) {
        // Use old value from 'atomicrmw'.
        NewVVal = Res.second;
      } else {
        // 'atomicrmw' does not provide new value, so evaluate it using old
        // value of 'x'.
        CodeGenFunction::OpaqueValueMapping MapExpr(CGF, ERValExpr, ExprRValue);
        CodeGenFunction::OpaqueValueMapping MapX(CGF, XRValExpr, Res.second);
        NewVVal = CGF.EmitAnyExpr(UE);
      }
    }
  } else {
    // 'x' is simply rewritten with some 'expr'.
    NewVValType = X->getType().getNonReferenceType();
    ExprRValue = convertToType(CGF, ExprRValue, E->getType(),
                               X->getType().getNonReferenceType(), Loc);
    auto &&Gen = [&NewVVal, ExprRValue](RValue XRValue) -> RValue {
      NewVVal = XRValue;
      return ExprRValue;
    };
    // Try to perform atomicrmw xchg, otherwise simple exchange.
    auto Res = CGF.EmitACCAtomicSimpleUpdateExpr(
        XLValue, ExprRValue, /*BO=*/BO_Assign, /*IsXLHSInRHSPart=*/false, AO,
        Loc, Gen);
    if (Res.first) {
      // 'atomicrmw' instruction was generated.
      NewVVal = IsPostfixUpdate ? Res.second : ExprRValue;
    }
  }
  // Emit post-update store to 'v' of old/new 'x' value.
  CGF.emitACCSimpleStore(VLValue, NewVVal, NewVValType, Loc);
  // OpenACC, 2.12.6, atomic Construct
  // Any atomic construct with a seq_cst clause forces the atomically
  // performed operation to include an implicit flush operation without a
  // list.
  if (IsSeqCst)
    CGF.CGM.getOpenACCRuntime().emitFlush(CGF, llvm::None, Loc);
}

static void EmitACCAtomicExpr(CodeGenFunction &CGF, OpenACCClauseKind Kind,
                              bool IsSeqCst, bool IsPostfixUpdate,
                              const Expr *X, const Expr *V, const Expr *E,
                              const Expr *UE, bool IsXLHSInRHSPart,
                              SourceLocation Loc) {
  switch (Kind) {
  case ACCC_read:
    EmitACCAtomicReadExpr(CGF, IsSeqCst, X, V, Loc);
    break;
  case ACCC_write:
    EmitACCAtomicWriteExpr(CGF, IsSeqCst, X, E, Loc);
    break;
  case ACCC_unknown:
  case ACCC_update:
    EmitACCAtomicUpdateExpr(CGF, IsSeqCst, X, E, UE, IsXLHSInRHSPart, Loc);
    break;
  case ACCC_capture:
    EmitACCAtomicCaptureExpr(CGF, IsSeqCst, IsPostfixUpdate, V, X, E, UE,
                             IsXLHSInRHSPart, Loc);
    break;
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_safelen:
  case ACCC_vectorlen:
  case ACCC_collapse:
  case ACCC_default:
  case ACCC_seq_cst:
  case ACCC_shared:
  case ACCC_linear:
  case ACCC_aligned:
  case ACCC_copyprivate:
  case ACCC_flush:
  case ACCC_proc_bind:
  case ACCC_schedule:
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_threadprivate:
  case ACCC_depend:
  case ACCC_mergeable:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_vector:
  case ACCC_map:
  case ACCC_create:
  case ACCC_copy:
  case ACCC_copyin:
  case ACCC_copyout:
  case ACCC_delete:
  case ACCC_num_gangs:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Clause is not allowed in 'acc atomic'.");
  }
}

void CodeGenFunction::EmitACCAtomicDirective(const ACCAtomicDirective &S) {
  bool IsSeqCst = S.getSingleClause<ACCSeqCstClause>();
  OpenACCClauseKind Kind = ACCC_unknown;
  for (auto *C : S.clauses()) {
    // Find first clause (skip seq_cst clause, if it is first).
    if (C->getClauseKind() != ACCC_seq_cst) {
      Kind = C->getClauseKind();
      break;
    }
  }

  const auto *CS = S.getInnermostCapturedStmt()->IgnoreContainers();
  if (const auto *EWC = dyn_cast<ExprWithCleanups>(CS)) {
    enterFullExpression(EWC);
  }
  // Processing for statements under 'atomic capture'.
  if (const auto *Compound = dyn_cast<CompoundStmt>(CS)) {
    for (const auto *C : Compound->body()) {
      if (const auto *EWC = dyn_cast<ExprWithCleanups>(C)) {
        enterFullExpression(EWC);
      }
    }
  }

  auto &&CodeGen = [&S, Kind, IsSeqCst, CS](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    CGF.EmitStopPoint(CS);
    EmitACCAtomicExpr(CGF, Kind, IsSeqCst, S.isPostfixUpdate(), S.getX(),
                      S.getV(), S.getExpr(), S.getUpdateExpr(),
                      S.isXLHSInRHSPart(), S.getLocStart());
  };
  ACCLexicalScope Scope(*this, S, ACCD_unknown);
  CGM.getOpenACCRuntime().emitInlinedDirective(*this, ACCD_atomic, CodeGen);
}

static void emitCommonACCTargetDirective(CodeGenFunction &CGF,
                                         const ACCExecutableDirective &S,
                                         const ACCRegionCodeGenTy &CodeGen) {
  assert(isOpenACCTargetExecutionDirective(S.getDirectiveKind()));
  CodeGenModule &CGM = CGF.CGM;

  llvm::Function *Fn = nullptr;
  llvm::Constant *FnID = nullptr;

  const Expr *IfCond = nullptr;
  // Check for the at most one if clause associated with the target region.
  for (const auto *C : S.getClausesOfKind<ACCIfClause>()) {
    if (C->getNameModifier() == ACCD_unknown ||
        C->getNameModifier() == ACCD_target) {
      IfCond = C->getCondition();
      break;
    }
  }

  // Check if we have any device clause associated with the directive.
  const Expr *Device = nullptr;
  if (auto *C = S.getSingleClause<ACCDeviceClause>()) {
    Device = C->getDevice();
  }

  // Check if we have an if clause whose conditional always evaluates to false
  // or if we do not have any targets specified. If so the target region is not
  // an offload entry point.
  bool IsOffloadEntry = true;
  if (IfCond) {
    bool Val;
    if (CGF.ConstantFoldsToSimpleInteger(IfCond, Val) && !Val)
      IsOffloadEntry = false;
  }
  if (CGM.getLangOpts().ACCTargetTriples.empty())
    IsOffloadEntry = false;

  assert(CGF.CurFuncDecl && "No parent declaration for target region!");
  StringRef ParentName;
  // In case we have Ctors/Dtors we use the complete type variant to produce
  // the mangling of the device outlined kernel.
  if (auto *D = dyn_cast<CXXConstructorDecl>(CGF.CurFuncDecl))
    ParentName = CGM.getMangledName(GlobalDecl(D, Ctor_Complete));
  else if (auto *D = dyn_cast<CXXDestructorDecl>(CGF.CurFuncDecl))
    ParentName = CGM.getMangledName(GlobalDecl(D, Dtor_Complete));
  else
    ParentName =
        CGM.getMangledName(GlobalDecl(cast<FunctionDecl>(CGF.CurFuncDecl)));

  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(S, ParentName, Fn, FnID,
                                                    IsOffloadEntry, CodeGen);
  ACCLexicalScope Scope(CGF, S, ACCD_task);
  CGM.getOpenACCRuntime().emitTargetCall(CGF, S, Fn, FnID, IfCond, Device);
}

static void emitTargetRegion(CodeGenFunction &CGF, const ACCTargetDirective &S,
                             ACCPrePostActionTy &Action) {
  CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
  (void)CGF.EmitACCFirstprivateClause(S, PrivateScope);
  CGF.EmitACCPrivateClause(S, PrivateScope);
  (void)PrivateScope.Privatize();

  Action.Enter(CGF);
  CGF.EmitStmt(S.getCapturedStmt(ACCD_target)->getCapturedStmt());
}

void CodeGenFunction::EmitACCTargetDeviceFunction(CodeGenModule &CGM,
                                                  StringRef ParentName,
                                                  const ACCTargetDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetDirective(const ACCTargetDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void emitCommonACCGangDirective(CodeGenFunction &CGF,
                                        const ACCExecutableDirective &S,
                                        OpenACCDirectiveKind InnermostKind,
                                        const ACCRegionCodeGenTy &CodeGen) {
  const CapturedStmt *CS = S.getCapturedStmt(ACCD_gang);
  auto OutlinedFn = CGF.CGM.getOpenACCRuntime().emitGangOutlinedFunction(
      S, *CS->getCapturedDecl()->param_begin(), InnermostKind, CodeGen);

  const ACCNumGangsClause *NT = S.getSingleClause<ACCNumGangsClause>();
  const ACCThreadLimitClause *TL = S.getSingleClause<ACCThreadLimitClause>();
  if (NT || TL) {
    Expr *NumGangs = (NT) ? NT->getNumGangs() : nullptr;
    Expr *ThreadLimit = (TL) ? TL->getThreadLimit() : nullptr;

    CGF.CGM.getOpenACCRuntime().emitNumGangsClause(CGF, NumGangs, ThreadLimit,
                                                  S.getLocStart());
  }

  ACCGangScope Scope(CGF, S);
  llvm::SmallVector<llvm::Value *, 16> CapturedVars;
  CGF.GenerateOpenACCCapturedVars(*CS, CapturedVars);
  CGF.CGM.getOpenACCRuntime().emitGangCall(CGF, S, S.getLocStart(), OutlinedFn,
                                           CapturedVars);
}

void CodeGenFunction::EmitACCGangDirective(const ACCGangDirective &S) {
  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
    (void)CGF.EmitACCFirstprivateClause(S, PrivateScope);
    CGF.EmitACCPrivateClause(S, PrivateScope);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.EmitStmt(S.getCapturedStmt(ACCD_gang)->getCapturedStmt());
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(*this, S, ACCD_distribute, CodeGen);
  emitPostUpdateForReductionClause(
      *this, S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
}

static void emitTargetGangRegion(CodeGenFunction &CGF, ACCPrePostActionTy &Action,
                                  const ACCTargetGangDirective &S) {
  auto *CS = S.getCapturedStmt(ACCD_gang);
  Action.Enter(CGF);
  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, CS](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    (void)CGF.EmitACCFirstprivateClause(S, PrivateScope);
    CGF.EmitACCPrivateClause(S, PrivateScope);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    Action.Enter(CGF);
    CGF.EmitStmt(CS->getCapturedStmt());
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(CGF, S, ACCD_gang, CodeGen);
  emitPostUpdateForReductionClause(
      CGF, S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
}

void CodeGenFunction::EmitACCTargetGangDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetGangDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangRegion(CGF, Action, S);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetGangDirective(
    const ACCTargetGangDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangRegion(CGF, Action, S);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void
emitTargetGangDistributeRegion(CodeGenFunction &CGF, ACCPrePostActionTy &Action,
                                const ACCTargetGangDistributeDirective &S) {
  Action.Enter(CGF);
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_distribute,
                                                    CodeGenDistribute);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(CGF, S, ACCD_distribute, CodeGen);
  emitPostUpdateForReductionClause(CGF, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCTargetGangDistributeDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetGangDistributeDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeRegion(CGF, Action, S);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetGangDistributeDirective(
    const ACCTargetGangDistributeDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeRegion(CGF, Action, S);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void emitTargetGangDistributeVectorRegion(
    CodeGenFunction &CGF, ACCPrePostActionTy &Action,
    const ACCTargetGangDistributeVectorDirective &S) {
  Action.Enter(CGF);
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_distribute,
                                                    CodeGenDistribute);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(CGF, S, ACCD_distribute_vector, CodeGen);
  emitPostUpdateForReductionClause(CGF, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCTargetGangDistributeVectorDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetGangDistributeVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeVectorRegion(CGF, Action, S);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetGangDistributeVectorDirective(
    const ACCTargetGangDistributeVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeVectorRegion(CGF, Action, S);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

void CodeGenFunction::EmitACCGangDistributeDirective(
    const ACCGangDistributeDirective &S) {

  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_distribute,
                                                    CodeGenDistribute);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(*this, S, ACCD_distribute, CodeGen);
  emitPostUpdateForReductionClause(*this, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCGangDistributeVectorDirective(
    const ACCGangDistributeVectorDirective &S) {
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitACCLoopBodyWithStopPoint, S.getInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_vector,
                                                    CodeGenDistribute);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(*this, S, ACCD_distribute_vector, CodeGen);
  emitPostUpdateForReductionClause(*this, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCGangDistributeParallelLoopDirective(
    const ACCGangDistributeParallelLoopDirective &S) {
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_distribute,
                                                    CodeGenDistribute);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(*this, S, ACCD_distribute_parallel_loop, CodeGen);
  emitPostUpdateForReductionClause(*this, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCGangDistributeParallelLoopVectorDirective(
    const ACCGangDistributeParallelLoopVectorDirective &S) {
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGen = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                            ACCPrePostActionTy &) {
    ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(
        CGF, ACCD_distribute, CodeGenDistribute, /*HasCancel=*/false);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };
  emitCommonACCGangDirective(*this, S, ACCD_distribute_parallel_loop, CodeGen);
  emitPostUpdateForReductionClause(*this, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

static void emitTargetGangDistributeParallelForRegion(
    CodeGenFunction &CGF, const ACCTargetGangDistributeParallelLoopDirective &S,
    ACCPrePostActionTy &Action) {
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGenGang = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                                 ACCPrePostActionTy &) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(
        CGF, ACCD_distribute, CodeGenDistribute, /*HasCancel=*/false);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };

  emitCommonACCGangDirective(CGF, S, ACCD_distribute_parallel_loop,
                              CodeGenGang);
  emitPostUpdateForReductionClause(CGF, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCTargetGangDistributeParallelForDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetGangDistributeParallelLoopDirective &S) {
  // Emit SPMD target teams distribute parallel for region as a standalone
  // region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeParallelForRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetGangDistributeParallelLoopDirective(
    const ACCTargetGangDistributeParallelLoopDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeParallelForRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void emitTargetGangDistributeParallelForVectorRegion(
    CodeGenFunction &CGF,
    const ACCTargetGangDistributeParallelLoopVectorDirective &S,
    ACCPrePostActionTy &Action) {
  auto &&CodeGenDistribute = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCDistributeLoop(S, emitInnerParallelForWhenCombined,
                              S.getDistInc());
  };

  // Emit teams region as a standalone region.
  auto &&CodeGenGang = [&S, &CodeGenDistribute](CodeGenFunction &CGF,
                                                 ACCPrePostActionTy &) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(
        CGF, ACCD_distribute, CodeGenDistribute, /*HasCancel=*/false);
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_gang);
  };

  emitCommonACCGangDirective(CGF, S, ACCD_distribute_parallel_loop_vector,
                              CodeGenGang);
  emitPostUpdateForReductionClause(CGF, S,
                                   [](CodeGenFunction &) { return nullptr; });
}

void CodeGenFunction::EmitACCTargetGangDistributeParallelForVectorDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetGangDistributeParallelLoopVectorDirective &S) {
  // Emit SPMD target teams distribute parallel for vector region as a standalone
  // region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeParallelForVectorRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetGangDistributeParallelLoopVectorDirective(
    const ACCTargetGangDistributeParallelLoopVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetGangDistributeParallelForVectorRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

void CodeGenFunction::EmitACCCancellationPointDirective(
    const ACCCancellationPointDirective &S) {
  CGM.getOpenACCRuntime().emitCancellationPointCall(*this, S.getLocStart(),
                                                   S.getCancelRegion());
}

void CodeGenFunction::EmitACCCancelDirective(const ACCCancelDirective &S) {
  const Expr *IfCond = nullptr;
  for (const auto *C : S.getClausesOfKind<ACCIfClause>()) {
    if (C->getNameModifier() == ACCD_unknown ||
        C->getNameModifier() == ACCD_cancel) {
      IfCond = C->getCondition();
      break;
    }
  }
  CGM.getOpenACCRuntime().emitCancelCall(*this, S.getLocStart(), IfCond,
                                        S.getCancelRegion());
}

CodeGenFunction::JumpDest
CodeGenFunction::getACCCancelDestination(OpenACCDirectiveKind Kind) {
  if (Kind == ACCD_parallel || Kind == ACCD_task ||
      Kind == ACCD_target_parallel)
    return ReturnBlock;
  assert(Kind == ACCD_loop || Kind == ACCD_section || Kind == ACCD_sections ||
         Kind == ACCD_parallel_sections || Kind == ACCD_parallel_loop ||
         Kind == ACCD_distribute_parallel_loop ||
         Kind == ACCD_target_parallel_loop ||
         Kind == ACCD_gang_distribute_parallel_loop ||
         Kind == ACCD_target_gang_distribute_parallel_loop);
  return ACCCancelStack.getExitBlock();
}

void CodeGenFunction::EmitACCUseDevicePtrClause(
    const ACCClause &NC, ACCPrivateScope &PrivateScope,
    const llvm::DenseMap<const ValueDecl *, Address> &CaptureDeviceAddrMap) {
  const auto &C = cast<ACCUseDevicePtrClause>(NC);
  auto OrigVarIt = C.varlist_begin();
  auto InitIt = C.inits().begin();
  for (auto PvtVarIt : C.private_copies()) {
    auto *OrigVD = cast<VarDecl>(cast<DeclRefExpr>(*OrigVarIt)->getDecl());
    auto *InitVD = cast<VarDecl>(cast<DeclRefExpr>(*InitIt)->getDecl());
    auto *PvtVD = cast<VarDecl>(cast<DeclRefExpr>(PvtVarIt)->getDecl());

    // In order to identify the right initializer we need to match the
    // declaration used by the mapping logic. In some cases we may get
    // ACCCapturedExprDecl that refers to the original declaration.
    const ValueDecl *MatchingVD = OrigVD;
    if (auto *OED = dyn_cast<ACCCapturedExprDecl>(MatchingVD)) {
      // ACCCapturedExprDecl are used to privative fields of the current
      // structure.
      auto *ME = cast<MemberExpr>(OED->getInit());
      assert(isa<CXXThisExpr>(ME->getBase()) &&
             "Base should be the current struct!");
      MatchingVD = ME->getMemberDecl();
    }

    // If we don't have information about the current list item, move on to
    // the next one.
    auto InitAddrIt = CaptureDeviceAddrMap.find(MatchingVD);
    if (InitAddrIt == CaptureDeviceAddrMap.end())
      continue;

    bool IsRegistered = PrivateScope.addPrivate(OrigVD, [&]() -> Address {
      // Initialize the temporary initialization variable with the address we
      // get from the runtime library. We have to cast the source address
      // because it is always a void *. References are materialized in the
      // privatization scope, so the initialization here disregards the fact
      // the original variable is a reference.
      QualType AddrQTy =
          getContext().getPointerType(OrigVD->getType().getNonReferenceType());
      llvm::Type *AddrTy = ConvertTypeForMem(AddrQTy);
      Address InitAddr = Builder.CreateBitCast(InitAddrIt->second, AddrTy);
      setAddrOfLocalVar(InitVD, InitAddr);

      // Emit private declaration, it will be initialized by the value we
      // declaration we just added to the local declarations map.
      EmitDecl(*PvtVD);

      // The initialization variables reached its purpose in the emission
      // ofthe previous declaration, so we don't need it anymore.
      LocalDeclMap.erase(InitVD);

      // Return the address of the private variable.
      return GetAddrOfLocalVar(PvtVD);
    });
    assert(IsRegistered && "firstprivate var already registered as private");
    // Silence the warning about unused variable.
    (void)IsRegistered;

    ++OrigVarIt;
    ++InitIt;
  }
}

// Generate the instructions for '#pragma acc target data' directive.
void CodeGenFunction::EmitACCDataDirective(
    const ACCDataDirective &S) {
  CGOpenACCRuntime::TargetDataInfo Info(/*RequiresDevicePointerInfo=*/true);

  // Create a pre/post action to signal the privatization of the device pointer.
  // This action can be replaced by the OpenACC runtime code generation to
  // deactivate privatization.
  bool PrivatizeDevicePointers = false;
  class DevicePointerPrivActionTy : public ACCPrePostActionTy {
    bool &PrivatizeDevicePointers;

  public:
    explicit DevicePointerPrivActionTy(bool &PrivatizeDevicePointers)
        : ACCPrePostActionTy(), PrivatizeDevicePointers(PrivatizeDevicePointers) {}
    void Enter(CodeGenFunction &CGF) override {
      PrivatizeDevicePointers = true;
    }
  };
  DevicePointerPrivActionTy PrivAction(PrivatizeDevicePointers);

  auto &&CodeGen = [&S, &Info, &PrivatizeDevicePointers](
                       CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    auto &&InnermostCodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
      CGF.EmitStmt(S.getInnermostCapturedStmt()->getCapturedStmt());
    };

    // Codegen that selects wheather to generate the privatization code or not.
    auto &&PrivCodeGen = [&S, &Info, &PrivatizeDevicePointers,
                          &InnermostCodeGen](CodeGenFunction &CGF,
                                             ACCPrePostActionTy &Action) {
      ACCRegionCodeGenTy RCG(InnermostCodeGen);
      PrivatizeDevicePointers = false;

      // Call the pre-action to change the status of PrivatizeDevicePointers if
      // needed.
      Action.Enter(CGF);

      if (PrivatizeDevicePointers) {
        ACCPrivateScope PrivateScope(CGF);
        // Emit all instances of the use_device_ptr clause.
        for (const auto *C : S.getClausesOfKind<ACCUseDevicePtrClause>())
          CGF.EmitACCUseDevicePtrClause(*C, PrivateScope,
                                        Info.CaptureDeviceAddrMap);
        (void)PrivateScope.Privatize();
        RCG(CGF);
      } else
        RCG(CGF);
    };

    // Forward the provided action to the privatization codegen.
    ACCRegionCodeGenTy PrivRCG(PrivCodeGen);
    PrivRCG.setAction(Action);

    // Notwithstanding the body of the region is emitted as inlined directive,
    // we don't use an inline scope as changes in the references inside the
    // region are expected to be visible outside, so we do not privative them.
    ACCLexicalScope Scope(CGF, S);
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_data,
                                                    PrivRCG);
  };

  ACCRegionCodeGenTy RCG(CodeGen);

  // If we don't have target devices, don't bother emitting the data mapping
  // code.
  if (CGM.getLangOpts().ACCTargetTriples.empty()) {
    RCG(*this);
    return;
  }

  // Check if we have any if clause associated with the directive.
  const Expr *IfCond = nullptr;
  if (auto *C = S.getSingleClause<ACCIfClause>())
    IfCond = C->getCondition();

  // Check if we have any device clause associated with the directive.
  const Expr *Device = nullptr;
  if (auto *C = S.getSingleClause<ACCDeviceClause>())
    Device = C->getDevice();

  // Set the action to signal privatization of device pointers.
  RCG.setAction(PrivAction);

  // Emit region code.
  CGM.getOpenACCRuntime().emitTargetDataCalls(*this, S, IfCond, Device, RCG,
                                             Info);
}

void CodeGenFunction::EmitACCEnterDataDirective(
    const ACCEnterDataDirective &S) {
  // If we don't have target devices, don't bother emitting the data mapping
  // code.
  if (CGM.getLangOpts().ACCTargetTriples.empty())
    return;

  // Check if we have any if clause associated with the directive.
  const Expr *IfCond = nullptr;
  if (auto *C = S.getSingleClause<ACCIfClause>())
    IfCond = C->getCondition();

  // Check if we have any device clause associated with the directive.
  const Expr *Device = nullptr;
  if (auto *C = S.getSingleClause<ACCDeviceClause>())
    Device = C->getDevice();

  ACCLexicalScope Scope(*this, S, ACCD_task);
  CGM.getOpenACCRuntime().emitTargetDataStandAloneCall(*this, S, IfCond, Device);
}

void CodeGenFunction::EmitACCExitDataDirective(
    const ACCExitDataDirective &S) {
  // If we don't have target devices, don't bother emitting the data mapping
  // code.
  if (CGM.getLangOpts().ACCTargetTriples.empty())
    return;

  // Check if we have any if clause associated with the directive.
  const Expr *IfCond = nullptr;
  if (auto *C = S.getSingleClause<ACCIfClause>())
    IfCond = C->getCondition();

  // Check if we have any device clause associated with the directive.
  const Expr *Device = nullptr;
  if (auto *C = S.getSingleClause<ACCDeviceClause>())
    Device = C->getDevice();

  ACCLexicalScope Scope(*this, S, ACCD_task);
  CGM.getOpenACCRuntime().emitTargetDataStandAloneCall(*this, S, IfCond, Device);
}

static void emitTargetParallelRegion(CodeGenFunction &CGF,
                                     const ACCTargetParallelDirective &S,
                                     ACCPrePostActionTy &Action) {
  // Get the captured statement associated with the 'parallel' region.
  auto *CS = S.getCapturedStmt(ACCD_parallel);
  Action.Enter(CGF);
  auto &&CodeGen = [&S, CS](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CodeGenFunction::ACCPrivateScope PrivateScope(CGF);
    (void)CGF.EmitACCFirstprivateClause(S, PrivateScope);
    CGF.EmitACCPrivateClause(S, PrivateScope);
    CGF.EmitACCReductionClauseInit(S, PrivateScope);
    (void)PrivateScope.Privatize();
    // TODO: Add support for clauses.
    CGF.EmitStmt(CS->getCapturedStmt());
    CGF.EmitACCReductionClauseFinal(S, /*ReductionKind=*/ACCD_parallel);
  };
  emitCommonACCParallelDirective(CGF, S, ACCD_parallel, CodeGen,
                                 emitEmptyBoundParameters);
  emitPostUpdateForReductionClause(
      CGF, S, [](CodeGenFunction &) -> llvm::Value * { return nullptr; });
}

void CodeGenFunction::EmitACCTargetParallelDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetParallelDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetParallelDirective(
    const ACCTargetParallelDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void emitTargetParallelForRegion(CodeGenFunction &CGF,
                                        const ACCTargetParallelLoopDirective &S,
                                        ACCPrePostActionTy &Action) {
  Action.Enter(CGF);
  // Emit directive as a combined directive that consists of two implicit
  // directives: 'parallel' with 'for' directive.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CodeGenFunction::ACCCancelStackRAII CancelRegion(
        CGF, ACCD_target_parallel_loop, S.hasCancel());
    CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(), emitForLoopBounds,
                               emitDispatchForLoopBounds);
  };
  emitCommonACCParallelDirective(CGF, S, ACCD_loop, CodeGen,
                                 emitEmptyBoundParameters);
}

void CodeGenFunction::EmitACCTargetParallelForDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetParallelLoopDirective &S) {
  // Emit SPMD target parallel for region as a standalone region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelForRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetParallelLoopDirective(
    const ACCTargetParallelLoopDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelForRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

static void
emitTargetParallelForVectorRegion(CodeGenFunction &CGF,
                                const ACCTargetParallelLoopVectorDirective &S,
                                ACCPrePostActionTy &Action) {
  Action.Enter(CGF);
  // Emit directive as a combined directive that consists of two implicit
  // directives: 'parallel' with 'for' directive.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    CGF.EmitACCWorksharingLoop(S, S.getEnsureUpperBound(), emitForLoopBounds,
                               emitDispatchForLoopBounds);
  };
  emitCommonACCParallelDirective(CGF, S, ACCD_vector, CodeGen,
                                 emitEmptyBoundParameters);
}

void CodeGenFunction::EmitACCTargetParallelForVectorDeviceFunction(
    CodeGenModule &CGM, StringRef ParentName,
    const ACCTargetParallelLoopVectorDirective &S) {
  // Emit SPMD target parallel for region as a standalone region.
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelForVectorRegion(CGF, S, Action);
  };
  llvm::Function *Fn;
  llvm::Constant *Addr;
  // Emit target region as a standalone region.
  CGM.getOpenACCRuntime().emitTargetOutlinedFunction(
      S, ParentName, Fn, Addr, /*IsOffloadEntry=*/true, CodeGen);
  assert(Fn && Addr && "Target device function emission failed.");
}

void CodeGenFunction::EmitACCTargetParallelLoopVectorDirective(
    const ACCTargetParallelLoopVectorDirective &S) {
  auto &&CodeGen = [&S](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    emitTargetParallelForVectorRegion(CGF, S, Action);
  };
  emitCommonACCTargetDirective(*this, S, CodeGen);
}

/// Emit a helper variable and return corresponding lvalue.
static void mapParam(CodeGenFunction &CGF, const DeclRefExpr *Helper,
                     const ImplicitParamDecl *PVD,
                     CodeGenFunction::ACCPrivateScope &Privates) {
  auto *VDecl = cast<VarDecl>(Helper->getDecl());
  Privates.addPrivate(
      VDecl, [&CGF, PVD]() -> Address { return CGF.GetAddrOfLocalVar(PVD); });
}

void CodeGenFunction::EmitACCTaskLoopBasedDirective(const ACCLoopLikeDirective &S) {
  assert(isOpenACCTaskLoopDirective(S.getDirectiveKind()));
  // Emit outlined function for task construct.
  const CapturedStmt *CS = S.getCapturedStmt(ACCD_taskloop);
  auto CapturedStruct = GenerateCapturedStmtArgument(*CS);
  auto SharedsTy = getContext().getRecordType(CS->getCapturedRecordDecl());
  const Expr *IfCond = nullptr;
  for (const auto *C : S.getClausesOfKind<ACCIfClause>()) {
    if (C->getNameModifier() == ACCD_unknown ||
        C->getNameModifier() == ACCD_taskloop) {
      IfCond = C->getCondition();
      break;
    }
  }

  ACCTaskDataTy Data;
  // Check if taskloop must be emitted without taskgroup.
  Data.Nogroup = S.getSingleClause<ACCNogroupClause>();
  // TODO: Check if we should emit tied or untied task.
  Data.Tied = true;
  // Set scheduling for taskloop
  if (const auto* Clause = S.getSingleClause<ACCGrainsizeClause>()) {
    // grainsize clause
    Data.Schedule.setInt(/*IntVal=*/false);
    Data.Schedule.setPointer(EmitScalarExpr(Clause->getGrainsize()));
  } else if (const auto* Clause = S.getSingleClause<ACCNumTasksClause>()) {
    // num_tasks clause
    Data.Schedule.setInt(/*IntVal=*/true);
    Data.Schedule.setPointer(EmitScalarExpr(Clause->getNumTasks()));
  }

  auto &&BodyGen = [CS, &S](CodeGenFunction &CGF, ACCPrePostActionTy &) {
    // if (PreCond) {
    //   for (IV in 0..LastIteration) BODY;
    //   <Final counter/linear vars updates>;
    // }
    //

    // Emit: if (PreCond) - begin.
    // If the condition constant folds and can be elided, avoid emitting the
    // whole loop.
    bool CondConstant;
    llvm::BasicBlock *ContBlock = nullptr;
    ACCLoopScope PreInitScope(CGF, S);
    if (CGF.ConstantFoldsToSimpleInteger(S.getPreCond(), CondConstant)) {
      if (!CondConstant)
        return;
    } else {
      auto *ThenBlock = CGF.createBasicBlock("taskloop.if.then");
      ContBlock = CGF.createBasicBlock("taskloop.if.end");
      emitPreCond(CGF, S, S.getPreCond(), ThenBlock, ContBlock,
                  CGF.getProfileCount(&S));
      CGF.EmitBlock(ThenBlock);
      CGF.incrementProfileCounter(&S);
    }

    if (isOpenACCVectorDirective(S.getDirectiveKind()))
      CGF.EmitACCVectorInit(S);

    ACCPrivateScope LoopScope(CGF);
    // Emit helper vars inits.
    enum { LowerBound = 5, UpperBound, Stride, LastIter };
    auto *I = CS->getCapturedDecl()->param_begin();
    auto *LBP = std::next(I, LowerBound);
    auto *UBP = std::next(I, UpperBound);
    auto *STP = std::next(I, Stride);
    auto *LIP = std::next(I, LastIter);
    mapParam(CGF, cast<DeclRefExpr>(S.getLowerBoundVariable()), *LBP,
             LoopScope);
    mapParam(CGF, cast<DeclRefExpr>(S.getUpperBoundVariable()), *UBP,
             LoopScope);
    mapParam(CGF, cast<DeclRefExpr>(S.getStrideVariable()), *STP, LoopScope);
    mapParam(CGF, cast<DeclRefExpr>(S.getIsLastIterVariable()), *LIP,
             LoopScope);
    CGF.EmitACCPrivateLoopCounters(S, LoopScope);
    bool HasLastprivateClause = CGF.EmitACCLastprivateClauseInit(S, LoopScope);
    (void)LoopScope.Privatize();
    // Emit the loop iteration variable.
    const Expr *IVExpr = S.getIterationVariable();
    const VarDecl *IVDecl = cast<VarDecl>(cast<DeclRefExpr>(IVExpr)->getDecl());
    CGF.EmitVarDecl(*IVDecl);
    CGF.EmitIgnoredExpr(S.getInit());

    // Emit the iterations count variable.
    // If it is not a variable, Sema decided to calculate iterations count on
    // each iteration (e.g., it is foldable into a constant).
    if (auto LIExpr = dyn_cast<DeclRefExpr>(S.getLastIteration())) {
      CGF.EmitVarDecl(*cast<VarDecl>(LIExpr->getDecl()));
      // Emit calculation of the iterations count.
      CGF.EmitIgnoredExpr(S.getCalcLastIteration());
    }

    CGF.EmitACCInnerLoop(S, LoopScope.requiresCleanups(), S.getCond(),
                         S.getInc(),
                         [&S](CodeGenFunction &CGF) {
                           CGF.EmitACCLoopBody(S, JumpDest());
                           CGF.EmitStopPoint(&S);
                         },
                         [](CodeGenFunction &) {});
    // Emit: if (PreCond) - end.
    if (ContBlock) {
      CGF.EmitBranch(ContBlock);
      CGF.EmitBlock(ContBlock, true);
    }
    // Emit final copy of the lastprivate variables if IsLastIter != 0.
    if (HasLastprivateClause) {
      CGF.EmitACCLastprivateClauseFinal(
          S, isOpenACCVectorDirective(S.getDirectiveKind()),
          CGF.Builder.CreateIsNotNull(CGF.EmitLoadOfScalar(
              CGF.GetAddrOfLocalVar(*LIP), /*Volatile=*/false,
              (*LIP)->getType(), S.getLocStart())));
    }
  };
  auto &&TaskGen = [&S, SharedsTy, CapturedStruct,
                    IfCond](CodeGenFunction &CGF, llvm::Value *OutlinedFn,
                            const ACCTaskDataTy &Data) {
    auto &&CodeGen = [&](CodeGenFunction &CGF, ACCPrePostActionTy &) {
      ACCLoopScope PreInitScope(CGF, S);
      CGF.CGM.getOpenACCRuntime().emitTaskLoopCall(CGF, S.getLocStart(), S,
                                                  OutlinedFn, SharedsTy,
                                                  CapturedStruct, IfCond, Data);
    };
    CGF.CGM.getOpenACCRuntime().emitInlinedDirective(CGF, ACCD_taskloop,
                                                    CodeGen);
  };
  if (Data.Nogroup) {
    EmitACCTaskBasedDirective(S, ACCD_taskloop, BodyGen, TaskGen, Data);
  } else {
    CGM.getOpenACCRuntime().emitTaskgroupRegion(
        *this,
        [&S, &BodyGen, &TaskGen, &Data](CodeGenFunction &CGF,
                                        ACCPrePostActionTy &Action) {
          Action.Enter(CGF);
          CGF.EmitACCTaskBasedDirective(S, ACCD_taskloop, BodyGen, TaskGen,
                                        Data);
        },
        S.getLocStart());
  }
}

void CodeGenFunction::EmitACCTaskLoopDirective(const ACCTaskLoopDirective &S) {
  EmitACCTaskLoopBasedDirective(S);
}

void CodeGenFunction::EmitACCTaskLoopVectorDirective(
    const ACCTaskLoopVectorDirective &S) {
  EmitACCTaskLoopBasedDirective(S);
}

// Generate the instructions for '#pragma acc target update' directive.
void CodeGenFunction::EmitACCTargetUpdateDirective(
    const ACCTargetUpdateDirective &S) {
  // If we don't have target devices, don't bother emitting the data mapping
  // code.
  if (CGM.getLangOpts().ACCTargetTriples.empty())
    return;

  // Check if we have any if clause associated with the directive.
  const Expr *IfCond = nullptr;
  if (auto *C = S.getSingleClause<ACCIfClause>())
    IfCond = C->getCondition();

  // Check if we have any device clause associated with the directive.
  const Expr *Device = nullptr;
  if (auto *C = S.getSingleClause<ACCDeviceClause>())
    Device = C->getDevice();

  ACCLexicalScope Scope(*this, S, ACCD_task);
  CGM.getOpenACCRuntime().emitTargetDataStandAloneCall(*this, S, IfCond, Device);
}

void CodeGenFunction::EmitSimpleACCExecutableDirective(
    const ACCExecutableDirective &D) {
  if (!D.hasAssociatedStmt() || !D.getAssociatedStmt())
    return;
  auto &&CodeGen = [&D](CodeGenFunction &CGF, ACCPrePostActionTy &Action) {
    if (isOpenACCVectorDirective(D.getDirectiveKind())) {
      emitACCVectorRegion(CGF, cast<ACCLoopLikeDirective>(D), Action);
    } else {
      if (const auto *LD = dyn_cast<ACCLoopLikeDirective>(&D)) {
        for (const auto *E : LD->counters()) {
          if (const auto *VD = dyn_cast<ACCCapturedExprDecl>(
                  cast<DeclRefExpr>(E)->getDecl())) {
            // Emit only those that were not explicitly referenced in clauses.
            if (!CGF.LocalDeclMap.count(VD))
              CGF.EmitVarDecl(*VD);
          }
        }
      }
      CGF.EmitStmt(D.getInnermostCapturedStmt()->getCapturedStmt());
    }
  };
  ACCVectorLexicalScope Scope(*this, D);
  CGM.getOpenACCRuntime().emitInlinedDirective(
      *this,
      isOpenACCVectorDirective(D.getDirectiveKind()) ? ACCD_vector
                                                  : D.getDirectiveKind(),
      CodeGen);
}
