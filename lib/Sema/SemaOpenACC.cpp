//===--- SemaOpenACC.cpp - Semantic Analysis for OpenACC constructs ---------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file implements semantic analysis for OpenACC directives and
/// clauses.
///
//===----------------------------------------------------------------------===//

#include "TreeTransform.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTMutationListener.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclOpenACC.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/StmtOpenACC.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/OpenACCKinds.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/Sema/SemaInternal.h"
#include "llvm/ADT/PointerEmbeddedInt.h"
using namespace clang;

//===----------------------------------------------------------------------===//
// Stack of data-sharing attributes for variables
//===----------------------------------------------------------------------===//

static Expr *CheckMapClauseExpressionBase(
    Sema &SemaRef, Expr *E,
    ACCClauseMappableExprCommon::MappableExprComponentList &CurComponents,
    OpenACCClauseKind CKind, bool NoDiagnose);

namespace {
/// \brief Default data sharing attributes, which can be applied to directive.
enum DefaultDataSharingAttributes {
  DSA_unspecified = 0, /// \brief Data sharing attribute not specified.
  DSA_none = 1 << 0,   /// \brief Default data sharing attribute 'none'.
  DSA_shared = 1 << 1, /// \brief Default data sharing attribute 'shared'.
};

/// Attributes of the defaultmap clause.
enum DefaultMapAttributes {
  DMA_unspecified,   /// Default mapping is not specified.
  DMA_tofrom_scalar, /// Default mapping is 'tofrom:scalar'.
};

/// \brief Stack for tracking declarations used in OpenACC directives and
/// clauses and their data-sharing attributes.
class DSAStackTy final {
public:
  struct DSAVarData final {
    OpenACCDirectiveKind DKind = ACCD_unknown;
    OpenACCClauseKind CKind = ACCC_unknown;
    Expr *RefExpr = nullptr;
    DeclRefExpr *PrivateCopy = nullptr;
    SourceLocation ImplicitDSALoc;
    DSAVarData() = default;
    DSAVarData(OpenACCDirectiveKind DKind, OpenACCClauseKind CKind, Expr *RefExpr,
               DeclRefExpr *PrivateCopy, SourceLocation ImplicitDSALoc)
        : DKind(DKind), CKind(CKind), RefExpr(RefExpr),
          PrivateCopy(PrivateCopy), ImplicitDSALoc(ImplicitDSALoc) {}
  };
  typedef llvm::SmallVector<std::pair<Expr *, OverloadedOperatorKind>, 4>
      OperatorOffsetTy;

private:
  struct DSAInfo final {
    OpenACCClauseKind Attributes = ACCC_unknown;
    /// Pointer to a reference expression and a flag which shows that the
    /// variable is marked as lastprivate(true) or not (false).
    llvm::PointerIntPair<Expr *, 1, bool> RefExpr;
    DeclRefExpr *PrivateCopy = nullptr;
  };
  typedef llvm::DenseMap<ValueDecl *, DSAInfo> DeclSAMapTy;
  typedef llvm::DenseMap<ValueDecl *, Expr *> AlignedMapTy;
  typedef std::pair<unsigned, VarDecl *> LCDeclInfo;
  typedef llvm::DenseMap<ValueDecl *, LCDeclInfo> LoopControlVariablesMapTy;
  /// Struct that associates a component with the clause kind where they are
  /// found.
  struct MappedExprComponentTy {
    ACCClauseMappableExprCommon::MappableExprComponentLists Components;
    OpenACCClauseKind Kind = ACCC_unknown;
  };
  typedef llvm::DenseMap<ValueDecl *, MappedExprComponentTy>
      MappedExprComponentsTy;
  typedef llvm::StringMap<std::pair<ACCCriticalDirective *, llvm::APSInt>>
      CriticalsWithHintsTy;
  typedef llvm::DenseMap<ACCDependClause *, OperatorOffsetTy>
      DoacrossDependMapTy;
  struct ReductionData {
    typedef llvm::PointerEmbeddedInt<BinaryOperatorKind, 16> BOKPtrType;
    SourceRange ReductionRange;
    llvm::PointerUnion<const Expr *, BOKPtrType> ReductionOp;
    ReductionData() = default;
    void set(BinaryOperatorKind BO, SourceRange RR) {
      ReductionRange = RR;
      ReductionOp = BO;
    }
    void set(const Expr *RefExpr, SourceRange RR) {
      ReductionRange = RR;
      ReductionOp = RefExpr;
    }
  };
  typedef llvm::DenseMap<ValueDecl *, ReductionData> DeclReductionMapTy;

  struct SharingMapTy final {
    DeclSAMapTy SharingMap;
    DeclReductionMapTy ReductionMap;
    AlignedMapTy AlignedMap;
    MappedExprComponentsTy MappedExprComponents;
    LoopControlVariablesMapTy LCVMap;
    DefaultDataSharingAttributes DefaultAttr = DSA_unspecified;
    SourceLocation DefaultAttrLoc;
    DefaultMapAttributes DefaultMapAttr = DMA_unspecified;
    SourceLocation DefaultMapAttrLoc;
    OpenACCDirectiveKind Directive = ACCD_unknown;
    DeclarationNameInfo DirectiveName;
    Scope *CurScope = nullptr;
    SourceLocation ConstructLoc;
    /// Set of 'depend' clauses with 'sink|source' dependence kind. Required to
    /// get the data (loop counters etc.) about enclosing loop-based construct.
    /// This data is required during codegen.
    DoacrossDependMapTy DoacrossDepends;
    /// \brief first argument (Expr *) contains optional argument of the
    /// 'ordered' clause, the second one is true if the regions has 'ordered'
    /// clause, false otherwise.
    llvm::PointerIntPair<Expr *, 1, bool> OrderedRegion;
    bool NowaitRegion = false;
    bool CancelRegion = false;
    unsigned AssociatedLoops = 1;
    SourceLocation InnerTeamsRegionLoc;
    /// Reference to the taskgroup task_reduction reference expression.
    Expr *TaskgroupReductionRef = nullptr;
    SharingMapTy(OpenACCDirectiveKind DKind, DeclarationNameInfo Name,
                 Scope *CurScope, SourceLocation Loc)
        : Directive(DKind), DirectiveName(Name), CurScope(CurScope),
          ConstructLoc(Loc) {}
    SharingMapTy() = default;
  };

  typedef SmallVector<SharingMapTy, 4> StackTy;

  /// \brief Stack of used declaration and their data-sharing attributes.
  DeclSAMapTy Threadprivates;
  const FunctionScopeInfo *CurrentNonCapturingFunctionScope = nullptr;
  SmallVector<std::pair<StackTy, const FunctionScopeInfo *>, 4> Stack;
  /// \brief true, if check for DSA must be from parent directive, false, if
  /// from current directive.
  OpenACCClauseKind ClauseKindMode = ACCC_unknown;
  Sema &SemaRef;
  bool ForceCapturing = false;
  CriticalsWithHintsTy Criticals;

  typedef SmallVector<SharingMapTy, 8>::reverse_iterator reverse_iterator;

  DSAVarData getDSA(StackTy::reverse_iterator &Iter, ValueDecl *D);

  /// \brief Checks if the variable is a local for OpenACC region.
  bool isOpenACCLocal(VarDecl *D, StackTy::reverse_iterator Iter);

  bool isStackEmpty() const {
    return Stack.empty() ||
           Stack.back().second != CurrentNonCapturingFunctionScope ||
           Stack.back().first.empty();
  }

public:
  explicit DSAStackTy(Sema &S) : SemaRef(S) {}

  bool isClauseParsingMode() const { return ClauseKindMode != ACCC_unknown; }
  OpenACCClauseKind getClauseParsingMode() const {
    assert(isClauseParsingMode() && "Must be in clause parsing mode.");
    return ClauseKindMode;
  }
  void setClauseParsingMode(OpenACCClauseKind K) { ClauseKindMode = K; }

  bool isForceVarCapturing() const { return ForceCapturing; }
  void setForceVarCapturing(bool V) { ForceCapturing = V; }

  void push(OpenACCDirectiveKind DKind, const DeclarationNameInfo &DirName,
            Scope *CurScope, SourceLocation Loc) {
    if (Stack.empty() ||
        Stack.back().second != CurrentNonCapturingFunctionScope)
      Stack.emplace_back(StackTy(), CurrentNonCapturingFunctionScope);
    Stack.back().first.emplace_back(DKind, DirName, CurScope, Loc);
    Stack.back().first.back().DefaultAttrLoc = Loc;
  }

  void pop() {
    assert(!Stack.back().first.empty() &&
           "Data-sharing attributes stack is empty!");
    Stack.back().first.pop_back();
  }

  /// Start new OpenACC region stack in new non-capturing function.
  void pushFunction() {
    const FunctionScopeInfo *CurFnScope = SemaRef.getCurFunction();
    assert(!isa<CapturingScopeInfo>(CurFnScope));
    CurrentNonCapturingFunctionScope = CurFnScope;
  }
  /// Pop region stack for non-capturing function.
  void popFunction(const FunctionScopeInfo *OldFSI) {
    if (!Stack.empty() && Stack.back().second == OldFSI) {
      assert(Stack.back().first.empty());
      Stack.pop_back();
    }
    CurrentNonCapturingFunctionScope = nullptr;
    for (const FunctionScopeInfo *FSI : llvm::reverse(SemaRef.FunctionScopes)) {
      if (!isa<CapturingScopeInfo>(FSI)) {
        CurrentNonCapturingFunctionScope = FSI;
        break;
      }
    }
  }

  void addCriticalWithHint(ACCCriticalDirective *D, llvm::APSInt Hint) {
    Criticals[D->getDirectiveName().getAsString()] = std::make_pair(D, Hint);
  }
  const std::pair<ACCCriticalDirective *, llvm::APSInt>
  getCriticalWithHint(const DeclarationNameInfo &Name) const {
    auto I = Criticals.find(Name.getAsString());
    if (I != Criticals.end())
      return I->second;
    return std::make_pair(nullptr, llvm::APSInt());
  }
  /// \brief If 'aligned' declaration for given variable \a D was not seen yet,
  /// add it and return NULL; otherwise return previous occurrence's expression
  /// for diagnostics.
  Expr *addUniqueAligned(ValueDecl *D, Expr *NewDE);

  /// \brief Register specified variable as loop control variable.
  void addLoopControlVariable(ValueDecl *D, VarDecl *Capture);
  /// \brief Check if the specified variable is a loop control variable for
  /// current region.
  /// \return The index of the loop control variable in the list of associated
  /// for-loops (from outer to inner).
  LCDeclInfo isLoopControlVariable(ValueDecl *D);
  /// \brief Check if the specified variable is a loop control variable for
  /// parent region.
  /// \return The index of the loop control variable in the list of associated
  /// for-loops (from outer to inner).
  LCDeclInfo isParentLoopControlVariable(ValueDecl *D);
  /// \brief Get the loop control variable for the I-th loop (or nullptr) in
  /// parent directive.
  ValueDecl *getParentLoopControlVariable(unsigned I);

  /// \brief Adds explicit data sharing attribute to the specified declaration.
  void addDSA(ValueDecl *D, Expr *E, OpenACCClauseKind A,
              DeclRefExpr *PrivateCopy = nullptr);

  /// Adds additional information for the reduction items with the reduction id
  /// represented as an operator.
  void addTaskgroupReductionData(ValueDecl *D, SourceRange SR,
                                 BinaryOperatorKind BOK);
  /// Adds additional information for the reduction items with the reduction id
  /// represented as reduction identifier.
  void addTaskgroupReductionData(ValueDecl *D, SourceRange SR,
                                 const Expr *ReductionRef);
  /// Returns the location and reduction operation from the innermost parent
  /// region for the given \p D.
  DSAVarData getTopMostTaskgroupReductionData(ValueDecl *D, SourceRange &SR,
                                              BinaryOperatorKind &BOK,
                                              Expr *&TaskgroupDescriptor);
  /// Returns the location and reduction operation from the innermost parent
  /// region for the given \p D.
  DSAVarData getTopMostTaskgroupReductionData(ValueDecl *D, SourceRange &SR,
                                              const Expr *&ReductionRef,
                                              Expr *&TaskgroupDescriptor);
  /// Return reduction reference expression for the current taskgroup.
  Expr *getTaskgroupReductionRef() const {
    assert(Stack.back().first.back().Directive == ACCD_taskgroup &&
           "taskgroup reference expression requested for non taskgroup "
           "directive.");
    return Stack.back().first.back().TaskgroupReductionRef;
  }
  /// Checks if the given \p VD declaration is actually a taskgroup reduction
  /// descriptor variable at the \p Level of OpenACC regions.
  bool isTaskgroupReductionRef(ValueDecl *VD, unsigned Level) const {
    return Stack.back().first[Level].TaskgroupReductionRef &&
           cast<DeclRefExpr>(Stack.back().first[Level].TaskgroupReductionRef)
                   ->getDecl() == VD;
  }

  /// \brief Returns data sharing attributes from top of the stack for the
  /// specified declaration.
  DSAVarData getTopDSA(ValueDecl *D, bool FromParent);
  /// \brief Returns data-sharing attributes for the specified declaration.
  DSAVarData getImplicitDSA(ValueDecl *D, bool FromParent);
  /// \brief Checks if the specified variables has data-sharing attributes which
  /// match specified \a CPred predicate in any directive which matches \a DPred
  /// predicate.
  DSAVarData hasDSA(ValueDecl *D,
                    const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
                    const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
                    bool FromParent);
  /// \brief Checks if the specified variables has data-sharing attributes which
  /// match specified \a CPred predicate in any innermost directive which
  /// matches \a DPred predicate.
  DSAVarData
  hasInnermostDSA(ValueDecl *D,
                  const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
                  const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
                  bool FromParent);
  /// \brief Checks if the specified variables has explicit data-sharing
  /// attributes which match specified \a CPred predicate at the specified
  /// OpenACC region.
  bool hasExplicitDSA(ValueDecl *D,
                      const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
                      unsigned Level, bool NotLastprivate = false);

  /// \brief Returns true if the directive at level \Level matches in the
  /// specified \a DPred predicate.
  bool hasExplicitDirective(
      const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
      unsigned Level);

  /// \brief Finds a directive which matches specified \a DPred predicate.
  bool hasDirective(const llvm::function_ref<bool(OpenACCDirectiveKind,
                                                  const DeclarationNameInfo &,
                                                  SourceLocation)> &DPred,
                    bool FromParent);

  /// \brief Returns currently analyzed directive.
  OpenACCDirectiveKind getCurrentDirective() const {
    return isStackEmpty() ? ACCD_unknown : Stack.back().first.back().Directive;
  }
  /// \brief Returns directive kind at specified level.
  OpenACCDirectiveKind getDirective(unsigned Level) const {
    assert(!isStackEmpty() && "No directive at specified level.");
    return Stack.back().first[Level].Directive;
  }
  /// \brief Returns parent directive.
  OpenACCDirectiveKind getParentDirective() const {
    if (isStackEmpty() || Stack.back().first.size() == 1)
      return ACCD_unknown;
    return std::next(Stack.back().first.rbegin())->Directive;
  }

  /// \brief Set default data sharing attribute to none.
  void setDefaultDSANone(SourceLocation Loc) {
    assert(!isStackEmpty());
    Stack.back().first.back().DefaultAttr = DSA_none;
    Stack.back().first.back().DefaultAttrLoc = Loc;
  }
  /// \brief Set default data sharing attribute to shared.
  void setDefaultDSAShared(SourceLocation Loc) {
    assert(!isStackEmpty());
    Stack.back().first.back().DefaultAttr = DSA_shared;
    Stack.back().first.back().DefaultAttrLoc = Loc;
  }
  /// Set default data mapping attribute to 'tofrom:scalar'.
  void setDefaultDMAToFromScalar(SourceLocation Loc) {
    assert(!isStackEmpty());
    Stack.back().first.back().DefaultMapAttr = DMA_tofrom_scalar;
    Stack.back().first.back().DefaultMapAttrLoc = Loc;
  }

  DefaultDataSharingAttributes getDefaultDSA() const {
    return isStackEmpty() ? DSA_unspecified
                          : Stack.back().first.back().DefaultAttr;
  }
  SourceLocation getDefaultDSALocation() const {
    return isStackEmpty() ? SourceLocation()
                          : Stack.back().first.back().DefaultAttrLoc;
  }
  DefaultMapAttributes getDefaultDMA() const {
    return isStackEmpty() ? DMA_unspecified
                          : Stack.back().first.back().DefaultMapAttr;
  }
  DefaultMapAttributes getDefaultDMAAtLevel(unsigned Level) const {
    return Stack.back().first[Level].DefaultMapAttr;
  }
  SourceLocation getDefaultDMALocation() const {
    return isStackEmpty() ? SourceLocation()
                          : Stack.back().first.back().DefaultMapAttrLoc;
  }

  /// \brief Checks if the specified variable is a threadprivate.
  bool isThreadPrivate(VarDecl *D) {
    DSAVarData DVar = getTopDSA(D, false);
    return isOpenACCThreadPrivate(DVar.CKind);
  }

  /// \brief Marks current region as ordered (it has an 'ordered' clause).
  void setOrderedRegion(bool IsOrdered, Expr *Param) {
    assert(!isStackEmpty());
    Stack.back().first.back().OrderedRegion.setInt(IsOrdered);
    Stack.back().first.back().OrderedRegion.setPointer(Param);
  }
  /// \brief Returns true, if parent region is ordered (has associated
  /// 'ordered' clause), false - otherwise.
  bool isParentOrderedRegion() const {
    if (isStackEmpty() || Stack.back().first.size() == 1)
      return false;
    return std::next(Stack.back().first.rbegin())->OrderedRegion.getInt();
  }
  /// \brief Returns optional parameter for the ordered region.
  Expr *getParentOrderedRegionParam() const {
    if (isStackEmpty() || Stack.back().first.size() == 1)
      return nullptr;
    return std::next(Stack.back().first.rbegin())->OrderedRegion.getPointer();
  }
  /// \brief Marks current region as nowait (it has a 'nowait' clause).
  void setNowaitRegion(bool IsNowait = true) {
    assert(!isStackEmpty());
    Stack.back().first.back().NowaitRegion = IsNowait;
  }
  /// \brief Returns true, if parent region is nowait (has associated
  /// 'nowait' clause), false - otherwise.
  bool isParentNowaitRegion() const {
    if (isStackEmpty() || Stack.back().first.size() == 1)
      return false;
    return std::next(Stack.back().first.rbegin())->NowaitRegion;
  }
  /// \brief Marks parent region as cancel region.
  void setParentCancelRegion(bool Cancel = true) {
    if (!isStackEmpty() && Stack.back().first.size() > 1) {
      auto &StackElemRef = *std::next(Stack.back().first.rbegin());
      StackElemRef.CancelRegion |= StackElemRef.CancelRegion || Cancel;
    }
  }
  /// \brief Return true if current region has inner cancel construct.
  bool isCancelRegion() const {
    return isStackEmpty() ? false : Stack.back().first.back().CancelRegion;
  }

  /// \brief Set collapse value for the region.
  void setAssociatedLoops(unsigned Val) {
    assert(!isStackEmpty());
    Stack.back().first.back().AssociatedLoops = Val;
  }
  /// \brief Return collapse value for region.
  unsigned getAssociatedLoops() const {
    return isStackEmpty() ? 0 : Stack.back().first.back().AssociatedLoops;
  }

  /// \brief Marks current target region as one with closely nested teams
  /// region.
  void setParentTeamsRegionLoc(SourceLocation TeamsRegionLoc) {
    if (!isStackEmpty() && Stack.back().first.size() > 1) {
      std::next(Stack.back().first.rbegin())->InnerTeamsRegionLoc =
          TeamsRegionLoc;
    }
  }
  /// \brief Returns true, if current region has closely nested teams region.
  bool hasInnerTeamsRegion() const {
    return getInnerTeamsRegionLoc().isValid();
  }
  /// \brief Returns location of the nested teams region (if any).
  SourceLocation getInnerTeamsRegionLoc() const {
    return isStackEmpty() ? SourceLocation()
                          : Stack.back().first.back().InnerTeamsRegionLoc;
  }

  Scope *getCurScope() const {
    return isStackEmpty() ? nullptr : Stack.back().first.back().CurScope;
  }
  Scope *getCurScope() {
    return isStackEmpty() ? nullptr : Stack.back().first.back().CurScope;
  }
  SourceLocation getConstructLoc() {
    return isStackEmpty() ? SourceLocation()
                          : Stack.back().first.back().ConstructLoc;
  }

  /// Do the check specified in \a Check to all component lists and return true
  /// if any issue is found.
  bool checkMappableExprComponentListsForDecl(
      ValueDecl *VD, bool CurrentRegionOnly,
      const llvm::function_ref<
          bool(ACCClauseMappableExprCommon::MappableExprComponentListRef,
               OpenACCClauseKind)> &Check) {
    if (isStackEmpty())
      return false;
    auto SI = Stack.back().first.rbegin();
    auto SE = Stack.back().first.rend();

    if (SI == SE)
      return false;

    if (CurrentRegionOnly) {
      SE = std::next(SI);
    } else {
      ++SI;
    }

    for (; SI != SE; ++SI) {
      auto MI = SI->MappedExprComponents.find(VD);
      if (MI != SI->MappedExprComponents.end())
        for (auto &L : MI->second.Components)
          if (Check(L, MI->second.Kind))
            return true;
    }
    return false;
  }

  /// Do the check specified in \a Check to all component lists at a given level
  /// and return true if any issue is found.
  bool checkMappableExprComponentListsForDeclAtLevel(
      ValueDecl *VD, unsigned Level,
      const llvm::function_ref<
          bool(ACCClauseMappableExprCommon::MappableExprComponentListRef,
               OpenACCClauseKind)> &Check) {
    if (isStackEmpty())
      return false;

    auto StartI = Stack.back().first.begin();
    auto EndI = Stack.back().first.end();
    if (std::distance(StartI, EndI) <= (int)Level)
      return false;
    std::advance(StartI, Level);

    auto MI = StartI->MappedExprComponents.find(VD);
    if (MI != StartI->MappedExprComponents.end())
      for (auto &L : MI->second.Components)
        if (Check(L, MI->second.Kind))
          return true;
    return false;
  }

  /// Create a new mappable expression component list associated with a given
  /// declaration and initialize it with the provided list of components.
  void addMappableExpressionComponents(
      ValueDecl *VD,
      ACCClauseMappableExprCommon::MappableExprComponentListRef Components,
      OpenACCClauseKind WhereFoundClauseKind) {
    assert(!isStackEmpty() &&
           "Not expecting to retrieve components from a empty stack!");
    auto &MEC = Stack.back().first.back().MappedExprComponents[VD];
    // Create new entry and append the new components there.
    MEC.Components.resize(MEC.Components.size() + 1);
    MEC.Components.back().append(Components.begin(), Components.end());
    MEC.Kind = WhereFoundClauseKind;
  }

  unsigned getNestingLevel() const {
    assert(!isStackEmpty());
    return Stack.back().first.size() - 1;
  }
  void addDoacrossDependClause(ACCDependClause *C, OperatorOffsetTy &OpsOffs) {
    assert(!isStackEmpty() && Stack.back().first.size() > 1);
    auto &StackElem = *std::next(Stack.back().first.rbegin());
    assert(isOpenACCWorksharingDirective(StackElem.Directive));
    StackElem.DoacrossDepends.insert({C, OpsOffs});
  }
  llvm::iterator_range<DoacrossDependMapTy::const_iterator>
  getDoacrossDependClauses() const {
    assert(!isStackEmpty());
    auto &StackElem = Stack.back().first.back();
    if (isOpenACCWorksharingDirective(StackElem.Directive)) {
      auto &Ref = StackElem.DoacrossDepends;
      return llvm::make_range(Ref.begin(), Ref.end());
    }
    return llvm::make_range(StackElem.DoacrossDepends.end(),
                            StackElem.DoacrossDepends.end());
  }
};
bool isParallelOrTaskRegion(OpenACCDirectiveKind DKind) {
  return isOpenACCParallelDirective(DKind) || isOpenACCTaskingDirective(DKind) ||
         isOpenACCTeamsDirective(DKind) || DKind == ACCD_unknown;
}
} // namespace

static Expr *getExprAsWritten(Expr *E) {
  if (auto *ExprTemp = dyn_cast<ExprWithCleanups>(E))
    E = ExprTemp->getSubExpr();

  if (auto *MTE = dyn_cast<MaterializeTemporaryExpr>(E))
    E = MTE->GetTemporaryExpr();

  while (auto *Binder = dyn_cast<CXXBindTemporaryExpr>(E))
    E = Binder->getSubExpr();

  if (auto *ICE = dyn_cast<ImplicitCastExpr>(E))
    E = ICE->getSubExprAsWritten();
  return E->IgnoreParens();
}

static ValueDecl *getCanonicalDecl(ValueDecl *D) {
  if (auto *CED = dyn_cast<ACCCapturedExprDecl>(D))
    if (auto *ME = dyn_cast<MemberExpr>(getExprAsWritten(CED->getInit())))
      D = ME->getMemberDecl();
  auto *VD = dyn_cast<VarDecl>(D);
  auto *FD = dyn_cast<FieldDecl>(D);
  if (VD != nullptr) {
    VD = VD->getCanonicalDecl();
    D = VD;
  } else {
    assert(FD);
    FD = FD->getCanonicalDecl();
    D = FD;
  }
  return D;
}

DSAStackTy::DSAVarData DSAStackTy::getDSA(StackTy::reverse_iterator &Iter,
                                          ValueDecl *D) {
  D = getCanonicalDecl(D);
  auto *VD = dyn_cast<VarDecl>(D);
  auto *FD = dyn_cast<FieldDecl>(D);
  DSAVarData DVar;
  if (isStackEmpty() || Iter == Stack.back().first.rend()) {
    // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a region but not in construct]
    //  File-scope or namespace-scope variables referenced in called routines
    //  in the region are shared unless they appear in a threadprivate
    //  directive.
    if (VD && !VD->isFunctionOrMethodVarDecl() && !isa<ParmVarDecl>(D))
      DVar.CKind = ACCC_shared;

    // OpenACC [2.9.1.2, Data-sharing Attribute Rules for Variables Referenced
    // in a region but not in construct]
    //  Variables with static storage duration that are declared in called
    //  routines in the region are shared.
    if (VD && VD->hasGlobalStorage())
      DVar.CKind = ACCC_shared;

    // Non-static data members are shared by default.
    if (FD)
      DVar.CKind = ACCC_shared;

    return DVar;
  }

  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, predetermined, p.1]
  // Variables with automatic storage duration that are declared in a scope
  // inside the construct are private.
  if (VD && isOpenACCLocal(VD, Iter) && VD->isLocalVarDecl() &&
      (VD->getStorageClass() == SC_Auto || VD->getStorageClass() == SC_None)) {
    DVar.CKind = ACCC_private;
    return DVar;
  }

  DVar.DKind = Iter->Directive;
  // Explicitly specified attributes and local variables with predetermined
  // attributes.
  if (Iter->SharingMap.count(D)) {
    DVar.RefExpr = Iter->SharingMap[D].RefExpr.getPointer();
    DVar.PrivateCopy = Iter->SharingMap[D].PrivateCopy;
    DVar.CKind = Iter->SharingMap[D].Attributes;
    DVar.ImplicitDSALoc = Iter->DefaultAttrLoc;
    return DVar;
  }

  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, implicitly determined, p.1]
  //  In a parallel or task construct, the data-sharing attributes of these
  //  variables are determined by the default clause, if present.
  switch (Iter->DefaultAttr) {
  case DSA_shared:
    DVar.CKind = ACCC_shared;
    DVar.ImplicitDSALoc = Iter->DefaultAttrLoc;
    return DVar;
  case DSA_none:
    return DVar;
  case DSA_unspecified:
    // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct, implicitly determined, p.2]
    //  In a parallel construct, if no default clause is present, these
    //  variables are shared.
    DVar.ImplicitDSALoc = Iter->DefaultAttrLoc;
    if (isOpenACCParallelDirective(DVar.DKind) ||
        isOpenACCTeamsDirective(DVar.DKind)) {
      DVar.CKind = ACCC_shared;
      return DVar;
    }

    // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct, implicitly determined, p.4]
    //  In a task construct, if no default clause is present, a variable that in
    //  the enclosing context is determined to be shared by all implicit tasks
    //  bound to the current team is shared.
    if (isOpenACCTaskingDirective(DVar.DKind)) {
      DSAVarData DVarTemp;
      auto I = Iter, E = Stack.back().first.rend();
      do {
        ++I;
        // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables
        // Referenced in a Construct, implicitly determined, p.6]
        //  In a task construct, if no default clause is present, a variable
        //  whose data-sharing attribute is not determined by the rules above is
        //  firstprivate.
        DVarTemp = getDSA(I, D);
        if (DVarTemp.CKind != ACCC_shared) {
          DVar.RefExpr = nullptr;
          DVar.CKind = ACCC_firstprivate;
          return DVar;
        }
      } while (I != E && !isParallelOrTaskRegion(I->Directive));
      DVar.CKind =
          (DVarTemp.CKind == ACCC_unknown) ? ACCC_firstprivate : ACCC_shared;
      return DVar;
    }
  }
  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, implicitly determined, p.3]
  //  For constructs other than task, if no default clause is present, these
  //  variables inherit their data-sharing attributes from the enclosing
  //  context.
  return getDSA(++Iter, D);
}

Expr *DSAStackTy::addUniqueAligned(ValueDecl *D, Expr *NewDE) {
  assert(!isStackEmpty() && "Data sharing attributes stack is empty");
  D = getCanonicalDecl(D);
  auto &StackElem = Stack.back().first.back();
  auto It = StackElem.AlignedMap.find(D);
  if (It == StackElem.AlignedMap.end()) {
    assert(NewDE && "Unexpected nullptr expr to be added into aligned map");
    StackElem.AlignedMap[D] = NewDE;
    return nullptr;
  } else {
    assert(It->second && "Unexpected nullptr expr in the aligned map");
    return It->second;
  }
  return nullptr;
}

void DSAStackTy::addLoopControlVariable(ValueDecl *D, VarDecl *Capture) {
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty");
  D = getCanonicalDecl(D);
  auto &StackElem = Stack.back().first.back();
  StackElem.LCVMap.insert(
      {D, LCDeclInfo(StackElem.LCVMap.size() + 1, Capture)});
}

DSAStackTy::LCDeclInfo DSAStackTy::isLoopControlVariable(ValueDecl *D) {
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty");
  D = getCanonicalDecl(D);
  auto &StackElem = Stack.back().first.back();
  auto It = StackElem.LCVMap.find(D);
  if (It != StackElem.LCVMap.end())
    return It->second;
  return {0, nullptr};
}

DSAStackTy::LCDeclInfo DSAStackTy::isParentLoopControlVariable(ValueDecl *D) {
  assert(!isStackEmpty() && Stack.back().first.size() > 1 &&
         "Data-sharing attributes stack is empty");
  D = getCanonicalDecl(D);
  auto &StackElem = *std::next(Stack.back().first.rbegin());
  auto It = StackElem.LCVMap.find(D);
  if (It != StackElem.LCVMap.end())
    return It->second;
  return {0, nullptr};
}

ValueDecl *DSAStackTy::getParentLoopControlVariable(unsigned I) {
  assert(!isStackEmpty() && Stack.back().first.size() > 1 &&
         "Data-sharing attributes stack is empty");
  auto &StackElem = *std::next(Stack.back().first.rbegin());
  if (StackElem.LCVMap.size() < I)
    return nullptr;
  for (auto &Pair : StackElem.LCVMap)
    if (Pair.second.first == I)
      return Pair.first;
  return nullptr;
}

void DSAStackTy::addDSA(ValueDecl *D, Expr *E, OpenACCClauseKind A,
                        DeclRefExpr *PrivateCopy) {
  D = getCanonicalDecl(D);
  if (A == ACCC_threadprivate) {
    auto &Data = Threadprivates[D];
    Data.Attributes = A;
    Data.RefExpr.setPointer(E);
    Data.PrivateCopy = nullptr;
  } else {
    assert(!isStackEmpty() && "Data-sharing attributes stack is empty");
    auto &Data = Stack.back().first.back().SharingMap[D];
    assert(Data.Attributes == ACCC_unknown || (A == Data.Attributes) ||
           (A == ACCC_firstprivate && Data.Attributes == ACCC_lastprivate) ||
           (A == ACCC_lastprivate && Data.Attributes == ACCC_firstprivate) ||
           (isLoopControlVariable(D).first && A == ACCC_private));
    if (A == ACCC_lastprivate && Data.Attributes == ACCC_firstprivate) {
      Data.RefExpr.setInt(/*IntVal=*/true);
      return;
    }
    const bool IsLastprivate =
        A == ACCC_lastprivate || Data.Attributes == ACCC_lastprivate;
    Data.Attributes = A;
    Data.RefExpr.setPointerAndInt(E, IsLastprivate);
    Data.PrivateCopy = PrivateCopy;
    if (PrivateCopy) {
      auto &Data = Stack.back().first.back().SharingMap[PrivateCopy->getDecl()];
      Data.Attributes = A;
      Data.RefExpr.setPointerAndInt(PrivateCopy, IsLastprivate);
      Data.PrivateCopy = nullptr;
    }
  }
}

/// \brief Build a variable declaration for OpenACC loop iteration variable.
static VarDecl *buildVarDecl(Sema &SemaRef, SourceLocation Loc, QualType Type,
                             StringRef Name, const AttrVec *Attrs = nullptr) {
  DeclContext *DC = SemaRef.CurContext;
  IdentifierInfo *II = &SemaRef.PP.getIdentifierTable().get(Name);
  TypeSourceInfo *TInfo = SemaRef.Context.getTrivialTypeSourceInfo(Type, Loc);
  VarDecl *Decl =
      VarDecl::Create(SemaRef.Context, DC, Loc, Loc, II, Type, TInfo, SC_None);
  if (Attrs) {
    for (specific_attr_iterator<AlignedAttr> I(Attrs->begin()), E(Attrs->end());
         I != E; ++I)
      Decl->addAttr(*I);
  }
  Decl->setImplicit();
  return Decl;
}

static DeclRefExpr *buildDeclRefExpr(Sema &S, VarDecl *D, QualType Ty,
                                     SourceLocation Loc,
                                     bool RefersToCapture = false) {
  D->setReferenced();
  D->markUsed(S.Context);
  return DeclRefExpr::Create(S.getASTContext(), NestedNameSpecifierLoc(),
                             SourceLocation(), D, RefersToCapture, Loc, Ty,
                             VK_LValue);
}

void DSAStackTy::addTaskgroupReductionData(ValueDecl *D, SourceRange SR,
                                           BinaryOperatorKind BOK) {
  D = getCanonicalDecl(D);
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty");
  assert(
      Stack.back().first.back().SharingMap[D].Attributes == ACCC_reduction &&
      "Additional reduction info may be specified only for reduction items.");
  auto &ReductionData = Stack.back().first.back().ReductionMap[D];
  assert(ReductionData.ReductionRange.isInvalid() &&
         Stack.back().first.back().Directive == ACCD_taskgroup &&
         "Additional reduction info may be specified only once for reduction "
         "items.");
  ReductionData.set(BOK, SR);
  Expr *&TaskgroupReductionRef =
      Stack.back().first.back().TaskgroupReductionRef;
  if (!TaskgroupReductionRef) {
    auto *VD = buildVarDecl(SemaRef, SR.getBegin(),
                            SemaRef.Context.VoidPtrTy, ".task_red.");
    TaskgroupReductionRef =
        buildDeclRefExpr(SemaRef, VD, SemaRef.Context.VoidPtrTy, SR.getBegin());
  }
}

void DSAStackTy::addTaskgroupReductionData(ValueDecl *D, SourceRange SR,
                                           const Expr *ReductionRef) {
  D = getCanonicalDecl(D);
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty");
  assert(
      Stack.back().first.back().SharingMap[D].Attributes == ACCC_reduction &&
      "Additional reduction info may be specified only for reduction items.");
  auto &ReductionData = Stack.back().first.back().ReductionMap[D];
  assert(ReductionData.ReductionRange.isInvalid() &&
         Stack.back().first.back().Directive == ACCD_taskgroup &&
         "Additional reduction info may be specified only once for reduction "
         "items.");
  ReductionData.set(ReductionRef, SR);
  Expr *&TaskgroupReductionRef =
      Stack.back().first.back().TaskgroupReductionRef;
  if (!TaskgroupReductionRef) {
    auto *VD = buildVarDecl(SemaRef, SR.getBegin(), SemaRef.Context.VoidPtrTy,
                            ".task_red.");
    TaskgroupReductionRef =
        buildDeclRefExpr(SemaRef, VD, SemaRef.Context.VoidPtrTy, SR.getBegin());
  }
}

DSAStackTy::DSAVarData
DSAStackTy::getTopMostTaskgroupReductionData(ValueDecl *D, SourceRange &SR,
                                             BinaryOperatorKind &BOK,
                                             Expr *&TaskgroupDescriptor) {
  D = getCanonicalDecl(D);
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty.");
  if (Stack.back().first.empty())
      return DSAVarData();
  for (auto I = std::next(Stack.back().first.rbegin(), 1),
            E = Stack.back().first.rend();
       I != E; std::advance(I, 1)) {
    auto &Data = I->SharingMap[D];
    if (Data.Attributes != ACCC_reduction || I->Directive != ACCD_taskgroup)
      continue;
    auto &ReductionData = I->ReductionMap[D];
    if (!ReductionData.ReductionOp ||
        ReductionData.ReductionOp.is<const Expr *>())
      return DSAVarData();
    SR = ReductionData.ReductionRange;
    BOK = ReductionData.ReductionOp.get<ReductionData::BOKPtrType>();
    assert(I->TaskgroupReductionRef && "taskgroup reduction reference "
                                       "expression for the descriptor is not "
                                       "set.");
    TaskgroupDescriptor = I->TaskgroupReductionRef;
    return DSAVarData(ACCD_taskgroup, ACCC_reduction, Data.RefExpr.getPointer(),
                      Data.PrivateCopy, I->DefaultAttrLoc);
  }
  return DSAVarData();
}

DSAStackTy::DSAVarData
DSAStackTy::getTopMostTaskgroupReductionData(ValueDecl *D, SourceRange &SR,
                                             const Expr *&ReductionRef,
                                             Expr *&TaskgroupDescriptor) {
  D = getCanonicalDecl(D);
  assert(!isStackEmpty() && "Data-sharing attributes stack is empty.");
  if (Stack.back().first.empty())
      return DSAVarData();
  for (auto I = std::next(Stack.back().first.rbegin(), 1),
            E = Stack.back().first.rend();
       I != E; std::advance(I, 1)) {
    auto &Data = I->SharingMap[D];
    if (Data.Attributes != ACCC_reduction || I->Directive != ACCD_taskgroup)
      continue;
    auto &ReductionData = I->ReductionMap[D];
    if (!ReductionData.ReductionOp ||
        !ReductionData.ReductionOp.is<const Expr *>())
      return DSAVarData();
    SR = ReductionData.ReductionRange;
    ReductionRef = ReductionData.ReductionOp.get<const Expr *>();
    assert(I->TaskgroupReductionRef && "taskgroup reduction reference "
                                       "expression for the descriptor is not "
                                       "set.");
    TaskgroupDescriptor = I->TaskgroupReductionRef;
    return DSAVarData(ACCD_taskgroup, ACCC_reduction, Data.RefExpr.getPointer(),
                      Data.PrivateCopy, I->DefaultAttrLoc);
  }
  return DSAVarData();
}

bool DSAStackTy::isOpenACCLocal(VarDecl *D, StackTy::reverse_iterator Iter) {
  D = D->getCanonicalDecl();
  if (!isStackEmpty() && Stack.back().first.size() > 1) {
    reverse_iterator I = Iter, E = Stack.back().first.rend();
    Scope *TopScope = nullptr;
    while (I != E && !isParallelOrTaskRegion(I->Directive))
      ++I;
    if (I == E)
      return false;
    TopScope = I->CurScope ? I->CurScope->getParent() : nullptr;
    Scope *CurScope = getCurScope();
    while (CurScope != TopScope && !CurScope->isDeclScope(D))
      CurScope = CurScope->getParent();
    return CurScope != TopScope;
  }
  return false;
}

DSAStackTy::DSAVarData DSAStackTy::getTopDSA(ValueDecl *D, bool FromParent) {
  D = getCanonicalDecl(D);
  DSAVarData DVar;

  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, predetermined, p.1]
  //  Variables appearing in threadprivate directives are threadprivate.
  auto *VD = dyn_cast<VarDecl>(D);
  if ((VD && VD->getTLSKind() != VarDecl::TLS_None &&
       !(VD->hasAttr<ACCThreadPrivateDeclAttr>() && 
         SemaRef.getLangOpts().OpenACCUseTLS &&
         SemaRef.getASTContext().getTargetInfo().isTLSSupported())) ||
      (VD && VD->getStorageClass() == SC_Register &&
       VD->hasAttr<AsmLabelAttr>() && !VD->isLocalVarDecl())) {
    addDSA(D, buildDeclRefExpr(SemaRef, VD, D->getType().getNonReferenceType(),
                               D->getLocation()),
           ACCC_threadprivate);
  }
  auto TI = Threadprivates.find(D);
  if (TI != Threadprivates.end()) {
    DVar.RefExpr = TI->getSecond().RefExpr.getPointer();
    DVar.CKind = ACCC_threadprivate;
    return DVar;
  }
  else if (VD  && VD->hasAttr<ACCThreadPrivateDeclAttr>() ) {
    DVar.RefExpr = buildDeclRefExpr(
        SemaRef, VD, D->getType().getNonReferenceType(),
        VD->getAttr<ACCThreadPrivateDeclAttr>()->getLocation());
    DVar.CKind = ACCC_threadprivate;
    addDSA(D, DVar.RefExpr, ACCC_threadprivate);
  }

  if (isStackEmpty())
    // Not in OpenACC execution region and top scope was already checked.
    return DVar;

  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, predetermined, p.4]
  //  Static data members are shared.
  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, predetermined, p.7]
  //  Variables with static storage duration that are declared in a scope
  //  inside the construct are shared.
  auto &&MatchesAlways = [](OpenACCDirectiveKind) -> bool { return true; };
  if (VD && VD->isStaticDataMember()) {
    DSAVarData DVarTemp = hasDSA(D, isOpenACCPrivate, MatchesAlways, FromParent);
    if (DVarTemp.CKind != ACCC_unknown && DVarTemp.RefExpr)
      return DVar;

    DVar.CKind = ACCC_shared;
    return DVar;
  }

  QualType Type = D->getType().getNonReferenceType().getCanonicalType();
  bool IsConstant = Type.isConstant(SemaRef.getASTContext());
  Type = SemaRef.getASTContext().getBaseElementType(Type);
  // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
  // in a Construct, C/C++, predetermined, p.6]
  //  Variables with const qualified type having no mutable member are
  //  shared.
  CXXRecordDecl *RD =
      SemaRef.getLangOpts().CPlusPlus ? Type->getAsCXXRecordDecl() : nullptr;
  if (auto *CTSD = dyn_cast_or_null<ClassTemplateSpecializationDecl>(RD))
    if (auto *CTD = CTSD->getSpecializedTemplate())
      RD = CTD->getTemplatedDecl();
  if (IsConstant &&
      !(SemaRef.getLangOpts().CPlusPlus && RD && RD->hasDefinition() &&
        RD->hasMutableFields())) {
    // Variables with const-qualified type having no mutable member may be
    // listed in a firstprivate clause, even if they are static data members.
    DSAVarData DVarTemp = hasDSA(
        D, [](OpenACCClauseKind C) -> bool { return C == ACCC_firstprivate; },
        MatchesAlways, FromParent);
    if (DVarTemp.CKind == ACCC_firstprivate && DVarTemp.RefExpr)
      return DVarTemp;

    DVar.CKind = ACCC_shared;
    return DVar;
  }

  // Explicitly specified attributes and local variables with predetermined
  // attributes.
  auto I = Stack.back().first.rbegin();
  auto EndI = Stack.back().first.rend();
  if (FromParent && I != EndI)
    std::advance(I, 1);
  if (I->SharingMap.count(D)) {
    DVar.RefExpr = I->SharingMap[D].RefExpr.getPointer();
    DVar.PrivateCopy = I->SharingMap[D].PrivateCopy;
    DVar.CKind = I->SharingMap[D].Attributes;
    DVar.ImplicitDSALoc = I->DefaultAttrLoc;
    DVar.DKind = I->Directive;
  }

  return DVar;
}

DSAStackTy::DSAVarData DSAStackTy::getImplicitDSA(ValueDecl *D,
                                                  bool FromParent) {
  if (isStackEmpty()) {
    StackTy::reverse_iterator I;
    return getDSA(I, D);
  }
  D = getCanonicalDecl(D);
  auto StartI = Stack.back().first.rbegin();
  auto EndI = Stack.back().first.rend();
  if (FromParent && StartI != EndI)
    std::advance(StartI, 1);
  return getDSA(StartI, D);
}

DSAStackTy::DSAVarData
DSAStackTy::hasDSA(ValueDecl *D,
                   const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
                   const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
                   bool FromParent) {
  if (isStackEmpty())
    return {};
  D = getCanonicalDecl(D);
  auto I = Stack.back().first.rbegin();
  auto EndI = Stack.back().first.rend();
  if (FromParent && I != EndI)
    std::advance(I, 1);
  for (; I != EndI; std::advance(I, 1)) {
    if (!DPred(I->Directive) && !isParallelOrTaskRegion(I->Directive))
      continue;
    auto NewI = I;
    DSAVarData DVar = getDSA(NewI, D);
    if (I == NewI && CPred(DVar.CKind))
      return DVar;
  }
  return {};
}

DSAStackTy::DSAVarData DSAStackTy::hasInnermostDSA(
    ValueDecl *D, const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
    const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
    bool FromParent) {
  if (isStackEmpty())
    return {};
  D = getCanonicalDecl(D);
  auto StartI = Stack.back().first.rbegin();
  auto EndI = Stack.back().first.rend();
  if (FromParent && StartI != EndI)
    std::advance(StartI, 1);
  if (StartI == EndI || !DPred(StartI->Directive))
    return {};
  auto NewI = StartI;
  DSAVarData DVar = getDSA(NewI, D);
  return (NewI == StartI && CPred(DVar.CKind)) ? DVar : DSAVarData();
}

bool DSAStackTy::hasExplicitDSA(
    ValueDecl *D, const llvm::function_ref<bool(OpenACCClauseKind)> &CPred,
    unsigned Level, bool NotLastprivate) {
  if (isStackEmpty())
    return false;
  D = getCanonicalDecl(D);
  auto StartI = Stack.back().first.begin();
  auto EndI = Stack.back().first.end();
  if (std::distance(StartI, EndI) <= (int)Level)
    return false;
  std::advance(StartI, Level);
  return (StartI->SharingMap.count(D) > 0) &&
         StartI->SharingMap[D].RefExpr.getPointer() &&
         CPred(StartI->SharingMap[D].Attributes) &&
         (!NotLastprivate || !StartI->SharingMap[D].RefExpr.getInt());
}

bool DSAStackTy::hasExplicitDirective(
    const llvm::function_ref<bool(OpenACCDirectiveKind)> &DPred,
    unsigned Level) {
  if (isStackEmpty())
    return false;
  auto StartI = Stack.back().first.begin();
  auto EndI = Stack.back().first.end();
  if (std::distance(StartI, EndI) <= (int)Level)
    return false;
  std::advance(StartI, Level);
  return DPred(StartI->Directive);
}

bool DSAStackTy::hasDirective(
    const llvm::function_ref<bool(OpenACCDirectiveKind,
                                  const DeclarationNameInfo &, SourceLocation)>
        &DPred,
    bool FromParent) {
  // We look only in the enclosing region.
  if (isStackEmpty())
    return false;
  auto StartI = std::next(Stack.back().first.rbegin());
  auto EndI = Stack.back().first.rend();
  if (FromParent && StartI != EndI)
    StartI = std::next(StartI);
  for (auto I = StartI, EE = EndI; I != EE; ++I) {
    if (DPred(I->Directive, I->DirectiveName, I->ConstructLoc))
      return true;
  }
  return false;
}

void Sema::InitOpenACCDataSharingAttributesStack() {
  VarDataSharingAttributesStack = new DSAStackTy(*this);
}

#define DSAStack static_cast<DSAStackTy *>(VarDataSharingAttributesStack)

void Sema::pushOpenACCFunctionRegion() {
  DSAStack->pushFunction();
}

void Sema::popOpenACCFunctionRegion(const FunctionScopeInfo *OldFSI) {
  DSAStack->popFunction(OldFSI);
}

bool Sema::IsOpenACCCapturedByRef(ValueDecl *D, unsigned Level) {
  assert(LangOpts.OpenACC && "OpenACC is not allowed");

  auto &Ctx = getASTContext();
  bool IsByRef = true;

  // Find the directive that is associated with the provided scope.
  D = cast<ValueDecl>(D->getCanonicalDecl());
  auto Ty = D->getType();

  if (DSAStack->hasExplicitDirective(isOpenACCTargetExecutionDirective, Level)) {
    // This table summarizes how a given variable should be passed to the device
    // given its type and the clauses where it appears. This table is based on
    // the description in OpenACC 4.5 [2.10.4, target Construct] and
    // OpenACC 4.5 [2.15.5, Data-mapping Attribute Rules and Clauses].
    //
    // =========================================================================
    // | type |  defaultmap   | pvt | first | is_device_ptr |    map   | res.  |
    // |      |(tofrom:scalar)|     |  pvt  |               |          |       |
    // =========================================================================
    // | scl  |               |     |       |       -       |          | bycopy|
    // | scl  |               |  -  |   x   |       -       |     -    | bycopy|
    // | scl  |               |  x  |   -   |       -       |     -    | null  |
    // | scl  |       x       |     |       |       -       |          | byref |
    // | scl  |       x       |  -  |   x   |       -       |     -    | bycopy|
    // | scl  |       x       |  x  |   -   |       -       |     -    | null  |
    // | scl  |               |  -  |   -   |       -       |     x    | byref |
    // | scl  |       x       |  -  |   -   |       -       |     x    | byref |
    //
    // | agg  |      n.a.     |     |       |       -       |          | byref |
    // | agg  |      n.a.     |  -  |   x   |       -       |     -    | byref |
    // | agg  |      n.a.     |  x  |   -   |       -       |     -    | null  |
    // | agg  |      n.a.     |  -  |   -   |       -       |     x    | byref |
    // | agg  |      n.a.     |  -  |   -   |       -       |    x[]   | byref |
    //
    // | ptr  |      n.a.     |     |       |       -       |          | bycopy|
    // | ptr  |      n.a.     |  -  |   x   |       -       |     -    | bycopy|
    // | ptr  |      n.a.     |  x  |   -   |       -       |     -    | null  |
    // | ptr  |      n.a.     |  -  |   -   |       -       |     x    | byref |
    // | ptr  |      n.a.     |  -  |   -   |       -       |    x[]   | bycopy|
    // | ptr  |      n.a.     |  -  |   -   |       x       |          | bycopy|
    // | ptr  |      n.a.     |  -  |   -   |       x       |     x    | bycopy|
    // | ptr  |      n.a.     |  -  |   -   |       x       |    x[]   | bycopy|
    // =========================================================================
    // Legend:
    //  scl - scalar
    //  ptr - pointer
    //  agg - aggregate
    //  x - applies
    //  - - invalid in this combination
    //  [] - mapped with an array section
    //  byref - should be mapped by reference
    //  byval - should be mapped by value
    //  null - initialize a local variable to null on the device
    //
    // Observations:
    //  - All scalar declarations that show up in a map clause have to be passed
    //    by reference, because they may have been mapped in the enclosing data
    //    environment.
    //  - If the scalar value does not fit the size of uintptr, it has to be
    //    passed by reference, regardless the result in the table above.
    //  - For pointers mapped by value that have either an implicit map or an
    //    array section, the runtime library may pass the NULL value to the
    //    device instead of the value passed to it by the compiler.

    if (Ty->isReferenceType())
      Ty = Ty->castAs<ReferenceType>()->getPointeeType();

    // Locate map clauses and see if the variable being captured is referred to
    // in any of those clauses. Here we only care about variables, not fields,
    // because fields are part of aggregates.
    bool IsVariableUsedInMapClause = false;
    bool IsVariableAssociatedWithSection = false;

    DSAStack->checkMappableExprComponentListsForDeclAtLevel(
        D, Level, [&](ACCClauseMappableExprCommon::MappableExprComponentListRef
                MapExprComponents,
            OpenACCClauseKind WhereFoundClauseKind) {
          // Only the map clause information influences how a variable is
          // captured. E.g. is_device_ptr does not require changing the default
          // behavior.
          if (WhereFoundClauseKind != ACCC_map)
            return false;

          auto EI = MapExprComponents.rbegin();
          auto EE = MapExprComponents.rend();

          assert(EI != EE && "Invalid map expression!");

          if (isa<DeclRefExpr>(EI->getAssociatedExpression()))
            IsVariableUsedInMapClause |= EI->getAssociatedDeclaration() == D;

          ++EI;
          if (EI == EE)
            return false;

          if (isa<ArraySubscriptExpr>(EI->getAssociatedExpression()) ||
              isa<ACCArraySectionExpr>(EI->getAssociatedExpression()) ||
              isa<MemberExpr>(EI->getAssociatedExpression())) {
            IsVariableAssociatedWithSection = true;
            // There is nothing more we need to know about this variable.
            return true;
          }

          // Keep looking for more map info.
          return false;
        });

    if (IsVariableUsedInMapClause) {
      // If variable is identified in a map clause it is always captured by
      // reference except if it is a pointer that is dereferenced somehow.
      IsByRef = !(Ty->isPointerType() && IsVariableAssociatedWithSection);
    } else {
      // By default, all the data that has a scalar type is mapped by copy
      // (except for reduction variables).
      IsByRef =
          !Ty->isScalarType() ||
          DSAStack->getDefaultDMAAtLevel(Level) == DMA_tofrom_scalar ||
          DSAStack->hasExplicitDSA(
              D, [](OpenACCClauseKind K) { return K == ACCC_reduction; }, Level);
    }
  }

  if (IsByRef && Ty.getNonReferenceType()->isScalarType()) {
    IsByRef =
        !DSAStack->hasExplicitDSA(
            D,
            [](OpenACCClauseKind K) -> bool { return K == ACCC_firstprivate; },
            Level, /*NotLastprivate=*/true) &&
        // If the variable is artificial and must be captured by value - try to
        // capture by value.
        !(isa<ACCCapturedExprDecl>(D) && !D->hasAttr<ACCCaptureNoInitAttr>() &&
          !cast<ACCCapturedExprDecl>(D)->getInit()->isGLValue());
  }

  // When passing data by copy, we need to make sure it fits the uintptr size
  // and alignment, because the runtime library only deals with uintptr types.
  // If it does not fit the uintptr size, we need to pass the data by reference
  // instead.
  if (!IsByRef &&
      (Ctx.getTypeSizeInChars(Ty) >
           Ctx.getTypeSizeInChars(Ctx.getUIntPtrType()) ||
       Ctx.getDeclAlign(D) > Ctx.getTypeAlignInChars(Ctx.getUIntPtrType()))) {
    IsByRef = true;
  }

  return IsByRef;
}

unsigned Sema::getOpenACCNestingLevel() const {
  assert(getLangOpts().OpenACC);
  return DSAStack->getNestingLevel();
}

bool Sema::isInOpenACCTargetExecutionDirective() const {
  return (isOpenACCTargetExecutionDirective(DSAStack->getCurrentDirective()) &&
          !DSAStack->isClauseParsingMode()) ||
         DSAStack->hasDirective(
             [](OpenACCDirectiveKind K, const DeclarationNameInfo &,
                SourceLocation) -> bool {
               return isOpenACCTargetExecutionDirective(K);
             },
             false);
}

VarDecl *Sema::IsOpenACCCapturedDecl(ValueDecl *D) {
  assert(LangOpts.OpenACC && "OpenACC is not allowed");
  D = getCanonicalDecl(D);

  // If we are attempting to capture a global variable in a directive with
  // 'target' we return true so that this global is also mapped to the device.
  //
  // FIXME: If the declaration is enclosed in a 'declare target' directive,
  // then it should not be captured. Therefore, an extra check has to be
  // inserted here once support for 'declare target' is added.
  //
  auto *VD = dyn_cast<VarDecl>(D);
  if (VD && !VD->hasLocalStorage() && isInOpenACCTargetExecutionDirective())
    return VD;

  if (DSAStack->getCurrentDirective() != ACCD_unknown &&
      (!DSAStack->isClauseParsingMode() ||
       DSAStack->getParentDirective() != ACCD_unknown)) {
    auto &&Info = DSAStack->isLoopControlVariable(D);
    if (Info.first ||
        (VD && VD->hasLocalStorage() &&
         isParallelOrTaskRegion(DSAStack->getCurrentDirective())) ||
        (VD && DSAStack->isForceVarCapturing()))
      return VD ? VD : Info.second;
    auto DVarPrivate = DSAStack->getTopDSA(D, DSAStack->isClauseParsingMode());
    if (DVarPrivate.CKind != ACCC_unknown && isOpenACCPrivate(DVarPrivate.CKind))
      return VD ? VD : cast<VarDecl>(DVarPrivate.PrivateCopy->getDecl());
    DVarPrivate = DSAStack->hasDSA(
        D, isOpenACCPrivate, [](OpenACCDirectiveKind) -> bool { return true; },
        DSAStack->isClauseParsingMode());
    if (DVarPrivate.CKind != ACCC_unknown)
      return VD ? VD : cast<VarDecl>(DVarPrivate.PrivateCopy->getDecl());
  }
  return nullptr;
}

void Sema::adjustOpenACCTargetScopeIndex(unsigned &FunctionScopesIndex,
                                        unsigned Level) const {
  SmallVector<OpenACCDirectiveKind, 4> Regions;
  getOpenACCCaptureRegions(Regions, DSAStack->getDirective(Level));
  FunctionScopesIndex -= Regions.size();
}

bool Sema::isOpenACCPrivateDecl(ValueDecl *D, unsigned Level) {
  assert(LangOpts.OpenACC && "OpenACC is not allowed");
  return DSAStack->hasExplicitDSA(
             D, [](OpenACCClauseKind K) -> bool { return K == ACCC_private; },
             Level) ||
         (DSAStack->isClauseParsingMode() &&
          DSAStack->getClauseParsingMode() == ACCC_private) ||
         // Consider taskgroup reduction descriptor variable a private to avoid
         // possible capture in the region.
         (DSAStack->hasExplicitDirective(
              [](OpenACCDirectiveKind K) { return K == ACCD_taskgroup; },
              Level) &&
          DSAStack->isTaskgroupReductionRef(D, Level));
}

void Sema::setOpenACCCaptureKind(FieldDecl *FD, ValueDecl *D, unsigned Level) {
  assert(LangOpts.OpenACC && "OpenACC is not allowed");
  D = getCanonicalDecl(D);
  OpenACCClauseKind ACCC = ACCC_unknown;
  for (unsigned I = DSAStack->getNestingLevel() + 1; I > Level; --I) {
    const unsigned NewLevel = I - 1;
    if (DSAStack->hasExplicitDSA(D,
                                 [&ACCC](const OpenACCClauseKind K) {
                                   if (isOpenACCPrivate(K)) {
                                     ACCC = K;
                                     return true;
                                   }
                                   return false;
                                 },
                                 NewLevel))
      break;
    if (DSAStack->checkMappableExprComponentListsForDeclAtLevel(
            D, NewLevel,
            [](ACCClauseMappableExprCommon::MappableExprComponentListRef,
               OpenACCClauseKind) { return true; })) {
      ACCC = ACCC_map;
      break;
    }
    if (DSAStack->hasExplicitDirective(isOpenACCTargetExecutionDirective,
                                       NewLevel)) {
      ACCC = ACCC_firstprivate;
      break;
    }
  }
  if (ACCC != ACCC_unknown)
    FD->addAttr(ACCCaptureKindAttr::CreateImplicit(Context, ACCC));
}

bool Sema::isOpenACCTargetCapturedDecl(ValueDecl *D, unsigned Level) {
  assert(LangOpts.OpenACC && "OpenACC is not allowed");
  // Return true if the current level is no longer enclosed in a target region.

  auto *VD = dyn_cast<VarDecl>(D);
  return VD && !VD->hasLocalStorage() &&
         DSAStack->hasExplicitDirective(isOpenACCTargetExecutionDirective,
                                        Level);
}

void Sema::DestroyOpenACCDataSharingAttributesStack() { delete DSAStack; }

void Sema::StartOpenACCDSABlock(OpenACCDirectiveKind DKind,
                               const DeclarationNameInfo &DirName,
                               Scope *CurScope, SourceLocation Loc) {
  DSAStack->push(DKind, DirName, CurScope, Loc);
  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);
}

void Sema::StartOpenACCClause(OpenACCClauseKind K) {
  DSAStack->setClauseParsingMode(K);
}

void Sema::EndOpenACCClause() {
  DSAStack->setClauseParsingMode(/*K=*/ACCC_unknown);
}

void Sema::EndOpenACCDSABlock(Stmt *CurDirective) {
  // OpenACC [2.14.3.5, Restrictions, C/C++, p.1]
  //  A variable of class type (or array thereof) that appears in a lastprivate
  //  clause requires an accessible, unambiguous default constructor for the
  //  class type, unless the list item is also specified in a firstprivate
  //  clause.
  if (auto *D = dyn_cast_or_null<ACCExecutableDirective>(CurDirective)) {
    for (auto *C : D->clauses()) {
      if (auto *Clause = dyn_cast<ACCLastprivateClause>(C)) {
        SmallVector<Expr *, 8> PrivateCopies;
        for (auto *DE : Clause->varlists()) {
          if (DE->isValueDependent() || DE->isTypeDependent()) {
            PrivateCopies.push_back(nullptr);
            continue;
          }
          auto *DRE = cast<DeclRefExpr>(DE->IgnoreParens());
          VarDecl *VD = cast<VarDecl>(DRE->getDecl());
          QualType Type = VD->getType().getNonReferenceType();
          auto DVar = DSAStack->getTopDSA(VD, false);
          if (DVar.CKind == ACCC_lastprivate) {
            // Generate helper private variable and initialize it with the
            // default value. The address of the original variable is replaced
            // by the address of the new private variable in CodeGen. This new
            // variable is not added to IdResolver, so the code in the OpenACC
            // region uses original variable for proper diagnostics.
            auto *VDPrivate = buildVarDecl(
                *this, DE->getExprLoc(), Type.getUnqualifiedType(),
                VD->getName(), VD->hasAttrs() ? &VD->getAttrs() : nullptr);
            ActOnUninitializedDecl(VDPrivate);
            if (VDPrivate->isInvalidDecl())
              continue;
            PrivateCopies.push_back(buildDeclRefExpr(
                *this, VDPrivate, DE->getType(), DE->getExprLoc()));
          } else {
            // The variable is also a firstprivate, so initialization sequence
            // for private copy is generated already.
            PrivateCopies.push_back(nullptr);
          }
        }
        // Set initializers to private copies if no errors were found.
        if (PrivateCopies.size() == Clause->varlist_size())
          Clause->setPrivateCopies(PrivateCopies);
      }
    }
  }

  DSAStack->pop();
  DiscardCleanupsInEvaluationContext();
  PopExpressionEvaluationContext();
}

static bool FinishOpenACCLinearClause(ACCLinearClause &Clause, DeclRefExpr *IV,
                                     Expr *NumIterations, Sema &SemaRef,
                                     Scope *S, DSAStackTy *Stack);

namespace {

class VarDeclFilterCCC : public CorrectionCandidateCallback {
private:
  Sema &SemaRef;

public:
  explicit VarDeclFilterCCC(Sema &S) : SemaRef(S) {}
  bool ValidateCandidate(const TypoCorrection &Candidate) override {
    NamedDecl *ND = Candidate.getCorrectionDecl();
    if (auto *VD = dyn_cast_or_null<VarDecl>(ND)) {
      return VD->hasGlobalStorage() &&
             SemaRef.isDeclInScope(ND, SemaRef.getCurLexicalContext(),
                                   SemaRef.getCurScope());
    }
    return false;
  }
};

class VarOrFuncDeclFilterCCC : public CorrectionCandidateCallback {
private:
  Sema &SemaRef;

public:
  explicit VarOrFuncDeclFilterCCC(Sema &S) : SemaRef(S) {}
  bool ValidateCandidate(const TypoCorrection &Candidate) override {
    NamedDecl *ND = Candidate.getCorrectionDecl();
    if (ND && (isa<VarDecl>(ND) || isa<FunctionDecl>(ND))) {
      return SemaRef.isDeclInScope(ND, SemaRef.getCurLexicalContext(),
                                   SemaRef.getCurScope());
    }
    return false;
  }
};

} // namespace

ExprResult Sema::ActOnOpenACCIdExpression(Scope *CurScope,
                                         CXXScopeSpec &ScopeSpec,
                                         const DeclarationNameInfo &Id) {
  LookupResult Lookup(*this, Id, LookupOrdinaryName);
  LookupParsedName(Lookup, CurScope, &ScopeSpec, true);

  if (Lookup.isAmbiguous())
    return ExprError();

  VarDecl *VD;
  if (!Lookup.isSingleResult()) {
    if (TypoCorrection Corrected = CorrectTypo(
            Id, LookupOrdinaryName, CurScope, nullptr,
            llvm::make_unique<VarDeclFilterCCC>(*this), CTK_ErrorRecovery)) {
      diagnoseTypo(Corrected,
                   PDiag(Lookup.empty()
                             ? diag::err_undeclared_var_use_suggest
                             : diag::err_acc_expected_var_arg_suggest)
                       << Id.getName());
      VD = Corrected.getCorrectionDeclAs<VarDecl>();
    } else {
      Diag(Id.getLoc(), Lookup.empty() ? diag::err_undeclared_var_use
                                       : diag::err_acc_expected_var_arg)
          << Id.getName();
      return ExprError();
    }
  } else {
    if (!(VD = Lookup.getAsSingle<VarDecl>())) {
      Diag(Id.getLoc(), diag::err_acc_expected_var_arg) << Id.getName();
      Diag(Lookup.getFoundDecl()->getLocation(), diag::note_declared_at);
      return ExprError();
    }
  }
  Lookup.suppressDiagnostics();

  // OpenACC [2.9.2, Syntax, C/C++]
  //   Variables must be file-scope, namespace-scope, or static block-scope.
  if (!VD->hasGlobalStorage()) {
    Diag(Id.getLoc(), diag::err_acc_global_var_arg)
        << getOpenACCDirectiveName(ACCD_threadprivate) << !VD->isStaticLocal();
    bool IsDecl =
        VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
    Diag(VD->getLocation(),
         IsDecl ? diag::note_previous_decl : diag::note_defined_here)
        << VD;
    return ExprError();
  }

  VarDecl *CanonicalVD = VD->getCanonicalDecl();
  NamedDecl *ND = cast<NamedDecl>(CanonicalVD);
  // OpenACC [2.9.2, Restrictions, C/C++, p.2]
  //   A threadprivate directive for file-scope variables must appear outside
  //   any definition or declaration.
  if (CanonicalVD->getDeclContext()->isTranslationUnit() &&
      !getCurLexicalContext()->isTranslationUnit()) {
    Diag(Id.getLoc(), diag::err_acc_var_scope)
        << getOpenACCDirectiveName(ACCD_threadprivate) << VD;
    bool IsDecl =
        VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
    Diag(VD->getLocation(),
         IsDecl ? diag::note_previous_decl : diag::note_defined_here)
        << VD;
    return ExprError();
  }
  // OpenACC [2.9.2, Restrictions, C/C++, p.3]
  //   A threadprivate directive for static class member variables must appear
  //   in the class definition, in the same scope in which the member
  //   variables are declared.
  if (CanonicalVD->isStaticDataMember() &&
      !CanonicalVD->getDeclContext()->Equals(getCurLexicalContext())) {
    Diag(Id.getLoc(), diag::err_acc_var_scope)
        << getOpenACCDirectiveName(ACCD_threadprivate) << VD;
    bool IsDecl =
        VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
    Diag(VD->getLocation(),
         IsDecl ? diag::note_previous_decl : diag::note_defined_here)
        << VD;
    return ExprError();
  }
  // OpenACC [2.9.2, Restrictions, C/C++, p.4]
  //   A threadprivate directive for namespace-scope variables must appear
  //   outside any definition or declaration other than the namespace
  //   definition itself.
  if (CanonicalVD->getDeclContext()->isNamespace() &&
      (!getCurLexicalContext()->isFileContext() ||
       !getCurLexicalContext()->Encloses(CanonicalVD->getDeclContext()))) {
    Diag(Id.getLoc(), diag::err_acc_var_scope)
        << getOpenACCDirectiveName(ACCD_threadprivate) << VD;
    bool IsDecl =
        VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
    Diag(VD->getLocation(),
         IsDecl ? diag::note_previous_decl : diag::note_defined_here)
        << VD;
    return ExprError();
  }
  // OpenACC [2.9.2, Restrictions, C/C++, p.6]
  //   A threadprivate directive for static block-scope variables must appear
  //   in the scope of the variable and not in a nested scope.
  if (CanonicalVD->isStaticLocal() && CurScope &&
      !isDeclInScope(ND, getCurLexicalContext(), CurScope)) {
    Diag(Id.getLoc(), diag::err_acc_var_scope)
        << getOpenACCDirectiveName(ACCD_threadprivate) << VD;
    bool IsDecl =
        VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
    Diag(VD->getLocation(),
         IsDecl ? diag::note_previous_decl : diag::note_defined_here)
        << VD;
    return ExprError();
  }

  // OpenACC [2.9.2, Restrictions, C/C++, p.2-6]
  //   A threadprivate directive must lexically precede all references to any
  //   of the variables in its list.
  if (VD->isUsed() && !DSAStack->isThreadPrivate(VD)) {
    Diag(Id.getLoc(), diag::err_acc_var_used)
        << getOpenACCDirectiveName(ACCD_threadprivate) << VD;
    return ExprError();
  }

  QualType ExprType = VD->getType().getNonReferenceType();
  return DeclRefExpr::Create(Context, NestedNameSpecifierLoc(),
                             SourceLocation(), VD,
                             /*RefersToEnclosingVariableOrCapture=*/false,
                             Id.getLoc(), ExprType, VK_LValue);
}

Sema::DeclGroupPtrTy
Sema::ActOnOpenACCThreadprivateDirective(SourceLocation Loc,
                                        ArrayRef<Expr *> VarList) {
  if (ACCThreadPrivateDecl *D = CheckACCThreadPrivateDecl(Loc, VarList)) {
    CurContext->addDecl(D);
    return DeclGroupPtrTy::make(DeclGroupRef(D));
  }
  return nullptr;
}

namespace {
class LocalVarRefChecker : public ConstStmtVisitor<LocalVarRefChecker, bool> {
  Sema &SemaRef;

public:
  bool VisitDeclRefExpr(const DeclRefExpr *E) {
    if (auto *VD = dyn_cast<VarDecl>(E->getDecl())) {
      if (VD->hasLocalStorage()) {
        SemaRef.Diag(E->getLocStart(),
                     diag::err_acc_local_var_in_threadprivate_init)
            << E->getSourceRange();
        SemaRef.Diag(VD->getLocation(), diag::note_defined_here)
            << VD << VD->getSourceRange();
        return true;
      }
    }
    return false;
  }
  bool VisitStmt(const Stmt *S) {
    for (auto Child : S->children()) {
      if (Child && Visit(Child))
        return true;
    }
    return false;
  }
  explicit LocalVarRefChecker(Sema &SemaRef) : SemaRef(SemaRef) {}
};
} // namespace

ACCThreadPrivateDecl *
Sema::CheckACCThreadPrivateDecl(SourceLocation Loc, ArrayRef<Expr *> VarList) {
  SmallVector<Expr *, 8> Vars;
  for (auto &RefExpr : VarList) {
    DeclRefExpr *DE = cast<DeclRefExpr>(RefExpr);
    VarDecl *VD = cast<VarDecl>(DE->getDecl());
    SourceLocation ILoc = DE->getExprLoc();

    // Mark variable as used.
    VD->setReferenced();
    VD->markUsed(Context);

    QualType QType = VD->getType();
    if (QType->isDependentType() || QType->isInstantiationDependentType()) {
      // It will be analyzed later.
      Vars.push_back(DE);
      continue;
    }

    // OpenACC [2.9.2, Restrictions, C/C++, p.10]
    //   A threadprivate variable must not have an incomplete type.
    if (RequireCompleteType(ILoc, VD->getType(),
                            diag::err_acc_threadprivate_incomplete_type)) {
      continue;
    }

    // OpenACC [2.9.2, Restrictions, C/C++, p.10]
    //   A threadprivate variable must not have a reference type.
    if (VD->getType()->isReferenceType()) {
      Diag(ILoc, diag::err_acc_ref_type_arg)
          << getOpenACCDirectiveName(ACCD_threadprivate) << VD->getType();
      bool IsDecl =
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(VD->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << VD;
      continue;
    }

    // Check if this is a TLS variable. If TLS is not being supported, produce
    // the corresponding diagnostic.
    if ((VD->getTLSKind() != VarDecl::TLS_None &&
         !(VD->hasAttr<ACCThreadPrivateDeclAttr>() &&
           getLangOpts().OpenACCUseTLS &&
           getASTContext().getTargetInfo().isTLSSupported())) ||
        (VD->getStorageClass() == SC_Register && VD->hasAttr<AsmLabelAttr>() &&
         !VD->isLocalVarDecl())) {
      Diag(ILoc, diag::err_acc_var_thread_local)
          << VD << ((VD->getTLSKind() != VarDecl::TLS_None) ? 0 : 1);
      bool IsDecl =
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(VD->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << VD;
      continue;
    }

    // Check if initial value of threadprivate variable reference variable with
    // local storage (it is not supported by runtime).
    if (auto Init = VD->getAnyInitializer()) {
      LocalVarRefChecker Checker(*this);
      if (Checker.Visit(Init))
        continue;
    }

    Vars.push_back(RefExpr);
    DSAStack->addDSA(VD, DE, ACCC_threadprivate);
    VD->addAttr(ACCThreadPrivateDeclAttr::CreateImplicit(
        Context, SourceRange(Loc, Loc)));
    if (auto *ML = Context.getASTMutationListener())
      ML->DeclarationMarkedOpenACCThreadPrivate(VD);
  }
  ACCThreadPrivateDecl *D = nullptr;
  if (!Vars.empty()) {
    D = ACCThreadPrivateDecl::Create(Context, getCurLexicalContext(), Loc,
                                     Vars);
    D->setAccess(AS_public);
  }
  return D;
}

static void ReportOriginalDSA(Sema &SemaRef, DSAStackTy *Stack,
                              const ValueDecl *D, DSAStackTy::DSAVarData DVar,
                              bool IsLoopIterVar = false) {
  if (DVar.RefExpr) {
    SemaRef.Diag(DVar.RefExpr->getExprLoc(), diag::note_acc_explicit_dsa)
        << getOpenACCClauseName(DVar.CKind);
    return;
  }
  enum {
    PDSA_StaticMemberShared,
    PDSA_StaticLocalVarShared,
    PDSA_LoopIterVarPrivate,
    PDSA_LoopIterVarLinear,
    PDSA_LoopIterVarLastprivate,
    PDSA_ConstVarShared,
    PDSA_GlobalVarShared,
    PDSA_TaskVarFirstprivate,
    PDSA_LocalVarPrivate,
    PDSA_Implicit
  } Reason = PDSA_Implicit;
  bool ReportHint = false;
  auto ReportLoc = D->getLocation();
  auto *VD = dyn_cast<VarDecl>(D);
  if (IsLoopIterVar) {
    if (DVar.CKind == ACCC_private)
      Reason = PDSA_LoopIterVarPrivate;
    else if (DVar.CKind == ACCC_lastprivate)
      Reason = PDSA_LoopIterVarLastprivate;
    else
      Reason = PDSA_LoopIterVarLinear;
  } else if (isOpenACCTaskingDirective(DVar.DKind) &&
             DVar.CKind == ACCC_firstprivate) {
    Reason = PDSA_TaskVarFirstprivate;
    ReportLoc = DVar.ImplicitDSALoc;
  } else if (VD && VD->isStaticLocal())
    Reason = PDSA_StaticLocalVarShared;
  else if (VD && VD->isStaticDataMember())
    Reason = PDSA_StaticMemberShared;
  else if (VD && VD->isFileVarDecl())
    Reason = PDSA_GlobalVarShared;
  else if (D->getType().isConstant(SemaRef.getASTContext()))
    Reason = PDSA_ConstVarShared;
  else if (VD && VD->isLocalVarDecl() && DVar.CKind == ACCC_private) {
    ReportHint = true;
    Reason = PDSA_LocalVarPrivate;
  }
  if (Reason != PDSA_Implicit) {
    SemaRef.Diag(ReportLoc, diag::note_acc_predetermined_dsa)
        << Reason << ReportHint
        << getOpenACCDirectiveName(Stack->getCurrentDirective());
  } else if (DVar.ImplicitDSALoc.isValid()) {
    SemaRef.Diag(DVar.ImplicitDSALoc, diag::note_acc_implicit_dsa)
        << getOpenACCClauseName(DVar.CKind);
  }
}

namespace {
class DSAAttrChecker : public StmtVisitor<DSAAttrChecker, void> {
  DSAStackTy *Stack;
  Sema &SemaRef;
  bool ErrorFound;
  CapturedStmt *CS;
  llvm::SmallVector<Expr *, 8> ImplicitFirstprivate;
  llvm::SmallVector<Expr *, 8> ImplicitMap;
  llvm::DenseMap<ValueDecl *, Expr *> VarsWithInheritedDSA;
  llvm::DenseSet<ValueDecl *> ImplicitDeclarations;

public:
  void VisitDeclRefExpr(DeclRefExpr *E) {
    if (E->isTypeDependent() || E->isValueDependent() ||
        E->containsUnexpandedParameterPack() || E->isInstantiationDependent())
      return;
    if (auto *VD = dyn_cast<VarDecl>(E->getDecl())) {
      VD = VD->getCanonicalDecl();
      // Skip internally declared variables.
      if (VD->hasLocalStorage() && !CS->capturesVariable(VD))
        return;

      auto DVar = Stack->getTopDSA(VD, false);
      // Check if the variable has explicit DSA set and stop analysis if it so.
      if (DVar.RefExpr || !ImplicitDeclarations.insert(VD).second)
        return;

      // Skip internally declared static variables.
      if (VD->hasGlobalStorage() && !CS->capturesVariable(VD))
        return;

      auto ELoc = E->getExprLoc();
      auto DKind = Stack->getCurrentDirective();
      // The default(none) clause requires that each variable that is referenced
      // in the construct, and does not have a predetermined data-sharing
      // attribute, must have its data-sharing attribute explicitly determined
      // by being listed in a data-sharing attribute clause.
      if (DVar.CKind == ACCC_unknown && Stack->getDefaultDSA() == DSA_none &&
          isParallelOrTaskRegion(DKind) &&
          VarsWithInheritedDSA.count(VD) == 0) {
        VarsWithInheritedDSA[VD] = E;
        return;
      }

      if (isOpenACCTargetExecutionDirective(DKind) &&
          !Stack->isLoopControlVariable(VD).first) {
        if (!Stack->checkMappableExprComponentListsForDecl(
                VD, /*CurrentRegionOnly=*/true,
                [](ACCClauseMappableExprCommon::MappableExprComponentListRef
                       StackComponents,
                   OpenACCClauseKind) {
                  // Variable is used if it has been marked as an array, array
                  // section or the variable iself.
                  return StackComponents.size() == 1 ||
                         std::all_of(
                             std::next(StackComponents.rbegin()),
                             StackComponents.rend(),
                             [](const ACCClauseMappableExprCommon::
                                    MappableComponent &MC) {
                               return MC.getAssociatedDeclaration() ==
                                          nullptr &&
                                      (isa<ACCArraySectionExpr>(
                                           MC.getAssociatedExpression()) ||
                                       isa<ArraySubscriptExpr>(
                                           MC.getAssociatedExpression()));
                             });
                })) {
          bool IsFirstprivate = false;
          // By default lambdas are captured as firstprivates.
          if (const auto *RD =
                  VD->getType().getNonReferenceType()->getAsCXXRecordDecl())
            IsFirstprivate = RD->isLambda();
          IsFirstprivate =
              IsFirstprivate ||
              (VD->getType().getNonReferenceType()->isScalarType() &&
               Stack->getDefaultDMA() != DMA_tofrom_scalar);
          if (IsFirstprivate)
            ImplicitFirstprivate.emplace_back(E);
          else
            ImplicitMap.emplace_back(E);
          return;
        }
      }

      // OpenACC [2.9.3.6, Restrictions, p.2]
      //  A list item that appears in a reduction clause of the innermost
      //  enclosing worksharing or parallel construct may not be accessed in an
      //  explicit task.
      DVar = Stack->hasInnermostDSA(
          VD, [](OpenACCClauseKind C) -> bool { return C == ACCC_reduction; },
          [](OpenACCDirectiveKind K) -> bool {
            return isOpenACCParallelDirective(K) ||
                   isOpenACCWorksharingDirective(K) || isOpenACCTeamsDirective(K);
          },
          /*FromParent=*/true);
      if (isOpenACCTaskingDirective(DKind) && DVar.CKind == ACCC_reduction) {
        ErrorFound = true;
        SemaRef.Diag(ELoc, diag::err_acc_reduction_in_task);
        ReportOriginalDSA(SemaRef, Stack, VD, DVar);
        return;
      }

      // Define implicit data-sharing attributes for task.
      DVar = Stack->getImplicitDSA(VD, false);
      if (isOpenACCTaskingDirective(DKind) && DVar.CKind != ACCC_shared &&
          !Stack->isLoopControlVariable(VD).first)
        ImplicitFirstprivate.push_back(E);
    }
  }
  void VisitMemberExpr(MemberExpr *E) {
    if (E->isTypeDependent() || E->isValueDependent() ||
        E->containsUnexpandedParameterPack() || E->isInstantiationDependent())
      return;
    auto *FD = dyn_cast<FieldDecl>(E->getMemberDecl());
    OpenACCDirectiveKind DKind = Stack->getCurrentDirective();
    if (isa<CXXThisExpr>(E->getBase()->IgnoreParens())) {
      if (!FD)
        return;
      auto DVar = Stack->getTopDSA(FD, false);
      // Check if the variable has explicit DSA set and stop analysis if it
      // so.
      if (DVar.RefExpr || !ImplicitDeclarations.insert(FD).second)
        return;

      if (isOpenACCTargetExecutionDirective(DKind) &&
          !Stack->isLoopControlVariable(FD).first &&
          !Stack->checkMappableExprComponentListsForDecl(
              FD, /*CurrentRegionOnly=*/true,
              [](ACCClauseMappableExprCommon::MappableExprComponentListRef
                     StackComponents,
                 OpenACCClauseKind) {
                return isa<CXXThisExpr>(
                    cast<MemberExpr>(
                        StackComponents.back().getAssociatedExpression())
                        ->getBase()
                        ->IgnoreParens());
              })) {
        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C/C++, p.3]
        //  A bit-field cannot appear in a map clause.
        //
        if (FD->isBitField())
          return;
        ImplicitMap.emplace_back(E);
        return;
      }

      auto ELoc = E->getExprLoc();
      // OpenACC [2.9.3.6, Restrictions, p.2]
      //  A list item that appears in a reduction clause of the innermost
      //  enclosing worksharing or parallel construct may not be accessed in
      //  an  explicit task.
      DVar = Stack->hasInnermostDSA(
          FD, [](OpenACCClauseKind C) -> bool { return C == ACCC_reduction; },
          [](OpenACCDirectiveKind K) -> bool {
            return isOpenACCParallelDirective(K) ||
                   isOpenACCWorksharingDirective(K) || isOpenACCTeamsDirective(K);
          },
          /*FromParent=*/true);
      if (isOpenACCTaskingDirective(DKind) && DVar.CKind == ACCC_reduction) {
        ErrorFound = true;
        SemaRef.Diag(ELoc, diag::err_acc_reduction_in_task);
        ReportOriginalDSA(SemaRef, Stack, FD, DVar);
        return;
      }

      // Define implicit data-sharing attributes for task.
      DVar = Stack->getImplicitDSA(FD, false);
      if (isOpenACCTaskingDirective(DKind) && DVar.CKind != ACCC_shared &&
          !Stack->isLoopControlVariable(FD).first)
        ImplicitFirstprivate.push_back(E);
      return;
    }
    if (isOpenACCTargetExecutionDirective(DKind)) {
      ACCClauseMappableExprCommon::MappableExprComponentList CurComponents;
      if (!CheckMapClauseExpressionBase(SemaRef, E, CurComponents, ACCC_map,
                                        /*NoDiagnose=*/true))
        return;
      auto *VD = cast<ValueDecl>(
          CurComponents.back().getAssociatedDeclaration()->getCanonicalDecl());
      if (!Stack->checkMappableExprComponentListsForDecl(
              VD, /*CurrentRegionOnly=*/true,
              [&CurComponents](
                  ACCClauseMappableExprCommon::MappableExprComponentListRef
                      StackComponents,
                  OpenACCClauseKind) {
                auto CCI = CurComponents.rbegin();
                auto CCE = CurComponents.rend();
                for (const auto &SC : llvm::reverse(StackComponents)) {
                  // Do both expressions have the same kind?
                  if (CCI->getAssociatedExpression()->getStmtClass() !=
                      SC.getAssociatedExpression()->getStmtClass())
                    if (!(isa<ACCArraySectionExpr>(
                              SC.getAssociatedExpression()) &&
                          isa<ArraySubscriptExpr>(
                              CCI->getAssociatedExpression())))
                      return false;

                  Decl *CCD = CCI->getAssociatedDeclaration();
                  Decl *SCD = SC.getAssociatedDeclaration();
                  CCD = CCD ? CCD->getCanonicalDecl() : nullptr;
                  SCD = SCD ? SCD->getCanonicalDecl() : nullptr;
                  if (SCD != CCD)
                    return false;
                  std::advance(CCI, 1);
                  if (CCI == CCE)
                    break;
                }
                return true;
              })) {
        Visit(E->getBase());
      }
    } else
      Visit(E->getBase());
  }
  void VisitACCExecutableDirective(ACCExecutableDirective *S) {
    llvm::outs() << "-- <<DEBUG>> Checkpoint DSAChecker 0\n";
    for (auto *C : S->clauses()) {
      // Skip analysis of arguments of implicitly defined firstprivate clause
      // for task|target directives.
      // Skip analysis of arguments of implicitly defined map clause for target
      // directives.
      if (C && !((isa<ACCFirstprivateClause>(C) || isa<ACCMapClause>(C)) &&
                 C->isImplicit())) {
        for (auto *CC : C->children()) {
          if (CC)
            Visit(CC);
        }
      }
    }
    llvm::outs() << "-- <<DEBUG>> Checkpoint DSAChecker 1\n";
  }
  void VisitStmt(Stmt *S) {
    for (auto *C : S->children()) {
      if (C && !isa<ACCExecutableDirective>(C))
        Visit(C);
    }
  }

  bool isErrorFound() { return ErrorFound; }
  ArrayRef<Expr *> getImplicitFirstprivate() const {
    return ImplicitFirstprivate;
  }
  ArrayRef<Expr *> getImplicitMap() const { return ImplicitMap; }
  llvm::DenseMap<ValueDecl *, Expr *> &getVarsWithInheritedDSA() {
    return VarsWithInheritedDSA;
  }

  DSAAttrChecker(DSAStackTy *S, Sema &SemaRef, CapturedStmt *CS)
      : Stack(S), SemaRef(SemaRef), ErrorFound(false), CS(CS) {}
};
} // namespace

void Sema::ActOnOpenACCRegionStart(OpenACCDirectiveKind DKind, Scope *CurScope) {
  switch (DKind) {
  case ACCD_parallel:
  case ACCD_parellel_loop:
  case ACCD_parallel_for_simd:
  case ACCD_parallel_sections:
  case ACCD_teams:
  case ACCD_teams_distribute:
  case ACCD_teams_distribute_simd: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType KmpInt32PtrTy =
        Context.getPointerType(KmpInt32Ty).withConst().withRestrict();
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    break;
  }
  case ACCD_target_teams:
  case ACCD_target_parallel:
  case ACCD_target_parallel_for:
  case ACCD_target_parallel_for_simd:
  case ACCD_target_teams_distribute:
  case ACCD_target_teams_distribute_simd: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.", Context.VoidPtrTy.withConst()),
        std::make_pair(".copy_fn.",
                       Context.getPointerType(CopyFnType).withConst()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    Sema::CapturedParamNameType ParamsTarget[] = {
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'target' with no implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsTarget);
    QualType KmpInt32PtrTy =
        Context.getPointerType(KmpInt32Ty).withConst().withRestrict();
    Sema::CapturedParamNameType ParamsTeamsOrParallel[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'teams' or 'parallel'.  Both regions have
    // the same implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsTeamsOrParallel);
    break;
  }
  case ACCD_target:
  case ACCD_target_simd: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.", Context.VoidPtrTy.withConst()),
        std::make_pair(".copy_fn.",
                       Context.getPointerType(CopyFnType).withConst()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             std::make_pair(StringRef(), QualType()));
    break;
  }
  case ACCD_simd:
  case ACCD_for:
  case ACCD_for_simd:
  case ACCD_sections:
  case ACCD_section:
  case ACCD_single:
  case ACCD_master:
  case ACCD_critical:
  case ACCD_taskgroup:
  case ACCD_distribute:
  case ACCD_distribute_simd:
  case ACCD_ordered:
  case ACCD_atomic:
  case ACCD_target_data: {
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    break;
  }
  case ACCD_task: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.", Context.VoidPtrTy.withConst()),
        std::make_pair(".copy_fn.",
                       Context.getPointerType(CopyFnType).withConst()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    break;
  }
  case ACCD_taskloop:
  case ACCD_taskloop_simd: {
    QualType KmpInt32Ty =
        Context.getIntTypeForBitwidth(/*DestWidth=*/32, /*Signed=*/1);
    QualType KmpUInt64Ty =
        Context.getIntTypeForBitwidth(/*DestWidth=*/64, /*Signed=*/0);
    QualType KmpInt64Ty =
        Context.getIntTypeForBitwidth(/*DestWidth=*/64, /*Signed=*/1);
    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.",
                       Context.VoidPtrTy.withConst().withRestrict()),
        std::make_pair(
            ".copy_fn.",
            Context.getPointerType(CopyFnType).withConst().withRestrict()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(".lb.", KmpUInt64Ty),
        std::make_pair(".ub.", KmpUInt64Ty), std::make_pair(".st.", KmpInt64Ty),
        std::make_pair(".liter.", KmpInt32Ty),
        std::make_pair(".reductions.",
                       Context.VoidPtrTy.withConst().withRestrict()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    break;
  }
  case ACCD_distribute_parallel_for_simd:
  case ACCD_distribute_parallel_for: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType KmpInt32PtrTy =
        Context.getPointerType(KmpInt32Ty).withConst().withRestrict();
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(".previous.lb.", Context.getSizeType()),
        std::make_pair(".previous.ub.", Context.getSizeType()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    break;
  }
  case ACCD_target_teams_distribute_parallel_for:
  case ACCD_target_teams_distribute_parallel_for_simd: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType KmpInt32PtrTy =
        Context.getPointerType(KmpInt32Ty).withConst().withRestrict();

    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.", Context.VoidPtrTy.withConst()),
        std::make_pair(".copy_fn.",
                       Context.getPointerType(CopyFnType).withConst()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    Sema::CapturedParamNameType ParamsTarget[] = {
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'target' with no implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsTarget);

    Sema::CapturedParamNameType ParamsTeams[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'target' with no implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsTeams);

    Sema::CapturedParamNameType ParamsParallel[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(".previous.lb.", Context.getSizeType()),
        std::make_pair(".previous.ub.", Context.getSizeType()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'teams' or 'parallel'.  Both regions have
    // the same implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsParallel);
    break;
  }

  case ACCD_teams_distribute_parallel_for:
  case ACCD_teams_distribute_parallel_for_simd: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType KmpInt32PtrTy =
        Context.getPointerType(KmpInt32Ty).withConst().withRestrict();

    Sema::CapturedParamNameType ParamsTeams[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'target' with no implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsTeams);

    Sema::CapturedParamNameType ParamsParallel[] = {
        std::make_pair(".global_tid.", KmpInt32PtrTy),
        std::make_pair(".bound_tid.", KmpInt32PtrTy),
        std::make_pair(".previous.lb.", Context.getSizeType()),
        std::make_pair(".previous.ub.", Context.getSizeType()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    // Start a captured region for 'teams' or 'parallel'.  Both regions have
    // the same implicit parameters.
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             ParamsParallel);
    break;
  }
  case ACCD_target_update:
  case ACCD_target_enter_data:
  case ACCD_target_exit_data: {
    QualType KmpInt32Ty = Context.getIntTypeForBitwidth(32, 1);
    QualType Args[] = {Context.VoidPtrTy.withConst().withRestrict()};
    FunctionProtoType::ExtProtoInfo EPI;
    EPI.Variadic = true;
    QualType CopyFnType = Context.getFunctionType(Context.VoidTy, Args, EPI);
    Sema::CapturedParamNameType Params[] = {
        std::make_pair(".global_tid.", KmpInt32Ty),
        std::make_pair(".part_id.", Context.getPointerType(KmpInt32Ty)),
        std::make_pair(".privates.", Context.VoidPtrTy.withConst()),
        std::make_pair(".copy_fn.",
                       Context.getPointerType(CopyFnType).withConst()),
        std::make_pair(".task_t.", Context.VoidPtrTy.withConst()),
        std::make_pair(StringRef(), QualType()) // __context with shared vars
    };
    ActOnCapturedRegionStart(DSAStack->getConstructLoc(), CurScope, CR_OpenACC,
                             Params);
    // Mark this captured region as inlined, because we don't use outlined
    // function directly.
    getCurCapturedRegion()->TheCapturedDecl->addAttr(
        AlwaysInlineAttr::CreateImplicit(
            Context, AlwaysInlineAttr::Keyword_forceinline, SourceRange()));
    break;
  }
  case ACCD_threadprivate:
  case ACCD_taskyield:
  case ACCD_barrier:
  case ACCD_taskwait:
  case ACCD_cancellation_point:
  case ACCD_cancel:
  case ACCD_flush:
  case ACCD_declare_reduction:
  case ACCD_declare_simd:
  case ACCD_declare_target:
  case ACCD_end_declare_target:
    llvm_unreachable("OpenACC Directive is not allowed");
  case ACCD_unknown:
    llvm_unreachable("Unknown OpenACC directive");
  }
}

int Sema::getOpenACCCaptureLevels(OpenACCDirectiveKind DKind) {
  SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
  getOpenACCCaptureRegions(CaptureRegions, DKind);
  return CaptureRegions.size();
}

static ACCCapturedExprDecl *buildCaptureDecl(Sema &S, IdentifierInfo *Id,
                                             Expr *CaptureExpr, bool WithInit,
                                             bool AsExpression) {
  assert(CaptureExpr);
  ASTContext &C = S.getASTContext();
  Expr *Init = AsExpression ? CaptureExpr : CaptureExpr->IgnoreImpCasts();
  QualType Ty = Init->getType();
  if (CaptureExpr->getObjectKind() == OK_Ordinary && CaptureExpr->isGLValue()) {
    if (S.getLangOpts().CPlusPlus) {
      Ty = C.getLValueReferenceType(Ty);
    } else {
      Ty = C.getPointerType(Ty);
      ExprResult Res =
          S.CreateBuiltinUnaryOp(CaptureExpr->getExprLoc(), UO_AddrOf, Init);
      if (!Res.isUsable())
        return nullptr;
      Init = Res.get();
    }
    WithInit = true;
  }
  auto *CED = ACCCapturedExprDecl::Create(C, S.CurContext, Id, Ty,
                                          CaptureExpr->getLocStart());
  if (!WithInit)
    CED->addAttr(ACCCaptureNoInitAttr::CreateImplicit(C, SourceRange()));
  S.CurContext->addHiddenDecl(CED);
  S.AddInitializerToDecl(CED, Init, /*DirectInit=*/false);
  return CED;
}

static DeclRefExpr *buildCapture(Sema &S, ValueDecl *D, Expr *CaptureExpr,
                                 bool WithInit) {
  ACCCapturedExprDecl *CD;
  if (auto *VD = S.IsOpenACCCapturedDecl(D)) {
    CD = cast<ACCCapturedExprDecl>(VD);
  } else {
    CD = buildCaptureDecl(S, D->getIdentifier(), CaptureExpr, WithInit,
                          /*AsExpression=*/false);
  }
  return buildDeclRefExpr(S, CD, CD->getType().getNonReferenceType(),
                          CaptureExpr->getExprLoc());
}

static ExprResult buildCapture(Sema &S, Expr *CaptureExpr, DeclRefExpr *&Ref) {
  CaptureExpr = S.DefaultLvalueConversion(CaptureExpr).get();
  if (!Ref) {
    ACCCapturedExprDecl *CD = buildCaptureDecl(
        S, &S.getASTContext().Idents.get(".capture_expr."), CaptureExpr,
        /*WithInit=*/true, /*AsExpression=*/true);
    Ref = buildDeclRefExpr(S, CD, CD->getType().getNonReferenceType(),
                           CaptureExpr->getExprLoc());
  }
  ExprResult Res = Ref;
  if (!S.getLangOpts().CPlusPlus &&
      CaptureExpr->getObjectKind() == OK_Ordinary && CaptureExpr->isGLValue() &&
      Ref->getType()->isPointerType()) {
    Res = S.CreateBuiltinUnaryOp(CaptureExpr->getExprLoc(), UO_Deref, Ref);
    if (!Res.isUsable())
      return ExprError();
  }
  return S.DefaultLvalueConversion(Res.get());
}

namespace {
// OpenACC directives parsed in this section are represented as a
// CapturedStatement with an associated statement.  If a syntax error
// is detected during the parsing of the associated statement, the
// compiler must abort processing and close the CapturedStatement.
//
// Combined directives such as 'target parallel' have more than one
// nested CapturedStatements.  This RAII ensures that we unwind out
// of all the nested CapturedStatements when an error is found.
class CaptureRegionUnwinderRAII {
private:
  Sema &S;
  bool &ErrorFound;
  OpenACCDirectiveKind DKind;

public:
  CaptureRegionUnwinderRAII(Sema &S, bool &ErrorFound,
                            OpenACCDirectiveKind DKind)
      : S(S), ErrorFound(ErrorFound), DKind(DKind) {}
  ~CaptureRegionUnwinderRAII() {
    if (ErrorFound) {
      int ThisCaptureLevel = S.getOpenACCCaptureLevels(DKind);
      while (--ThisCaptureLevel >= 0)
        S.ActOnCapturedRegionError();
    }
  }
};
} // namespace

StmtResult Sema::ActOnOpenACCRegionEnd(StmtResult S,
                                      ArrayRef<ACCClause *> Clauses) {
  bool ErrorFound = false;
  CaptureRegionUnwinderRAII CaptureRegionUnwinder(
      *this, ErrorFound, DSAStack->getCurrentDirective());
  if (!S.isUsable()) {
    ErrorFound = true;
    return StmtError();
  }

  SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
  getOpenACCCaptureRegions(CaptureRegions, DSAStack->getCurrentDirective());
  ACCOrderedClause *OC = nullptr;
  ACCScheduleClause *SC = nullptr;
  SmallVector<ACCLinearClause *, 4> LCs;
  SmallVector<ACCClauseWithPreInit *, 8> PICs;
  // This is required for proper codegen.
  for (auto *Clause : Clauses) {
    if (isOpenACCTaskingDirective(DSAStack->getCurrentDirective()) &&
        Clause->getClauseKind() == ACCC_in_reduction) {
      // Capture taskgroup task_reduction descriptors inside the tasking regions
      // with the corresponding in_reduction items.
      auto *IRC = cast<ACCInReductionClause>(Clause);
      for (auto *E : IRC->taskgroup_descriptors())
        if (E)
          MarkDeclarationsReferencedInExpr(E);
    }
    if (isOpenACCPrivate(Clause->getClauseKind()) ||
        Clause->getClauseKind() == ACCC_copyprivate ||
        (getLangOpts().OpenACCUseTLS &&
         getASTContext().getTargetInfo().isTLSSupported() &&
         Clause->getClauseKind() == ACCC_copyin)) {
      DSAStack->setForceVarCapturing(Clause->getClauseKind() == ACCC_copyin);
      // Mark all variables in private list clauses as used in inner region.
      for (auto *VarRef : Clause->children()) {
        if (auto *E = cast_or_null<Expr>(VarRef)) {
          MarkDeclarationsReferencedInExpr(E);
        }
      }
      DSAStack->setForceVarCapturing(/*V=*/false);
    } else if (CaptureRegions.size() > 1 ||
               CaptureRegions.back() != ACCD_unknown) {
      if (auto *C = ACCClauseWithPreInit::get(Clause))
        PICs.push_back(C);
      if (auto *C = ACCClauseWithPostUpdate::get(Clause)) {
        if (auto *E = C->getPostUpdateExpr())
          MarkDeclarationsReferencedInExpr(E);
      }
    }
    if (Clause->getClauseKind() == ACCC_schedule)
      SC = cast<ACCScheduleClause>(Clause);
    else if (Clause->getClauseKind() == ACCC_ordered)
      OC = cast<ACCOrderedClause>(Clause);
    else if (Clause->getClauseKind() == ACCC_linear)
      LCs.push_back(cast<ACCLinearClause>(Clause));
  }
  // OpenACC, 2.7.1 Loop Construct, Restrictions
  // The nonmonotonic modifier cannot be specified if an ordered clause is
  // specified.
  if (SC &&
      (SC->getFirstScheduleModifier() == ACCC_SCHEDULE_MODIFIER_nonmonotonic ||
       SC->getSecondScheduleModifier() ==
           ACCC_SCHEDULE_MODIFIER_nonmonotonic) &&
      OC) {
    Diag(SC->getFirstScheduleModifier() == ACCC_SCHEDULE_MODIFIER_nonmonotonic
             ? SC->getFirstScheduleModifierLoc()
             : SC->getSecondScheduleModifierLoc(),
         diag::err_acc_schedule_nonmonotonic_ordered)
        << SourceRange(OC->getLocStart(), OC->getLocEnd());
    ErrorFound = true;
  }
  if (!LCs.empty() && OC && OC->getNumForLoops()) {
    for (auto *C : LCs) {
      Diag(C->getLocStart(), diag::err_acc_linear_ordered)
          << SourceRange(OC->getLocStart(), OC->getLocEnd());
    }
    ErrorFound = true;
  }
  if (isOpenACCWorksharingDirective(DSAStack->getCurrentDirective()) &&
      isOpenACCSimdDirective(DSAStack->getCurrentDirective()) && OC &&
      OC->getNumForLoops()) {
    Diag(OC->getLocStart(), diag::err_acc_ordered_simd)
        << getOpenACCDirectiveName(DSAStack->getCurrentDirective());
    ErrorFound = true;
  }
  if (ErrorFound) {
    return StmtError();
  }
  StmtResult SR = S;
  for (OpenACCDirectiveKind ThisCaptureRegion : llvm::reverse(CaptureRegions)) {
    // Mark all variables in private list clauses as used in inner region.
    // Required for proper codegen of combined directives.
    // TODO: add processing for other clauses.
    if (ThisCaptureRegion != ACCD_unknown) {
      for (auto *C : PICs) {
        OpenACCDirectiveKind CaptureRegion = C->getCaptureRegion();
        // Find the particular capture region for the clause if the
        // directive is a combined one with multiple capture regions.
        // If the directive is not a combined one, the capture region
        // associated with the clause is ACCD_unknown and is generated
        // only once.
        if (CaptureRegion == ThisCaptureRegion ||
            CaptureRegion == ACCD_unknown) {
          if (auto *DS = cast_or_null<DeclStmt>(C->getPreInitStmt())) {
            for (auto *D : DS->decls())
              MarkVariableReferenced(D->getLocation(), cast<VarDecl>(D));
          }
        }
      }
    }
    SR = ActOnCapturedRegionEnd(SR.get());
  }
  return SR;
}

static bool checkCancelRegion(Sema &SemaRef, OpenACCDirectiveKind CurrentRegion,
                              OpenACCDirectiveKind CancelRegion,
                              SourceLocation StartLoc) {
  // CancelRegion is only needed for cancel and cancellation_point.
  if (CurrentRegion != ACCD_cancel && CurrentRegion != ACCD_cancellation_point)
    return false;

  if (CancelRegion == ACCD_parallel || CancelRegion == ACCD_for ||
      CancelRegion == ACCD_sections || CancelRegion == ACCD_taskgroup)
    return false;

  SemaRef.Diag(StartLoc, diag::err_acc_wrong_cancel_region)
      << getOpenACCDirectiveName(CancelRegion);
  return true;
}

static bool checkNestingOfRegions(Sema &SemaRef, DSAStackTy *Stack,
                                  OpenACCDirectiveKind CurrentRegion,
                                  const DeclarationNameInfo &CurrentName,
                                  OpenACCDirectiveKind CancelRegion,
                                  SourceLocation StartLoc) {
  if (Stack->getCurScope()) {
    auto ParentRegion = Stack->getParentDirective();
    auto OffendingRegion = ParentRegion;
    bool NestingProhibited = false;
    bool CloseNesting = true;
    bool OrphanSeen = false;
    enum {
      NoRecommend,
      ShouldBeInParallelRegion,
      ShouldBeInOrderedRegion,
      ShouldBeInTargetRegion,
      ShouldBeInTeamsRegion
    } Recommend = NoRecommend;
    if (isOpenACCSimdDirective(ParentRegion) && CurrentRegion != ACCD_ordered) {
      // OpenACC [2.16, Nesting of Regions]
      // OpenACC constructs may not be nested inside a simd region.
      // OpenACC [2.8.1,simd Construct, Restrictions]
      // An ordered construct with the simd clause is the only OpenACC
      // construct that can appear in the simd region.
      // Allowing a SIMD construct nested in another SIMD construct is an
      // extension. The OpenACC 4.5 spec does not allow it. Issue a warning
      // message.
      SemaRef.Diag(StartLoc, (CurrentRegion != ACCD_simd)
                                 ? diag::err_acc_prohibited_region_simd
                                 : diag::warn_acc_nesting_simd);
      return CurrentRegion != ACCD_simd;
    }
    if (ParentRegion == ACCD_atomic) {
      // OpenACC [2.16, Nesting of Regions]
      // OpenACC constructs may not be nested inside an atomic region.
      SemaRef.Diag(StartLoc, diag::err_acc_prohibited_region_atomic);
      return true;
    }
    if (CurrentRegion == ACCD_section) {
      // OpenACC [2.7.2, sections Construct, Restrictions]
      // Orphaned section directives are prohibited. That is, the section
      // directives must appear within the sections construct and must not be
      // encountered elsewhere in the sections region.
      if (ParentRegion != ACCD_sections &&
          ParentRegion != ACCD_parallel_sections) {
        SemaRef.Diag(StartLoc, diag::err_acc_orphaned_section_directive)
            << (ParentRegion != ACCD_unknown)
            << getOpenACCDirectiveName(ParentRegion);
        return true;
      }
      return false;
    }
    // Allow some constructs (except teams) to be orphaned (they could be
    // used in functions, called from OpenACC regions with the required
    // preconditions).
    if (ParentRegion == ACCD_unknown &&
        !isOpenACCNestingTeamsDirective(CurrentRegion))
      return false;
    if (CurrentRegion == ACCD_cancellation_point ||
        CurrentRegion == ACCD_cancel) {
      // OpenACC [2.16, Nesting of Regions]
      // A cancellation point construct for which construct-type-clause is
      // taskgroup must be nested inside a task construct. A cancellation
      // point construct for which construct-type-clause is not taskgroup must
      // be closely nested inside an OpenACC construct that matches the type
      // specified in construct-type-clause.
      // A cancel construct for which construct-type-clause is taskgroup must be
      // nested inside a task construct. A cancel construct for which
      // construct-type-clause is not taskgroup must be closely nested inside an
      // OpenACC construct that matches the type specified in
      // construct-type-clause.
      NestingProhibited =
          !((CancelRegion == ACCD_parallel &&
             (ParentRegion == ACCD_parallel ||
              ParentRegion == ACCD_target_parallel)) ||
            (CancelRegion == ACCD_for &&
             (ParentRegion == ACCD_for || ParentRegion == ACCD_parellel_loop ||
              ParentRegion == ACCD_target_parallel_for ||
              ParentRegion == ACCD_distribute_parallel_for ||
              ParentRegion == ACCD_teams_distribute_parallel_for ||
              ParentRegion == ACCD_target_teams_distribute_parallel_for)) ||
            (CancelRegion == ACCD_taskgroup && ParentRegion == ACCD_task) ||
            (CancelRegion == ACCD_sections &&
             (ParentRegion == ACCD_section || ParentRegion == ACCD_sections ||
              ParentRegion == ACCD_parallel_sections)));
    } else if (CurrentRegion == ACCD_master) {
      // OpenACC [2.16, Nesting of Regions]
      // A master region may not be closely nested inside a worksharing,
      // atomic, or explicit task region.
      NestingProhibited = isOpenACCWorksharingDirective(ParentRegion) ||
                          isOpenACCTaskingDirective(ParentRegion);
    } else if (CurrentRegion == ACCD_critical && CurrentName.getName()) {
      // OpenACC [2.16, Nesting of Regions]
      // A critical region may not be nested (closely or otherwise) inside a
      // critical region with the same name. Note that this restriction is not
      // sufficient to prevent deadlock.
      SourceLocation PreviousCriticalLoc;
      bool DeadLock = Stack->hasDirective(
          [CurrentName, &PreviousCriticalLoc](OpenACCDirectiveKind K,
                                              const DeclarationNameInfo &DNI,
                                              SourceLocation Loc) -> bool {
            if (K == ACCD_critical && DNI.getName() == CurrentName.getName()) {
              PreviousCriticalLoc = Loc;
              return true;
            } else
              return false;
          },
          false /* skip top directive */);
      if (DeadLock) {
        SemaRef.Diag(StartLoc,
                     diag::err_acc_prohibited_region_critical_same_name)
            << CurrentName.getName();
        if (PreviousCriticalLoc.isValid())
          SemaRef.Diag(PreviousCriticalLoc,
                       diag::note_acc_previous_critical_region);
        return true;
      }
    } else if (CurrentRegion == ACCD_barrier) {
      // OpenACC [2.16, Nesting of Regions]
      // A barrier region may not be closely nested inside a worksharing,
      // explicit task, critical, ordered, atomic, or master region.
      NestingProhibited = isOpenACCWorksharingDirective(ParentRegion) ||
                          isOpenACCTaskingDirective(ParentRegion) ||
                          ParentRegion == ACCD_master ||
                          ParentRegion == ACCD_critical ||
                          ParentRegion == ACCD_ordered;
    } else if (isOpenACCWorksharingDirective(CurrentRegion) &&
               !isOpenACCParallelDirective(CurrentRegion) &&
               !isOpenACCTeamsDirective(CurrentRegion)) {
      // OpenACC [2.16, Nesting of Regions]
      // A worksharing region may not be closely nested inside a worksharing,
      // explicit task, critical, ordered, atomic, or master region.
      NestingProhibited = isOpenACCWorksharingDirective(ParentRegion) ||
                          isOpenACCTaskingDirective(ParentRegion) ||
                          ParentRegion == ACCD_master ||
                          ParentRegion == ACCD_critical ||
                          ParentRegion == ACCD_ordered;
      Recommend = ShouldBeInParallelRegion;
    } else if (CurrentRegion == ACCD_ordered) {
      // OpenACC [2.16, Nesting of Regions]
      // An ordered region may not be closely nested inside a critical,
      // atomic, or explicit task region.
      // An ordered region must be closely nested inside a loop region (or
      // parallel loop region) with an ordered clause.
      // OpenACC [2.8.1,simd Construct, Restrictions]
      // An ordered construct with the simd clause is the only OpenACC construct
      // that can appear in the simd region.
      NestingProhibited = ParentRegion == ACCD_critical ||
                          isOpenACCTaskingDirective(ParentRegion) ||
                          !(isOpenACCSimdDirective(ParentRegion) ||
                            Stack->isParentOrderedRegion());
      Recommend = ShouldBeInOrderedRegion;
    } else if (isOpenACCNestingTeamsDirective(CurrentRegion)) {
      // OpenACC [2.16, Nesting of Regions]
      // If specified, a teams construct must be contained within a target
      // construct.
      NestingProhibited = ParentRegion != ACCD_target;
      OrphanSeen = ParentRegion == ACCD_unknown;
      Recommend = ShouldBeInTargetRegion;
    }
    if (!NestingProhibited &&
        !isOpenACCTargetExecutionDirective(CurrentRegion) &&
        !isOpenACCTargetDataManagementDirective(CurrentRegion) &&
        (ParentRegion == ACCD_teams || ParentRegion == ACCD_target_teams)) {
      // OpenACC [2.16, Nesting of Regions]
      // distribute, parallel, parallel sections, parallel workshare, and the
      // parallel loop and parallel loop SIMD constructs are the only OpenACC
      // constructs that can be closely nested in the teams region.
      NestingProhibited = !isOpenACCParallelDirective(CurrentRegion) &&
                          !isOpenACCDistributeDirective(CurrentRegion);
      Recommend = ShouldBeInParallelRegion;
    }
    if (!NestingProhibited &&
        isOpenACCNestingDistributeDirective(CurrentRegion)) {
      // OpenACC 4.5 [2.17 Nesting of Regions]
      // The region associated with the distribute construct must be strictly
      // nested inside a teams region
      NestingProhibited =
          (ParentRegion != ACCD_teams && ParentRegion != ACCD_target_teams);
      Recommend = ShouldBeInTeamsRegion;
    }
    if (!NestingProhibited &&
        (isOpenACCTargetExecutionDirective(CurrentRegion) ||
         isOpenACCTargetDataManagementDirective(CurrentRegion))) {
      // OpenACC 4.5 [2.17 Nesting of Regions]
      // If a target, target update, target data, target enter data, or
      // target exit data construct is encountered during execution of a
      // target region, the behavior is unspecified.
      NestingProhibited = Stack->hasDirective(
          [&OffendingRegion](OpenACCDirectiveKind K, const DeclarationNameInfo &,
                             SourceLocation) -> bool {
            if (isOpenACCTargetExecutionDirective(K)) {
              OffendingRegion = K;
              return true;
            } else
              return false;
          },
          false /* don't skip top directive */);
      CloseNesting = false;
    }
    if (NestingProhibited) {
      if (OrphanSeen) {
        SemaRef.Diag(StartLoc, diag::err_acc_orphaned_device_directive)
            << getOpenACCDirectiveName(CurrentRegion) << Recommend;
      } else {
        SemaRef.Diag(StartLoc, diag::err_acc_prohibited_region)
            << CloseNesting << getOpenACCDirectiveName(OffendingRegion)
            << Recommend << getOpenACCDirectiveName(CurrentRegion);
      }
      return true;
    }
  }
  return false;
}

static bool checkIfClauses(Sema &S, OpenACCDirectiveKind Kind,
                           ArrayRef<ACCClause *> Clauses,
                           ArrayRef<OpenACCDirectiveKind> AllowedNameModifiers) {
  bool ErrorFound = false;
  unsigned NamedModifiersNumber = 0;
  SmallVector<const ACCIfClause *, ACCC_unknown + 1> FoundNameModifiers(
      ACCD_unknown + 1);
  SmallVector<SourceLocation, 4> NameModifierLoc;
  for (const auto *C : Clauses) {
    if (const auto *IC = dyn_cast_or_null<ACCIfClause>(C)) {
      // At most one if clause without a directive-name-modifier can appear on
      // the directive.
      OpenACCDirectiveKind CurNM = IC->getNameModifier();
      if (FoundNameModifiers[CurNM]) {
        S.Diag(C->getLocStart(), diag::err_acc_more_one_clause)
            << getOpenACCDirectiveName(Kind) << getOpenACCClauseName(ACCC_if)
            << (CurNM != ACCD_unknown) << getOpenACCDirectiveName(CurNM);
        ErrorFound = true;
      } else if (CurNM != ACCD_unknown) {
        NameModifierLoc.push_back(IC->getNameModifierLoc());
        ++NamedModifiersNumber;
      }
      FoundNameModifiers[CurNM] = IC;
      if (CurNM == ACCD_unknown)
        continue;
      // Check if the specified name modifier is allowed for the current
      // directive.
      // At most one if clause with the particular directive-name-modifier can
      // appear on the directive.
      bool MatchFound = false;
      for (auto NM : AllowedNameModifiers) {
        if (CurNM == NM) {
          MatchFound = true;
          break;
        }
      }
      if (!MatchFound) {
        S.Diag(IC->getNameModifierLoc(),
               diag::err_acc_wrong_if_directive_name_modifier)
            << getOpenACCDirectiveName(CurNM) << getOpenACCDirectiveName(Kind);
        ErrorFound = true;
      }
    }
  }
  // If any if clause on the directive includes a directive-name-modifier then
  // all if clauses on the directive must include a directive-name-modifier.
  if (FoundNameModifiers[ACCD_unknown] && NamedModifiersNumber > 0) {
    if (NamedModifiersNumber == AllowedNameModifiers.size()) {
      S.Diag(FoundNameModifiers[ACCD_unknown]->getLocStart(),
             diag::err_acc_no_more_if_clause);
    } else {
      std::string Values;
      std::string Sep(", ");
      unsigned AllowedCnt = 0;
      unsigned TotalAllowedNum =
          AllowedNameModifiers.size() - NamedModifiersNumber;
      for (unsigned Cnt = 0, End = AllowedNameModifiers.size(); Cnt < End;
           ++Cnt) {
        OpenACCDirectiveKind NM = AllowedNameModifiers[Cnt];
        if (!FoundNameModifiers[NM]) {
          Values += "'";
          Values += getOpenACCDirectiveName(NM);
          Values += "'";
          if (AllowedCnt + 2 == TotalAllowedNum)
            Values += " or ";
          else if (AllowedCnt + 1 != TotalAllowedNum)
            Values += Sep;
          ++AllowedCnt;
        }
      }
      S.Diag(FoundNameModifiers[ACCD_unknown]->getCondition()->getLocStart(),
             diag::err_acc_unnamed_if_clause)
          << (TotalAllowedNum > 1) << Values;
    }
    for (auto Loc : NameModifierLoc) {
      S.Diag(Loc, diag::note_acc_previous_named_if_clause);
    }
    ErrorFound = true;
  }
  return ErrorFound;
}

StmtResult Sema::ActOnOpenACCExecutableDirective(
    OpenACCDirectiveKind Kind, const DeclarationNameInfo &DirName,
    OpenACCDirectiveKind CancelRegion, ArrayRef<ACCClause *> Clauses,
    Stmt *AStmt, SourceLocation StartLoc, SourceLocation EndLoc) {
  StmtResult Res = StmtError();
  // First check CancelRegion which is then used in checkNestingOfRegions.
  if (checkCancelRegion(*this, Kind, CancelRegion, StartLoc) ||
      checkNestingOfRegions(*this, DSAStack, Kind, DirName, CancelRegion,
                            StartLoc))
    return StmtError();

  llvm::SmallVector<ACCClause *, 8> ClausesWithImplicit;
  llvm::DenseMap<ValueDecl *, Expr *> VarsWithInheritedDSA;
  bool ErrorFound = false;
  ClausesWithImplicit.append(Clauses.begin(), Clauses.end());

  if (AStmt && !CurContext->isDependentContext()) {
    assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

    // Check default data sharing attributes for referenced variables.
    DSAAttrChecker DSAChecker(DSAStack, *this, cast<CapturedStmt>(AStmt));
    int ThisCaptureLevel = getOpenACCCaptureLevels(Kind);
    Stmt *S = AStmt;
    while (--ThisCaptureLevel >= 0)
      S = cast<CapturedStmt>(S)->getCapturedStmt();
    /* S->dumpColor(); */
    DSAChecker.Visit(S);
    if (DSAChecker.isErrorFound())
      return StmtError();
    // Generate list of implicitly defined firstprivate variables.
    VarsWithInheritedDSA = DSAChecker.getVarsWithInheritedDSA();

    SmallVector<Expr *, 4> ImplicitFirstprivates(
        DSAChecker.getImplicitFirstprivate().begin(),
        DSAChecker.getImplicitFirstprivate().end());
    SmallVector<Expr *, 4> ImplicitMaps(DSAChecker.getImplicitMap().begin(),
                                        DSAChecker.getImplicitMap().end());
    // Mark taskgroup task_reduction descriptors as implicitly firstprivate.
    for (auto *C : Clauses) {
      if (auto *IRC = dyn_cast<ACCInReductionClause>(C)) {
        for (auto *E : IRC->taskgroup_descriptors())
          if (E)
            ImplicitFirstprivates.emplace_back(E);
      }
    }
    if (!ImplicitFirstprivates.empty()) {
      if (ACCClause *Implicit = ActOnOpenACCFirstprivateClause(
              ImplicitFirstprivates, SourceLocation(), SourceLocation(),
              SourceLocation())) {
        ClausesWithImplicit.push_back(Implicit);
        ErrorFound = cast<ACCFirstprivateClause>(Implicit)->varlist_size() !=
                     ImplicitFirstprivates.size();
      } else
        ErrorFound = true;
    }
    if (!ImplicitMaps.empty()) {
      if (ACCClause *Implicit = ActOnOpenACCMapClause(
              ACCC_MAP_unknown, ACCC_MAP_tofrom, /*IsMapTypeImplicit=*/true,
              SourceLocation(), SourceLocation(), ImplicitMaps,
              SourceLocation(), SourceLocation(), SourceLocation())) {
        ClausesWithImplicit.emplace_back(Implicit);
        ErrorFound |=
            cast<ACCMapClause>(Implicit)->varlist_size() != ImplicitMaps.size();
      } else
        ErrorFound = true;
    }
  }

  llvm::SmallVector<OpenACCDirectiveKind, 4> AllowedNameModifiers;
  switch (Kind) {
  case ACCD_parallel:
    Res = ActOnOpenACCParallelDirective(ClausesWithImplicit, AStmt, StartLoc,
                                       EndLoc);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_simd:
    Res = ActOnOpenACCSimdDirective(ClausesWithImplicit, AStmt, StartLoc, EndLoc,
                                   VarsWithInheritedDSA);
    break;
  case ACCD_for:
    Res = ActOnOpenACCForDirective(ClausesWithImplicit, AStmt, StartLoc, EndLoc,
                                  VarsWithInheritedDSA);
    break;
  case ACCD_for_simd:
    Res = ActOnOpenACCForSimdDirective(ClausesWithImplicit, AStmt, StartLoc,
                                      EndLoc, VarsWithInheritedDSA);
    break;
  case ACCD_sections:
    Res = ActOnOpenACCSectionsDirective(ClausesWithImplicit, AStmt, StartLoc,
                                       EndLoc);
    break;
  case ACCD_section:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc section' directive");
    Res = ActOnOpenACCSectionDirective(AStmt, StartLoc, EndLoc);
    break;
  case ACCD_single:
    Res = ActOnOpenACCSingleDirective(ClausesWithImplicit, AStmt, StartLoc,
                                     EndLoc);
    break;
  case ACCD_master:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc master' directive");
    Res = ActOnOpenACCMasterDirective(AStmt, StartLoc, EndLoc);
    break;
  case ACCD_critical:
    Res = ActOnOpenACCCriticalDirective(DirName, ClausesWithImplicit, AStmt,
                                       StartLoc, EndLoc);
    break;
  case ACCD_parellel_loop:
    Res = ActOnOpenACCParallelLoopDirective(ClausesWithImplicit, AStmt, StartLoc,
                                          EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_parallel_for_simd:
    Res = ActOnOpenACCParallelForSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_parallel_sections:
    Res = ActOnOpenACCParallelSectionsDirective(ClausesWithImplicit, AStmt,
                                               StartLoc, EndLoc);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_task:
    Res =
        ActOnOpenACCTaskDirective(ClausesWithImplicit, AStmt, StartLoc, EndLoc);
    AllowedNameModifiers.push_back(ACCD_task);
    break;
  case ACCD_taskyield:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc taskyield' directive");
    assert(AStmt == nullptr &&
           "No associated statement allowed for 'acc taskyield' directive");
    Res = ActOnOpenACCTaskyieldDirective(StartLoc, EndLoc);
    break;
  case ACCD_barrier:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc barrier' directive");
    assert(AStmt == nullptr &&
           "No associated statement allowed for 'acc barrier' directive");
    Res = ActOnOpenACCBarrierDirective(StartLoc, EndLoc);
    break;
  case ACCD_taskwait:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc taskwait' directive");
    assert(AStmt == nullptr &&
           "No associated statement allowed for 'acc taskwait' directive");
    Res = ActOnOpenACCTaskwaitDirective(StartLoc, EndLoc);
    break;
  case ACCD_taskgroup:
    Res = ActOnOpenACCTaskgroupDirective(ClausesWithImplicit, AStmt, StartLoc,
                                        EndLoc);
    break;
  case ACCD_flush:
    assert(AStmt == nullptr &&
           "No associated statement allowed for 'acc flush' directive");
    Res = ActOnOpenACCFlushDirective(ClausesWithImplicit, StartLoc, EndLoc);
    break;
  case ACCD_ordered:
    Res = ActOnOpenACCOrderedDirective(ClausesWithImplicit, AStmt, StartLoc,
                                      EndLoc);
    break;
  case ACCD_atomic:
    Res = ActOnOpenACCAtomicDirective(ClausesWithImplicit, AStmt, StartLoc,
                                     EndLoc);
    break;
  case ACCD_teams:
    Res =
        ActOnOpenACCTeamsDirective(ClausesWithImplicit, AStmt, StartLoc, EndLoc);
    break;
  case ACCD_target:
    Res = ActOnOpenACCTargetDirective(ClausesWithImplicit, AStmt, StartLoc,
                                     EndLoc);
    AllowedNameModifiers.push_back(ACCD_target);
    break;
  case ACCD_target_parallel:
    Res = ActOnOpenACCTargetParallelDirective(ClausesWithImplicit, AStmt,
                                             StartLoc, EndLoc);
    AllowedNameModifiers.push_back(ACCD_target);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_target_parallel_for:
    Res = ActOnOpenACCTargetParallelForDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_cancellation_point:
    assert(ClausesWithImplicit.empty() &&
           "No clauses are allowed for 'acc cancellation point' directive");
    assert(AStmt == nullptr && "No associated statement allowed for 'acc "
                               "cancellation point' directive");
    Res = ActOnOpenACCCancellationPointDirective(StartLoc, EndLoc, CancelRegion);
    break;
  case ACCD_cancel:
    assert(AStmt == nullptr &&
           "No associated statement allowed for 'acc cancel' directive");
    Res = ActOnOpenACCCancelDirective(ClausesWithImplicit, StartLoc, EndLoc,
                                     CancelRegion);
    AllowedNameModifiers.push_back(ACCD_cancel);
    break;
  case ACCD_target_data:
    Res = ActOnOpenACCTargetDataDirective(ClausesWithImplicit, AStmt, StartLoc,
                                         EndLoc);
    AllowedNameModifiers.push_back(ACCD_target_data);
    break;
  case ACCD_target_enter_data:
    Res = ActOnOpenACCTargetEnterDataDirective(ClausesWithImplicit, StartLoc,
                                              EndLoc, AStmt);
    AllowedNameModifiers.push_back(ACCD_target_enter_data);
    break;
  case ACCD_target_exit_data:
    Res = ActOnOpenACCTargetExitDataDirective(ClausesWithImplicit, StartLoc,
                                             EndLoc, AStmt);
    AllowedNameModifiers.push_back(ACCD_target_exit_data);
    break;
  case ACCD_taskloop:
    Res = ActOnOpenACCTaskLoopDirective(ClausesWithImplicit, AStmt, StartLoc,
                                       EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_taskloop);
    break;
  case ACCD_taskloop_simd:
    Res = ActOnOpenACCTaskLoopSimdDirective(ClausesWithImplicit, AStmt, StartLoc,
                                           EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_taskloop);
    break;
  case ACCD_distribute:
    Res = ActOnOpenACCDistributeDirective(ClausesWithImplicit, AStmt, StartLoc,
                                         EndLoc, VarsWithInheritedDSA);
    break;
  case ACCD_target_update:
    Res = ActOnOpenACCTargetUpdateDirective(ClausesWithImplicit, StartLoc,
                                           EndLoc, AStmt);
    AllowedNameModifiers.push_back(ACCD_target_update);
    break;
  case ACCD_distribute_parallel_for:
    Res = ActOnOpenACCDistributeParallelForDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_distribute_parallel_for_simd:
    Res = ActOnOpenACCDistributeParallelForSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_distribute_simd:
    Res = ActOnOpenACCDistributeSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    break;
  case ACCD_target_parallel_for_simd:
    Res = ActOnOpenACCTargetParallelForSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_target_simd:
    Res = ActOnOpenACCTargetSimdDirective(ClausesWithImplicit, AStmt, StartLoc,
                                         EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    break;
  case ACCD_teams_distribute:
    Res = ActOnOpenACCTeamsDistributeDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    break;
  case ACCD_teams_distribute_simd:
    Res = ActOnOpenACCTeamsDistributeSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    break;
  case ACCD_teams_distribute_parallel_for_simd:
    Res = ActOnOpenACCTeamsDistributeParallelForSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_teams_distribute_parallel_for:
    Res = ActOnOpenACCTeamsDistributeParallelForDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_target_teams:
    Res = ActOnOpenACCTargetTeamsDirective(ClausesWithImplicit, AStmt, StartLoc,
                                          EndLoc);
    AllowedNameModifiers.push_back(ACCD_target);
    break;
  case ACCD_target_teams_distribute:
    Res = ActOnOpenACCTargetTeamsDistributeDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    break;
  case ACCD_target_teams_distribute_parallel_for:
    Res = ActOnOpenACCTargetTeamsDistributeParallelForDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_target_teams_distribute_parallel_for_simd:
    Res = ActOnOpenACCTargetTeamsDistributeParallelForSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    AllowedNameModifiers.push_back(ACCD_parallel);
    break;
  case ACCD_target_teams_distribute_simd:
    Res = ActOnOpenACCTargetTeamsDistributeSimdDirective(
        ClausesWithImplicit, AStmt, StartLoc, EndLoc, VarsWithInheritedDSA);
    AllowedNameModifiers.push_back(ACCD_target);
    break;
  case ACCD_declare_target:
  case ACCD_end_declare_target:
  case ACCD_threadprivate:
  case ACCD_declare_reduction:
  case ACCD_declare_simd:
    llvm_unreachable("OpenACC Directive is not allowed");
  case ACCD_unknown:
    llvm_unreachable("Unknown OpenACC directive");
  }

  for (auto P : VarsWithInheritedDSA) {
    Diag(P.second->getExprLoc(), diag::err_acc_no_dsa_for_variable)
        << P.first << P.second->getSourceRange();
  }
  ErrorFound = !VarsWithInheritedDSA.empty() || ErrorFound;

  if (!AllowedNameModifiers.empty())
    ErrorFound = checkIfClauses(*this, Kind, Clauses, AllowedNameModifiers) ||
                 ErrorFound;

  if (ErrorFound)
    return StmtError();
  return Res;
}

Sema::DeclGroupPtrTy Sema::ActOnOpenACCDeclareSimdDirective(
    DeclGroupPtrTy DG, ACCDeclareSimdDeclAttr::BranchStateTy BS, Expr *Simdlen,
    ArrayRef<Expr *> Uniforms, ArrayRef<Expr *> Aligneds,
    ArrayRef<Expr *> Alignments, ArrayRef<Expr *> Linears,
    ArrayRef<unsigned> LinModifiers, ArrayRef<Expr *> Steps, SourceRange SR) {
  assert(Aligneds.size() == Alignments.size());
  assert(Linears.size() == LinModifiers.size());
  assert(Linears.size() == Steps.size());
  if (!DG || DG.get().isNull())
    return DeclGroupPtrTy();

  if (!DG.get().isSingleDecl()) {
    Diag(SR.getBegin(), diag::err_acc_single_decl_in_declare_simd);
    return DG;
  }
  auto *ADecl = DG.get().getSingleDecl();
  if (auto *FTD = dyn_cast<FunctionTemplateDecl>(ADecl))
    ADecl = FTD->getTemplatedDecl();

  auto *FD = dyn_cast<FunctionDecl>(ADecl);
  if (!FD) {
    Diag(ADecl->getLocation(), diag::err_acc_function_expected);
    return DeclGroupPtrTy();
  }

  // OpenACC [2.8.2, declare simd construct, Description]
  // The parameter of the simdlen clause must be a constant positive integer
  // expression.
  ExprResult SL;
  if (Simdlen)
    SL = VerifyPositiveIntegerConstantInClause(Simdlen, ACCC_simdlen);
  // OpenACC [2.8.2, declare simd construct, Description]
  // The special this pointer can be used as if was one of the arguments to the
  // function in any of the linear, aligned, or uniform clauses.
  // The uniform clause declares one or more arguments to have an invariant
  // value for all concurrent invocations of the function in the execution of a
  // single SIMD loop.
  llvm::DenseMap<Decl *, Expr *> UniformedArgs;
  Expr *UniformedLinearThis = nullptr;
  for (auto *E : Uniforms) {
    E = E->IgnoreParenImpCasts();
    if (auto *DRE = dyn_cast<DeclRefExpr>(E))
      if (auto *PVD = dyn_cast<ParmVarDecl>(DRE->getDecl()))
        if (FD->getNumParams() > PVD->getFunctionScopeIndex() &&
            FD->getParamDecl(PVD->getFunctionScopeIndex())
                    ->getCanonicalDecl() == PVD->getCanonicalDecl()) {
          UniformedArgs.insert(std::make_pair(PVD->getCanonicalDecl(), E));
          continue;
        }
    if (isa<CXXThisExpr>(E)) {
      UniformedLinearThis = E;
      continue;
    }
    Diag(E->getExprLoc(), diag::err_acc_param_or_this_in_clause)
        << FD->getDeclName() << (isa<CXXMethodDecl>(ADecl) ? 1 : 0);
  }
  // OpenACC [2.8.2, declare simd construct, Description]
  // The aligned clause declares that the object to which each list item points
  // is aligned to the number of bytes expressed in the optional parameter of
  // the aligned clause.
  // The special this pointer can be used as if was one of the arguments to the
  // function in any of the linear, aligned, or uniform clauses.
  // The type of list items appearing in the aligned clause must be array,
  // pointer, reference to array, or reference to pointer.
  llvm::DenseMap<Decl *, Expr *> AlignedArgs;
  Expr *AlignedThis = nullptr;
  for (auto *E : Aligneds) {
    E = E->IgnoreParenImpCasts();
    if (auto *DRE = dyn_cast<DeclRefExpr>(E))
      if (auto *PVD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
        auto *CanonPVD = PVD->getCanonicalDecl();
        if (FD->getNumParams() > PVD->getFunctionScopeIndex() &&
            FD->getParamDecl(PVD->getFunctionScopeIndex())
                    ->getCanonicalDecl() == CanonPVD) {
          // OpenACC  [2.8.1, simd construct, Restrictions]
          // A list-item cannot appear in more than one aligned clause.
          if (AlignedArgs.count(CanonPVD) > 0) {
            Diag(E->getExprLoc(), diag::err_acc_aligned_twice)
                << 1 << E->getSourceRange();
            Diag(AlignedArgs[CanonPVD]->getExprLoc(),
                 diag::note_acc_explicit_dsa)
                << getOpenACCClauseName(ACCC_aligned);
            continue;
          }
          AlignedArgs[CanonPVD] = E;
          QualType QTy = PVD->getType()
                             .getNonReferenceType()
                             .getUnqualifiedType()
                             .getCanonicalType();
          const Type *Ty = QTy.getTypePtrOrNull();
          if (!Ty || (!Ty->isArrayType() && !Ty->isPointerType())) {
            Diag(E->getExprLoc(), diag::err_acc_aligned_expected_array_or_ptr)
                << QTy << getLangOpts().CPlusPlus << E->getSourceRange();
            Diag(PVD->getLocation(), diag::note_previous_decl) << PVD;
          }
          continue;
        }
      }
    if (isa<CXXThisExpr>(E)) {
      if (AlignedThis) {
        Diag(E->getExprLoc(), diag::err_acc_aligned_twice)
            << 2 << E->getSourceRange();
        Diag(AlignedThis->getExprLoc(), diag::note_acc_explicit_dsa)
            << getOpenACCClauseName(ACCC_aligned);
      }
      AlignedThis = E;
      continue;
    }
    Diag(E->getExprLoc(), diag::err_acc_param_or_this_in_clause)
        << FD->getDeclName() << (isa<CXXMethodDecl>(ADecl) ? 1 : 0);
  }
  // The optional parameter of the aligned clause, alignment, must be a constant
  // positive integer expression. If no optional parameter is specified,
  // implementation-defined default alignments for SIMD instructions on the
  // target platforms are assumed.
  SmallVector<Expr *, 4> NewAligns;
  for (auto *E : Alignments) {
    ExprResult Align;
    if (E)
      Align = VerifyPositiveIntegerConstantInClause(E, ACCC_aligned);
    NewAligns.push_back(Align.get());
  }
  // OpenACC [2.8.2, declare simd construct, Description]
  // The linear clause declares one or more list items to be private to a SIMD
  // lane and to have a linear relationship with respect to the iteration space
  // of a loop.
  // The special this pointer can be used as if was one of the arguments to the
  // function in any of the linear, aligned, or uniform clauses.
  // When a linear-step expression is specified in a linear clause it must be
  // either a constant integer expression or an integer-typed parameter that is
  // specified in a uniform clause on the directive.
  llvm::DenseMap<Decl *, Expr *> LinearArgs;
  const bool IsUniformedThis = UniformedLinearThis != nullptr;
  auto MI = LinModifiers.begin();
  for (auto *E : Linears) {
    auto LinKind = static_cast<OpenACCLinearClauseKind>(*MI);
    ++MI;
    E = E->IgnoreParenImpCasts();
    if (auto *DRE = dyn_cast<DeclRefExpr>(E))
      if (auto *PVD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
        auto *CanonPVD = PVD->getCanonicalDecl();
        if (FD->getNumParams() > PVD->getFunctionScopeIndex() &&
            FD->getParamDecl(PVD->getFunctionScopeIndex())
                    ->getCanonicalDecl() == CanonPVD) {
          // OpenACC  [2.15.3.7, linear Clause, Restrictions]
          // A list-item cannot appear in more than one linear clause.
          if (LinearArgs.count(CanonPVD) > 0) {
            Diag(E->getExprLoc(), diag::err_acc_wrong_dsa)
                << getOpenACCClauseName(ACCC_linear)
                << getOpenACCClauseName(ACCC_linear) << E->getSourceRange();
            Diag(LinearArgs[CanonPVD]->getExprLoc(),
                 diag::note_acc_explicit_dsa)
                << getOpenACCClauseName(ACCC_linear);
            continue;
          }
          // Each argument can appear in at most one uniform or linear clause.
          if (UniformedArgs.count(CanonPVD) > 0) {
            Diag(E->getExprLoc(), diag::err_acc_wrong_dsa)
                << getOpenACCClauseName(ACCC_linear)
                << getOpenACCClauseName(ACCC_uniform) << E->getSourceRange();
            Diag(UniformedArgs[CanonPVD]->getExprLoc(),
                 diag::note_acc_explicit_dsa)
                << getOpenACCClauseName(ACCC_uniform);
            continue;
          }
          LinearArgs[CanonPVD] = E;
          if (E->isValueDependent() || E->isTypeDependent() ||
              E->isInstantiationDependent() ||
              E->containsUnexpandedParameterPack())
            continue;
          (void)CheckOpenACCLinearDecl(CanonPVD, E->getExprLoc(), LinKind,
                                      PVD->getOriginalType());
          continue;
        }
      }
    if (isa<CXXThisExpr>(E)) {
      if (UniformedLinearThis) {
        Diag(E->getExprLoc(), diag::err_acc_wrong_dsa)
            << getOpenACCClauseName(ACCC_linear)
            << getOpenACCClauseName(IsUniformedThis ? ACCC_uniform : ACCC_linear)
            << E->getSourceRange();
        Diag(UniformedLinearThis->getExprLoc(), diag::note_acc_explicit_dsa)
            << getOpenACCClauseName(IsUniformedThis ? ACCC_uniform
                                                   : ACCC_linear);
        continue;
      }
      UniformedLinearThis = E;
      if (E->isValueDependent() || E->isTypeDependent() ||
          E->isInstantiationDependent() || E->containsUnexpandedParameterPack())
        continue;
      (void)CheckOpenACCLinearDecl(/*D=*/nullptr, E->getExprLoc(), LinKind,
                                  E->getType());
      continue;
    }
    Diag(E->getExprLoc(), diag::err_acc_param_or_this_in_clause)
        << FD->getDeclName() << (isa<CXXMethodDecl>(ADecl) ? 1 : 0);
  }
  Expr *Step = nullptr;
  Expr *NewStep = nullptr;
  SmallVector<Expr *, 4> NewSteps;
  for (auto *E : Steps) {
    // Skip the same step expression, it was checked already.
    if (Step == E || !E) {
      NewSteps.push_back(E ? NewStep : nullptr);
      continue;
    }
    Step = E;
    if (auto *DRE = dyn_cast<DeclRefExpr>(Step))
      if (auto *PVD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
        auto *CanonPVD = PVD->getCanonicalDecl();
        if (UniformedArgs.count(CanonPVD) == 0) {
          Diag(Step->getExprLoc(), diag::err_acc_expected_uniform_param)
              << Step->getSourceRange();
        } else if (E->isValueDependent() || E->isTypeDependent() ||
                   E->isInstantiationDependent() ||
                   E->containsUnexpandedParameterPack() ||
                   CanonPVD->getType()->hasIntegerRepresentation())
          NewSteps.push_back(Step);
        else {
          Diag(Step->getExprLoc(), diag::err_acc_expected_int_param)
              << Step->getSourceRange();
        }
        continue;
      }
    NewStep = Step;
    if (Step && !Step->isValueDependent() && !Step->isTypeDependent() &&
        !Step->isInstantiationDependent() &&
        !Step->containsUnexpandedParameterPack()) {
      NewStep = PerformOpenACCImplicitIntegerConversion(Step->getExprLoc(), Step)
                    .get();
      if (NewStep)
        NewStep = VerifyIntegerConstantExpression(NewStep).get();
    }
    NewSteps.push_back(NewStep);
  }
  auto *NewAttr = ACCDeclareSimdDeclAttr::CreateImplicit(
      Context, BS, SL.get(), const_cast<Expr **>(Uniforms.data()),
      Uniforms.size(), const_cast<Expr **>(Aligneds.data()), Aligneds.size(),
      const_cast<Expr **>(NewAligns.data()), NewAligns.size(),
      const_cast<Expr **>(Linears.data()), Linears.size(),
      const_cast<unsigned *>(LinModifiers.data()), LinModifiers.size(),
      NewSteps.data(), NewSteps.size(), SR);
  ADecl->addAttr(NewAttr);
  return ConvertDeclToDeclGroup(ADecl);
}

StmtResult Sema::ActOnOpenACCParallelDirective(ArrayRef<ACCClause *> Clauses,
                                              Stmt *AStmt,
                                              SourceLocation StartLoc,
                                              SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  getCurFunction()->setHasBranchProtectedScope();

  return ACCParallelDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt,
                                      DSAStack->isCancelRegion());
}

namespace {
/// \brief Helper class for checking canonical form of the OpenACC loops and
/// extracting iteration space of each loop in the loop nest, that will be used
/// for IR generation.
class OpenACCIterationSpaceChecker {
  /// \brief Reference to Sema.
  Sema &SemaRef;
  /// \brief A location for diagnostics (when there is no some better location).
  SourceLocation DefaultLoc;
  /// \brief A location for diagnostics (when increment is not compatible).
  SourceLocation ConditionLoc;
  /// \brief A source location for referring to loop init later.
  SourceRange InitSrcRange;
  /// \brief A source location for referring to condition later.
  SourceRange ConditionSrcRange;
  /// \brief A source location for referring to increment later.
  SourceRange IncrementSrcRange;
  /// \brief Loop variable.
  ValueDecl *LCDecl = nullptr;
  /// \brief Reference to loop variable.
  Expr *LCRef = nullptr;
  /// \brief Lower bound (initializer for the var).
  Expr *LB = nullptr;
  /// \brief Upper bound.
  Expr *UB = nullptr;
  /// \brief Loop step (increment).
  Expr *Step = nullptr;
  /// \brief This flag is true when condition is one of:
  ///   Var <  UB
  ///   Var <= UB
  ///   UB  >  Var
  ///   UB  >= Var
  bool TestIsLessOp = false;
  /// \brief This flag is true when condition is strict ( < or > ).
  bool TestIsStrictOp = false;
  /// \brief This flag is true when step is subtracted on each iteration.
  bool SubtractStep = false;

public:
  OpenACCIterationSpaceChecker(Sema &SemaRef, SourceLocation DefaultLoc)
      : SemaRef(SemaRef), DefaultLoc(DefaultLoc), ConditionLoc(DefaultLoc) {}
  /// \brief Check init-expr for canonical loop form and save loop counter
  /// variable - #Var and its initialization value - #LB.
  bool CheckInit(Stmt *S, bool EmitDiags = true);
  /// \brief Check test-expr for canonical form, save upper-bound (#UB), flags
  /// for less/greater and for strict/non-strict comparison.
  bool CheckCond(Expr *S);
  /// \brief Check incr-expr for canonical loop form and return true if it
  /// does not conform, otherwise save loop step (#Step).
  bool CheckInc(Expr *S);
  /// \brief Return the loop counter variable.
  ValueDecl *GetLoopDecl() const { return LCDecl; }
  /// \brief Return the reference expression to loop counter variable.
  Expr *GetLoopDeclRefExpr() const { return LCRef; }
  /// \brief Source range of the loop init.
  SourceRange GetInitSrcRange() const { return InitSrcRange; }
  /// \brief Source range of the loop condition.
  SourceRange GetConditionSrcRange() const { return ConditionSrcRange; }
  /// \brief Source range of the loop increment.
  SourceRange GetIncrementSrcRange() const { return IncrementSrcRange; }
  /// \brief True if the step should be subtracted.
  bool ShouldSubtractStep() const { return SubtractStep; }
  /// \brief Build the expression to calculate the number of iterations.
  Expr *
  BuildNumIterations(Scope *S, const bool LimitedType,
                     llvm::MapVector<Expr *, DeclRefExpr *> &Captures) const;
  /// \brief Build the precondition expression for the loops.
  Expr *BuildPreCond(Scope *S, Expr *Cond,
                     llvm::MapVector<Expr *, DeclRefExpr *> &Captures) const;
  /// \brief Build reference expression to the counter be used for codegen.
  DeclRefExpr *BuildCounterVar(llvm::MapVector<Expr *, DeclRefExpr *> &Captures,
                               DSAStackTy &DSA) const;
  /// \brief Build reference expression to the private counter be used for
  /// codegen.
  Expr *BuildPrivateCounterVar() const;
  /// \brief Build initialization of the counter be used for codegen.
  Expr *BuildCounterInit() const;
  /// \brief Build step of the counter be used for codegen.
  Expr *BuildCounterStep() const;
  /// \brief Return true if any expression is dependent.
  bool Dependent() const;

private:
  /// \brief Check the right-hand side of an assignment in the increment
  /// expression.
  bool CheckIncRHS(Expr *RHS);
  /// \brief Helper to set loop counter variable and its initializer.
  bool SetLCDeclAndLB(ValueDecl *NewLCDecl, Expr *NewDeclRefExpr, Expr *NewLB);
  /// \brief Helper to set upper bound.
  bool SetUB(Expr *NewUB, bool LessOp, bool StrictOp, SourceRange SR,
             SourceLocation SL);
  /// \brief Helper to set loop increment.
  bool SetStep(Expr *NewStep, bool Subtract);
};

bool OpenACCIterationSpaceChecker::Dependent() const {
  if (!LCDecl) {
    assert(!LB && !UB && !Step);
    return false;
  }
  return LCDecl->getType()->isDependentType() ||
         (LB && LB->isValueDependent()) || (UB && UB->isValueDependent()) ||
         (Step && Step->isValueDependent());
}

bool OpenACCIterationSpaceChecker::SetLCDeclAndLB(ValueDecl *NewLCDecl,
                                                 Expr *NewLCRefExpr,
                                                 Expr *NewLB) {
  // State consistency checking to ensure correct usage.
  assert(LCDecl == nullptr && LB == nullptr && LCRef == nullptr &&
         UB == nullptr && Step == nullptr && !TestIsLessOp && !TestIsStrictOp);
  if (!NewLCDecl || !NewLB)
    return true;
  LCDecl = getCanonicalDecl(NewLCDecl);
  LCRef = NewLCRefExpr;
  if (auto *CE = dyn_cast_or_null<CXXConstructExpr>(NewLB))
    if (const CXXConstructorDecl *Ctor = CE->getConstructor())
      if ((Ctor->isCopyOrMoveConstructor() ||
           Ctor->isConvertingConstructor(/*AllowExplicit=*/false)) &&
          CE->getNumArgs() > 0 && CE->getArg(0) != nullptr)
        NewLB = CE->getArg(0)->IgnoreParenImpCasts();
  LB = NewLB;
  return false;
}

bool OpenACCIterationSpaceChecker::SetUB(Expr *NewUB, bool LessOp, bool StrictOp,
                                        SourceRange SR, SourceLocation SL) {
  // State consistency checking to ensure correct usage.
  assert(LCDecl != nullptr && LB != nullptr && UB == nullptr &&
         Step == nullptr && !TestIsLessOp && !TestIsStrictOp);
  if (!NewUB)
    return true;
  UB = NewUB;
  TestIsLessOp = LessOp;
  TestIsStrictOp = StrictOp;
  ConditionSrcRange = SR;
  ConditionLoc = SL;
  return false;
}

bool OpenACCIterationSpaceChecker::SetStep(Expr *NewStep, bool Subtract) {
  // State consistency checking to ensure correct usage.
  assert(LCDecl != nullptr && LB != nullptr && Step == nullptr);
  if (!NewStep)
    return true;
  if (!NewStep->isValueDependent()) {
    // Check that the step is integer expression.
    SourceLocation StepLoc = NewStep->getLocStart();
    ExprResult Val = SemaRef.PerformOpenACCImplicitIntegerConversion(
        StepLoc, getExprAsWritten(NewStep));
    if (Val.isInvalid())
      return true;
    NewStep = Val.get();

    // OpenACC [2.6, Canonical Loop Form, Restrictions]
    //  If test-expr is of form var relational-op b and relational-op is < or
    //  <= then incr-expr must cause var to increase on each iteration of the
    //  loop. If test-expr is of form var relational-op b and relational-op is
    //  > or >= then incr-expr must cause var to decrease on each iteration of
    //  the loop.
    //  If test-expr is of form b relational-op var and relational-op is < or
    //  <= then incr-expr must cause var to decrease on each iteration of the
    //  loop. If test-expr is of form b relational-op var and relational-op is
    //  > or >= then incr-expr must cause var to increase on each iteration of
    //  the loop.
    llvm::APSInt Result;
    bool IsConstant = NewStep->isIntegerConstantExpr(Result, SemaRef.Context);
    bool IsUnsigned = !NewStep->getType()->hasSignedIntegerRepresentation();
    bool IsConstNeg =
        IsConstant && Result.isSigned() && (Subtract != Result.isNegative());
    bool IsConstPos =
        IsConstant && Result.isSigned() && (Subtract == Result.isNegative());
    bool IsConstZero = IsConstant && !Result.getBoolValue();
    if (UB && (IsConstZero ||
               (TestIsLessOp ? (IsConstNeg || (IsUnsigned && Subtract))
                             : (IsConstPos || (IsUnsigned && !Subtract))))) {
      SemaRef.Diag(NewStep->getExprLoc(),
                   diag::err_acc_loop_incr_not_compatible)
          << LCDecl << TestIsLessOp << NewStep->getSourceRange();
      SemaRef.Diag(ConditionLoc,
                   diag::note_acc_loop_cond_requres_compatible_incr)
          << TestIsLessOp << ConditionSrcRange;
      return true;
    }
    if (TestIsLessOp == Subtract) {
      NewStep =
          SemaRef.CreateBuiltinUnaryOp(NewStep->getExprLoc(), UO_Minus, NewStep)
              .get();
      Subtract = !Subtract;
    }
  }

  Step = NewStep;
  SubtractStep = Subtract;
  return false;
}

bool OpenACCIterationSpaceChecker::CheckInit(Stmt *S, bool EmitDiags) {
  // Check init-expr for canonical loop form and save loop counter
  // variable - #Var and its initialization value - #LB.
  // OpenACC [2.6] Canonical loop form. init-expr may be one of the following:
  //   var = lb
  //   integer-type var = lb
  //   random-access-iterator-type var = lb
  //   pointer-type var = lb
  //
  if (!S) {
    if (EmitDiags) {
      SemaRef.Diag(DefaultLoc, diag::err_acc_loop_not_canonical_init);
    }
    return true;
  }
  if (auto *ExprTemp = dyn_cast<ExprWithCleanups>(S))
    if (!ExprTemp->cleanupsHaveSideEffects())
      S = ExprTemp->getSubExpr();

  InitSrcRange = S->getSourceRange();
  if (Expr *E = dyn_cast<Expr>(S))
    S = E->IgnoreParens();
  if (auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->getOpcode() == BO_Assign) {
      auto *LHS = BO->getLHS()->IgnoreParens();
      if (auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
        if (auto *CED = dyn_cast<ACCCapturedExprDecl>(DRE->getDecl()))
          if (auto *ME = dyn_cast<MemberExpr>(getExprAsWritten(CED->getInit())))
            return SetLCDeclAndLB(ME->getMemberDecl(), ME, BO->getRHS());
        return SetLCDeclAndLB(DRE->getDecl(), DRE, BO->getRHS());
      }
      if (auto *ME = dyn_cast<MemberExpr>(LHS)) {
        if (ME->isArrow() &&
            isa<CXXThisExpr>(ME->getBase()->IgnoreParenImpCasts()))
          return SetLCDeclAndLB(ME->getMemberDecl(), ME, BO->getRHS());
      }
    }
  } else if (auto *DS = dyn_cast<DeclStmt>(S)) {
    if (DS->isSingleDecl()) {
      if (auto *Var = dyn_cast_or_null<VarDecl>(DS->getSingleDecl())) {
        if (Var->hasInit() && !Var->getType()->isReferenceType()) {
          // Accept non-canonical init form here but emit ext. warning.
          if (Var->getInitStyle() != VarDecl::CInit && EmitDiags)
            SemaRef.Diag(S->getLocStart(),
                         diag::ext_acc_loop_not_canonical_init)
                << S->getSourceRange();
          return SetLCDeclAndLB(Var, nullptr, Var->getInit());
        }
      }
    }
  } else if (auto *CE = dyn_cast<CXXOperatorCallExpr>(S)) {
    if (CE->getOperator() == OO_Equal) {
      auto *LHS = CE->getArg(0);
      if (auto *DRE = dyn_cast<DeclRefExpr>(LHS)) {
        if (auto *CED = dyn_cast<ACCCapturedExprDecl>(DRE->getDecl()))
          if (auto *ME = dyn_cast<MemberExpr>(getExprAsWritten(CED->getInit())))
            return SetLCDeclAndLB(ME->getMemberDecl(), ME, BO->getRHS());
        return SetLCDeclAndLB(DRE->getDecl(), DRE, CE->getArg(1));
      }
      if (auto *ME = dyn_cast<MemberExpr>(LHS)) {
        if (ME->isArrow() &&
            isa<CXXThisExpr>(ME->getBase()->IgnoreParenImpCasts()))
          return SetLCDeclAndLB(ME->getMemberDecl(), ME, BO->getRHS());
      }
    }
  }

  if (Dependent() || SemaRef.CurContext->isDependentContext())
    return false;
  if (EmitDiags) {
    SemaRef.Diag(S->getLocStart(), diag::err_acc_loop_not_canonical_init)
        << S->getSourceRange();
  }
  return true;
}

/// \brief Ignore parenthesizes, implicit casts, copy constructor and return the
/// variable (which may be the loop variable) if possible.
static const ValueDecl *GetInitLCDecl(Expr *E) {
  if (!E)
    return nullptr;
  E = getExprAsWritten(E);
  if (auto *CE = dyn_cast_or_null<CXXConstructExpr>(E))
    if (const CXXConstructorDecl *Ctor = CE->getConstructor())
      if ((Ctor->isCopyOrMoveConstructor() ||
           Ctor->isConvertingConstructor(/*AllowExplicit=*/false)) &&
          CE->getNumArgs() > 0 && CE->getArg(0) != nullptr)
        E = CE->getArg(0)->IgnoreParenImpCasts();
  if (auto *DRE = dyn_cast_or_null<DeclRefExpr>(E)) {
    if (auto *VD = dyn_cast<VarDecl>(DRE->getDecl()))
      return getCanonicalDecl(VD);
  }
  if (auto *ME = dyn_cast_or_null<MemberExpr>(E))
    if (ME->isArrow() && isa<CXXThisExpr>(ME->getBase()->IgnoreParenImpCasts()))
      return getCanonicalDecl(ME->getMemberDecl());
  return nullptr;
}

bool OpenACCIterationSpaceChecker::CheckCond(Expr *S) {
  // Check test-expr for canonical form, save upper-bound UB, flags for
  // less/greater and for strict/non-strict comparison.
  // OpenACC [2.6] Canonical loop form. Test-expr may be one of the following:
  //   var relational-op b
  //   b relational-op var
  //
  if (!S) {
    SemaRef.Diag(DefaultLoc, diag::err_acc_loop_not_canonical_cond) << LCDecl;
    return true;
  }
  S = getExprAsWritten(S);
  SourceLocation CondLoc = S->getLocStart();
  if (auto *BO = dyn_cast<BinaryOperator>(S)) {
    if (BO->isRelationalOp()) {
      if (GetInitLCDecl(BO->getLHS()) == LCDecl)
        return SetUB(BO->getRHS(),
                     (BO->getOpcode() == BO_LT || BO->getOpcode() == BO_LE),
                     (BO->getOpcode() == BO_LT || BO->getOpcode() == BO_GT),
                     BO->getSourceRange(), BO->getOperatorLoc());
      if (GetInitLCDecl(BO->getRHS()) == LCDecl)
        return SetUB(BO->getLHS(),
                     (BO->getOpcode() == BO_GT || BO->getOpcode() == BO_GE),
                     (BO->getOpcode() == BO_LT || BO->getOpcode() == BO_GT),
                     BO->getSourceRange(), BO->getOperatorLoc());
    }
  } else if (auto *CE = dyn_cast<CXXOperatorCallExpr>(S)) {
    if (CE->getNumArgs() == 2) {
      auto Op = CE->getOperator();
      switch (Op) {
      case OO_Greater:
      case OO_GreaterEqual:
      case OO_Less:
      case OO_LessEqual:
        if (GetInitLCDecl(CE->getArg(0)) == LCDecl)
          return SetUB(CE->getArg(1), Op == OO_Less || Op == OO_LessEqual,
                       Op == OO_Less || Op == OO_Greater, CE->getSourceRange(),
                       CE->getOperatorLoc());
        if (GetInitLCDecl(CE->getArg(1)) == LCDecl)
          return SetUB(CE->getArg(0), Op == OO_Greater || Op == OO_GreaterEqual,
                       Op == OO_Less || Op == OO_Greater, CE->getSourceRange(),
                       CE->getOperatorLoc());
        break;
      default:
        break;
      }
    }
  }
  if (Dependent() || SemaRef.CurContext->isDependentContext())
    return false;
  SemaRef.Diag(CondLoc, diag::err_acc_loop_not_canonical_cond)
      << S->getSourceRange() << LCDecl;
  return true;
}

bool OpenACCIterationSpaceChecker::CheckIncRHS(Expr *RHS) {
  // RHS of canonical loop form increment can be:
  //   var + incr
  //   incr + var
  //   var - incr
  //
  RHS = RHS->IgnoreParenImpCasts();
  if (auto *BO = dyn_cast<BinaryOperator>(RHS)) {
    if (BO->isAdditiveOp()) {
      bool IsAdd = BO->getOpcode() == BO_Add;
      if (GetInitLCDecl(BO->getLHS()) == LCDecl)
        return SetStep(BO->getRHS(), !IsAdd);
      if (IsAdd && GetInitLCDecl(BO->getRHS()) == LCDecl)
        return SetStep(BO->getLHS(), false);
    }
  } else if (auto *CE = dyn_cast<CXXOperatorCallExpr>(RHS)) {
    bool IsAdd = CE->getOperator() == OO_Plus;
    if ((IsAdd || CE->getOperator() == OO_Minus) && CE->getNumArgs() == 2) {
      if (GetInitLCDecl(CE->getArg(0)) == LCDecl)
        return SetStep(CE->getArg(1), !IsAdd);
      if (IsAdd && GetInitLCDecl(CE->getArg(1)) == LCDecl)
        return SetStep(CE->getArg(0), false);
    }
  }
  if (Dependent() || SemaRef.CurContext->isDependentContext())
    return false;
  SemaRef.Diag(RHS->getLocStart(), diag::err_acc_loop_not_canonical_incr)
      << RHS->getSourceRange() << LCDecl;
  return true;
}

bool OpenACCIterationSpaceChecker::CheckInc(Expr *S) {
  // Check incr-expr for canonical loop form and return true if it
  // does not conform.
  // OpenACC [2.6] Canonical loop form. Test-expr may be one of the following:
  //   ++var
  //   var++
  //   --var
  //   var--
  //   var += incr
  //   var -= incr
  //   var = var + incr
  //   var = incr + var
  //   var = var - incr
  //
  if (!S) {
    SemaRef.Diag(DefaultLoc, diag::err_acc_loop_not_canonical_incr) << LCDecl;
    return true;
  }
  if (auto *ExprTemp = dyn_cast<ExprWithCleanups>(S))
    if (!ExprTemp->cleanupsHaveSideEffects())
      S = ExprTemp->getSubExpr();

  IncrementSrcRange = S->getSourceRange();
  S = S->IgnoreParens();
  if (auto *UO = dyn_cast<UnaryOperator>(S)) {
    if (UO->isIncrementDecrementOp() &&
        GetInitLCDecl(UO->getSubExpr()) == LCDecl)
      return SetStep(SemaRef
                         .ActOnIntegerConstant(UO->getLocStart(),
                                               (UO->isDecrementOp() ? -1 : 1))
                         .get(),
                     false);
  } else if (auto *BO = dyn_cast<BinaryOperator>(S)) {
    switch (BO->getOpcode()) {
    case BO_AddAssign:
    case BO_SubAssign:
      if (GetInitLCDecl(BO->getLHS()) == LCDecl)
        return SetStep(BO->getRHS(), BO->getOpcode() == BO_SubAssign);
      break;
    case BO_Assign:
      if (GetInitLCDecl(BO->getLHS()) == LCDecl)
        return CheckIncRHS(BO->getRHS());
      break;
    default:
      break;
    }
  } else if (auto *CE = dyn_cast<CXXOperatorCallExpr>(S)) {
    switch (CE->getOperator()) {
    case OO_PlusPlus:
    case OO_MinusMinus:
      if (GetInitLCDecl(CE->getArg(0)) == LCDecl)
        return SetStep(SemaRef
                           .ActOnIntegerConstant(
                               CE->getLocStart(),
                               ((CE->getOperator() == OO_MinusMinus) ? -1 : 1))
                           .get(),
                       false);
      break;
    case OO_PlusEqual:
    case OO_MinusEqual:
      if (GetInitLCDecl(CE->getArg(0)) == LCDecl)
        return SetStep(CE->getArg(1), CE->getOperator() == OO_MinusEqual);
      break;
    case OO_Equal:
      if (GetInitLCDecl(CE->getArg(0)) == LCDecl)
        return CheckIncRHS(CE->getArg(1));
      break;
    default:
      break;
    }
  }
  if (Dependent() || SemaRef.CurContext->isDependentContext())
    return false;
  SemaRef.Diag(S->getLocStart(), diag::err_acc_loop_not_canonical_incr)
      << S->getSourceRange() << LCDecl;
  return true;
}

static ExprResult
tryBuildCapture(Sema &SemaRef, Expr *Capture,
                llvm::MapVector<Expr *, DeclRefExpr *> &Captures) {
  if (SemaRef.CurContext->isDependentContext())
    return ExprResult(Capture);
  if (Capture->isEvaluatable(SemaRef.Context, Expr::SE_AllowSideEffects))
    return SemaRef.PerformImplicitConversion(
        Capture->IgnoreImpCasts(), Capture->getType(), Sema::AA_Converting,
        /*AllowExplicit=*/true);
  auto I = Captures.find(Capture);
  if (I != Captures.end())
    return buildCapture(SemaRef, Capture, I->second);
  DeclRefExpr *Ref = nullptr;
  ExprResult Res = buildCapture(SemaRef, Capture, Ref);
  Captures[Capture] = Ref;
  return Res;
}

/// \brief Build the expression to calculate the number of iterations.
Expr *OpenACCIterationSpaceChecker::BuildNumIterations(
    Scope *S, const bool LimitedType,
    llvm::MapVector<Expr *, DeclRefExpr *> &Captures) const {
  ExprResult Diff;
  auto VarType = LCDecl->getType().getNonReferenceType();
  if (VarType->isIntegerType() || VarType->isPointerType() ||
      SemaRef.getLangOpts().CPlusPlus) {
    // Upper - Lower
    auto *UBExpr = TestIsLessOp ? UB : LB;
    auto *LBExpr = TestIsLessOp ? LB : UB;
    Expr *Upper = tryBuildCapture(SemaRef, UBExpr, Captures).get();
    Expr *Lower = tryBuildCapture(SemaRef, LBExpr, Captures).get();
    if (!Upper || !Lower)
      return nullptr;

    Diff = SemaRef.BuildBinOp(S, DefaultLoc, BO_Sub, Upper, Lower);

    if (!Diff.isUsable() && VarType->getAsCXXRecordDecl()) {
      // BuildBinOp already emitted error, this one is to point user to upper
      // and lower bound, and to tell what is passed to 'operator-'.
      SemaRef.Diag(Upper->getLocStart(), diag::err_acc_loop_diff_cxx)
          << Upper->getSourceRange() << Lower->getSourceRange();
      return nullptr;
    }
  }

  if (!Diff.isUsable())
    return nullptr;

  // Upper - Lower [- 1]
  if (TestIsStrictOp)
    Diff = SemaRef.BuildBinOp(
        S, DefaultLoc, BO_Sub, Diff.get(),
        SemaRef.ActOnIntegerConstant(SourceLocation(), 1).get());
  if (!Diff.isUsable())
    return nullptr;

  // Upper - Lower [- 1] + Step
  auto NewStep = tryBuildCapture(SemaRef, Step, Captures);
  if (!NewStep.isUsable())
    return nullptr;
  Diff = SemaRef.BuildBinOp(S, DefaultLoc, BO_Add, Diff.get(), NewStep.get());
  if (!Diff.isUsable())
    return nullptr;

  // Parentheses (for dumping/debugging purposes only).
  Diff = SemaRef.ActOnParenExpr(DefaultLoc, DefaultLoc, Diff.get());
  if (!Diff.isUsable())
    return nullptr;

  // (Upper - Lower [- 1] + Step) / Step
  Diff = SemaRef.BuildBinOp(S, DefaultLoc, BO_Div, Diff.get(), NewStep.get());
  if (!Diff.isUsable())
    return nullptr;

  // OpenACC runtime requires 32-bit or 64-bit loop variables.
  QualType Type = Diff.get()->getType();
  auto &C = SemaRef.Context;
  bool UseVarType = VarType->hasIntegerRepresentation() &&
                    C.getTypeSize(Type) > C.getTypeSize(VarType);
  if (!Type->isIntegerType() || UseVarType) {
    unsigned NewSize =
        UseVarType ? C.getTypeSize(VarType) : C.getTypeSize(Type);
    bool IsSigned = UseVarType ? VarType->hasSignedIntegerRepresentation()
                               : Type->hasSignedIntegerRepresentation();
    Type = C.getIntTypeForBitwidth(NewSize, IsSigned);
    if (!SemaRef.Context.hasSameType(Diff.get()->getType(), Type)) {
      Diff = SemaRef.PerformImplicitConversion(
          Diff.get(), Type, Sema::AA_Converting, /*AllowExplicit=*/true);
      if (!Diff.isUsable())
        return nullptr;
    }
  }
  if (LimitedType) {
    unsigned NewSize = (C.getTypeSize(Type) > 32) ? 64 : 32;
    if (NewSize != C.getTypeSize(Type)) {
      if (NewSize < C.getTypeSize(Type)) {
        assert(NewSize == 64 && "incorrect loop var size");
        SemaRef.Diag(DefaultLoc, diag::warn_acc_loop_64_bit_var)
            << InitSrcRange << ConditionSrcRange;
      }
      QualType NewType = C.getIntTypeForBitwidth(
          NewSize, Type->hasSignedIntegerRepresentation() ||
                       C.getTypeSize(Type) < NewSize);
      if (!SemaRef.Context.hasSameType(Diff.get()->getType(), NewType)) {
        Diff = SemaRef.PerformImplicitConversion(Diff.get(), NewType,
                                                 Sema::AA_Converting, true);
        if (!Diff.isUsable())
          return nullptr;
      }
    }
  }

  return Diff.get();
}

Expr *OpenACCIterationSpaceChecker::BuildPreCond(
    Scope *S, Expr *Cond,
    llvm::MapVector<Expr *, DeclRefExpr *> &Captures) const {
  // Try to build LB <op> UB, where <op> is <, >, <=, or >=.
  bool Suppress = SemaRef.getDiagnostics().getSuppressAllDiagnostics();
  SemaRef.getDiagnostics().setSuppressAllDiagnostics(/*Val=*/true);

  auto NewLB = tryBuildCapture(SemaRef, LB, Captures);
  auto NewUB = tryBuildCapture(SemaRef, UB, Captures);
  if (!NewLB.isUsable() || !NewUB.isUsable())
    return nullptr;

  auto CondExpr = SemaRef.BuildBinOp(
      S, DefaultLoc, TestIsLessOp ? (TestIsStrictOp ? BO_LT : BO_LE)
                                  : (TestIsStrictOp ? BO_GT : BO_GE),
      NewLB.get(), NewUB.get());
  if (CondExpr.isUsable()) {
    if (!SemaRef.Context.hasSameUnqualifiedType(CondExpr.get()->getType(),
                                                SemaRef.Context.BoolTy))
      CondExpr = SemaRef.PerformImplicitConversion(
          CondExpr.get(), SemaRef.Context.BoolTy, /*Action=*/Sema::AA_Casting,
          /*AllowExplicit=*/true);
  }
  SemaRef.getDiagnostics().setSuppressAllDiagnostics(Suppress);
  // Otherwise use original loop conditon and evaluate it in runtime.
  return CondExpr.isUsable() ? CondExpr.get() : Cond;
}

/// \brief Build reference expression to the counter be used for codegen.
DeclRefExpr *OpenACCIterationSpaceChecker::BuildCounterVar(
    llvm::MapVector<Expr *, DeclRefExpr *> &Captures, DSAStackTy &DSA) const {
  auto *VD = dyn_cast<VarDecl>(LCDecl);
  if (!VD) {
    VD = SemaRef.IsOpenACCCapturedDecl(LCDecl);
    auto *Ref = buildDeclRefExpr(
        SemaRef, VD, VD->getType().getNonReferenceType(), DefaultLoc);
    DSAStackTy::DSAVarData Data = DSA.getTopDSA(LCDecl, /*FromParent=*/false);
    // If the loop control decl is explicitly marked as private, do not mark it
    // as captured again.
    if (!isOpenACCPrivate(Data.CKind) || !Data.RefExpr)
      Captures.insert(std::make_pair(LCRef, Ref));
    return Ref;
  }
  return buildDeclRefExpr(SemaRef, VD, VD->getType().getNonReferenceType(),
                          DefaultLoc);
}

Expr *OpenACCIterationSpaceChecker::BuildPrivateCounterVar() const {
  if (LCDecl && !LCDecl->isInvalidDecl()) {
    auto Type = LCDecl->getType().getNonReferenceType();
    auto *PrivateVar =
        buildVarDecl(SemaRef, DefaultLoc, Type, LCDecl->getName(),
                     LCDecl->hasAttrs() ? &LCDecl->getAttrs() : nullptr);
    if (PrivateVar->isInvalidDecl())
      return nullptr;
    return buildDeclRefExpr(SemaRef, PrivateVar, Type, DefaultLoc);
  }
  return nullptr;
}

/// \brief Build initialization of the counter to be used for codegen.
Expr *OpenACCIterationSpaceChecker::BuildCounterInit() const { return LB; }

/// \brief Build step of the counter be used for codegen.
Expr *OpenACCIterationSpaceChecker::BuildCounterStep() const { return Step; }

/// \brief Iteration space of a single for loop.
struct LoopIterationSpace final {
  /// \brief Condition of the loop.
  Expr *PreCond = nullptr;
  /// \brief This expression calculates the number of iterations in the loop.
  /// It is always possible to calculate it before starting the loop.
  Expr *NumIterations = nullptr;
  /// \brief The loop counter variable.
  Expr *CounterVar = nullptr;
  /// \brief Private loop counter variable.
  Expr *PrivateCounterVar = nullptr;
  /// \brief This is initializer for the initial value of #CounterVar.
  Expr *CounterInit = nullptr;
  /// \brief This is step for the #CounterVar used to generate its update:
  /// #CounterVar = #CounterInit + #CounterStep * CurrentIteration.
  Expr *CounterStep = nullptr;
  /// \brief Should step be subtracted?
  bool Subtract = false;
  /// \brief Source range of the loop init.
  SourceRange InitSrcRange;
  /// \brief Source range of the loop condition.
  SourceRange CondSrcRange;
  /// \brief Source range of the loop increment.
  SourceRange IncSrcRange;
};

} // namespace

void Sema::ActOnOpenACCLoopInitialization(SourceLocation ForLoc, Stmt *Init) {
  assert(getLangOpts().OpenACC && "OpenACC is not active.");
  assert(Init && "Expected loop in canonical form.");
  unsigned AssociatedLoops = DSAStack->getAssociatedLoops();
  if (AssociatedLoops > 0 &&
      isOpenACCLoopDirective(DSAStack->getCurrentDirective())) {
    OpenACCIterationSpaceChecker ISC(*this, ForLoc);
    if (!ISC.CheckInit(Init, /*EmitDiags=*/false)) {
      if (auto *D = ISC.GetLoopDecl()) {
        auto *VD = dyn_cast<VarDecl>(D);
        if (!VD) {
          if (auto *Private = IsOpenACCCapturedDecl(D))
            VD = Private;
          else {
            auto *Ref = buildCapture(*this, D, ISC.GetLoopDeclRefExpr(),
                                     /*WithInit=*/false);
            VD = cast<VarDecl>(Ref->getDecl());
          }
        }
        DSAStack->addLoopControlVariable(D, VD);
      }
    }
    DSAStack->setAssociatedLoops(AssociatedLoops - 1);
  }
}

/// \brief Called on a for stmt to check and extract its iteration space
/// for further processing (such as collapsing).
static bool CheckOpenACCIterationSpace(
    OpenACCDirectiveKind DKind, Stmt *S, Sema &SemaRef, DSAStackTy &DSA,
    unsigned CurrentNestedLoopCount, unsigned NestedLoopCount,
    Expr *CollapseLoopCountExpr, Expr *OrderedLoopCountExpr,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA,
    LoopIterationSpace &ResultIterSpace,
    llvm::MapVector<Expr *, DeclRefExpr *> &Captures) {
  // OpenACC [2.6, Canonical Loop Form]
  //   for (init-expr; test-expr; incr-expr) structured-block
  auto *For = dyn_cast_or_null<ForStmt>(S);
  if (!For) {
    SemaRef.Diag(S->getLocStart(), diag::err_acc_not_for)
        << (CollapseLoopCountExpr != nullptr || OrderedLoopCountExpr != nullptr)
        << getOpenACCDirectiveName(DKind) << NestedLoopCount
        << (CurrentNestedLoopCount > 0) << CurrentNestedLoopCount;
    if (NestedLoopCount > 1) {
      if (CollapseLoopCountExpr && OrderedLoopCountExpr)
        SemaRef.Diag(DSA.getConstructLoc(),
                     diag::note_acc_collapse_ordered_expr)
            << 2 << CollapseLoopCountExpr->getSourceRange()
            << OrderedLoopCountExpr->getSourceRange();
      else if (CollapseLoopCountExpr)
        SemaRef.Diag(CollapseLoopCountExpr->getExprLoc(),
                     diag::note_acc_collapse_ordered_expr)
            << 0 << CollapseLoopCountExpr->getSourceRange();
      else
        SemaRef.Diag(OrderedLoopCountExpr->getExprLoc(),
                     diag::note_acc_collapse_ordered_expr)
            << 1 << OrderedLoopCountExpr->getSourceRange();
    }
    return true;
  }
  assert(For->getBody());

  OpenACCIterationSpaceChecker ISC(SemaRef, For->getForLoc());

  // Check init.
  auto Init = For->getInit();
  if (ISC.CheckInit(Init))
    return true;

  bool HasErrors = false;

  // Check loop variable's type.
  if (auto *LCDecl = ISC.GetLoopDecl()) {
    auto *LoopDeclRefExpr = ISC.GetLoopDeclRefExpr();

    // OpenACC [2.6, Canonical Loop Form]
    // Var is one of the following:
    //   A variable of signed or unsigned integer type.
    //   For C++, a variable of a random access iterator type.
    //   For C, a variable of a pointer type.
    auto VarType = LCDecl->getType().getNonReferenceType();
    if (!VarType->isDependentType() && !VarType->isIntegerType() &&
        !VarType->isPointerType() &&
        !(SemaRef.getLangOpts().CPlusPlus && VarType->isOverloadableType())) {
      SemaRef.Diag(Init->getLocStart(), diag::err_acc_loop_variable_type)
          << SemaRef.getLangOpts().CPlusPlus;
      HasErrors = true;
    }

    // OpenACC, 2.14.1.1 Data-sharing Attribute Rules for Variables Referenced in
    // a Construct
    // The loop iteration variable(s) in the associated for-loop(s) of a for or
    // parallel for construct is (are) private.
    // The loop iteration variable in the associated for-loop of a simd
    // construct with just one associated for-loop is linear with a
    // constant-linear-step that is the increment of the associated for-loop.
    // Exclude loop var from the list of variables with implicitly defined data
    // sharing attributes.
    VarsWithImplicitDSA.erase(LCDecl);

    // OpenACC [2.14.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct, C/C++].
    // The loop iteration variable in the associated for-loop of a simd
    // construct with just one associated for-loop may be listed in a linear
    // clause with a constant-linear-step that is the increment of the
    // associated for-loop.
    // The loop iteration variable(s) in the associated for-loop(s) of a for or
    // parallel for construct may be listed in a private or lastprivate clause.
    DSAStackTy::DSAVarData DVar = DSA.getTopDSA(LCDecl, false);
    // If LoopVarRefExpr is nullptr it means the corresponding loop variable is
    // declared in the loop and it is predetermined as a private.
    auto PredeterminedCKind =
        isOpenACCSimdDirective(DKind)
            ? ((NestedLoopCount == 1) ? ACCC_linear : ACCC_lastprivate)
            : ACCC_private;
    if (((isOpenACCSimdDirective(DKind) && DVar.CKind != ACCC_unknown &&
          DVar.CKind != PredeterminedCKind) ||
         ((isOpenACCWorksharingDirective(DKind) || DKind == ACCD_taskloop ||
           isOpenACCDistributeDirective(DKind)) &&
          !isOpenACCSimdDirective(DKind) && DVar.CKind != ACCC_unknown &&
          DVar.CKind != ACCC_private && DVar.CKind != ACCC_lastprivate)) &&
        (DVar.CKind != ACCC_private || DVar.RefExpr != nullptr)) {
      SemaRef.Diag(Init->getLocStart(), diag::err_acc_loop_var_dsa)
          << getOpenACCClauseName(DVar.CKind) << getOpenACCDirectiveName(DKind)
          << getOpenACCClauseName(PredeterminedCKind);
      if (DVar.RefExpr == nullptr)
        DVar.CKind = PredeterminedCKind;
      ReportOriginalDSA(SemaRef, &DSA, LCDecl, DVar, /*IsLoopIterVar=*/true);
      HasErrors = true;
    } else if (LoopDeclRefExpr != nullptr) {
      // Make the loop iteration variable private (for worksharing constructs),
      // linear (for simd directives with the only one associated loop) or
      // lastprivate (for simd directives with several collapsed or ordered
      // loops).
      if (DVar.CKind == ACCC_unknown)
        DVar = DSA.hasDSA(LCDecl, isOpenACCPrivate,
                          [](OpenACCDirectiveKind) -> bool { return true; },
                          /*FromParent=*/false);
      DSA.addDSA(LCDecl, LoopDeclRefExpr, PredeterminedCKind);
    }

    assert(isOpenACCLoopDirective(DKind) && "DSA for non-loop vars");

    // Check test-expr.
    HasErrors |= ISC.CheckCond(For->getCond());

    // Check incr-expr.
    HasErrors |= ISC.CheckInc(For->getInc());
  }

  if (ISC.Dependent() || SemaRef.CurContext->isDependentContext() || HasErrors)
    return HasErrors;

  // Build the loop's iteration space representation.
  ResultIterSpace.PreCond =
      ISC.BuildPreCond(DSA.getCurScope(), For->getCond(), Captures);
  ResultIterSpace.NumIterations = ISC.BuildNumIterations(
      DSA.getCurScope(),
      (isOpenACCWorksharingDirective(DKind) ||
       isOpenACCTaskLoopDirective(DKind) || isOpenACCDistributeDirective(DKind)),
      Captures);
  ResultIterSpace.CounterVar = ISC.BuildCounterVar(Captures, DSA);
  ResultIterSpace.PrivateCounterVar = ISC.BuildPrivateCounterVar();
  ResultIterSpace.CounterInit = ISC.BuildCounterInit();
  ResultIterSpace.CounterStep = ISC.BuildCounterStep();
  ResultIterSpace.InitSrcRange = ISC.GetInitSrcRange();
  ResultIterSpace.CondSrcRange = ISC.GetConditionSrcRange();
  ResultIterSpace.IncSrcRange = ISC.GetIncrementSrcRange();
  ResultIterSpace.Subtract = ISC.ShouldSubtractStep();

  HasErrors |= (ResultIterSpace.PreCond == nullptr ||
                ResultIterSpace.NumIterations == nullptr ||
                ResultIterSpace.CounterVar == nullptr ||
                ResultIterSpace.PrivateCounterVar == nullptr ||
                ResultIterSpace.CounterInit == nullptr ||
                ResultIterSpace.CounterStep == nullptr);

  return HasErrors;
}

/// \brief Build 'VarRef = Start.
static ExprResult
BuildCounterInit(Sema &SemaRef, Scope *S, SourceLocation Loc, ExprResult VarRef,
                 ExprResult Start,
                 llvm::MapVector<Expr *, DeclRefExpr *> &Captures) {
  // Build 'VarRef = Start.
  auto NewStart = tryBuildCapture(SemaRef, Start.get(), Captures);
  if (!NewStart.isUsable())
    return ExprError();
  if (!SemaRef.Context.hasSameType(NewStart.get()->getType(),
                                   VarRef.get()->getType())) {
    NewStart = SemaRef.PerformImplicitConversion(
        NewStart.get(), VarRef.get()->getType(), Sema::AA_Converting,
        /*AllowExplicit=*/true);
    if (!NewStart.isUsable())
      return ExprError();
  }

  auto Init =
      SemaRef.BuildBinOp(S, Loc, BO_Assign, VarRef.get(), NewStart.get());
  return Init;
}

/// \brief Build 'VarRef = Start + Iter * Step'.
static ExprResult
BuildCounterUpdate(Sema &SemaRef, Scope *S, SourceLocation Loc,
                   ExprResult VarRef, ExprResult Start, ExprResult Iter,
                   ExprResult Step, bool Subtract,
                   llvm::MapVector<Expr *, DeclRefExpr *> *Captures = nullptr) {
  // Add parentheses (for debugging purposes only).
  Iter = SemaRef.ActOnParenExpr(Loc, Loc, Iter.get());
  if (!VarRef.isUsable() || !Start.isUsable() || !Iter.isUsable() ||
      !Step.isUsable())
    return ExprError();

  ExprResult NewStep = Step;
  if (Captures)
    NewStep = tryBuildCapture(SemaRef, Step.get(), *Captures);
  if (NewStep.isInvalid())
    return ExprError();
  ExprResult Update =
      SemaRef.BuildBinOp(S, Loc, BO_Mul, Iter.get(), NewStep.get());
  if (!Update.isUsable())
    return ExprError();

  // Try to build 'VarRef = Start, VarRef (+|-)= Iter * Step' or
  // 'VarRef = Start (+|-) Iter * Step'.
  ExprResult NewStart = Start;
  if (Captures)
    NewStart = tryBuildCapture(SemaRef, Start.get(), *Captures);
  if (NewStart.isInvalid())
    return ExprError();

  // First attempt: try to build 'VarRef = Start, VarRef += Iter * Step'.
  ExprResult SavedUpdate = Update;
  ExprResult UpdateVal;
  if (VarRef.get()->getType()->isOverloadableType() ||
      NewStart.get()->getType()->isOverloadableType() ||
      Update.get()->getType()->isOverloadableType()) {
    bool Suppress = SemaRef.getDiagnostics().getSuppressAllDiagnostics();
    SemaRef.getDiagnostics().setSuppressAllDiagnostics(/*Val=*/true);
    Update =
        SemaRef.BuildBinOp(S, Loc, BO_Assign, VarRef.get(), NewStart.get());
    if (Update.isUsable()) {
      UpdateVal =
          SemaRef.BuildBinOp(S, Loc, Subtract ? BO_SubAssign : BO_AddAssign,
                             VarRef.get(), SavedUpdate.get());
      if (UpdateVal.isUsable()) {
        Update = SemaRef.CreateBuiltinBinOp(Loc, BO_Comma, Update.get(),
                                            UpdateVal.get());
      }
    }
    SemaRef.getDiagnostics().setSuppressAllDiagnostics(Suppress);
  }

  // Second attempt: try to build 'VarRef = Start (+|-) Iter * Step'.
  if (!Update.isUsable() || !UpdateVal.isUsable()) {
    Update = SemaRef.BuildBinOp(S, Loc, Subtract ? BO_Sub : BO_Add,
                                NewStart.get(), SavedUpdate.get());
    if (!Update.isUsable())
      return ExprError();

    if (!SemaRef.Context.hasSameType(Update.get()->getType(),
                                     VarRef.get()->getType())) {
      Update = SemaRef.PerformImplicitConversion(
          Update.get(), VarRef.get()->getType(), Sema::AA_Converting, true);
      if (!Update.isUsable())
        return ExprError();
    }

    Update = SemaRef.BuildBinOp(S, Loc, BO_Assign, VarRef.get(), Update.get());
  }
  return Update;
}

/// \brief Convert integer expression \a E to make it have at least \a Bits
/// bits.
static ExprResult WidenIterationCount(unsigned Bits, Expr *E, Sema &SemaRef) {
  if (E == nullptr)
    return ExprError();
  auto &C = SemaRef.Context;
  QualType OldType = E->getType();
  unsigned HasBits = C.getTypeSize(OldType);
  if (HasBits >= Bits)
    return ExprResult(E);
  // OK to convert to signed, because new type has more bits than old.
  QualType NewType = C.getIntTypeForBitwidth(Bits, /* Signed */ true);
  return SemaRef.PerformImplicitConversion(E, NewType, Sema::AA_Converting,
                                           true);
}

/// \brief Check if the given expression \a E is a constant integer that fits
/// into \a Bits bits.
static bool FitsInto(unsigned Bits, bool Signed, Expr *E, Sema &SemaRef) {
  if (E == nullptr)
    return false;
  llvm::APSInt Result;
  if (E->isIntegerConstantExpr(Result, SemaRef.Context))
    return Signed ? Result.isSignedIntN(Bits) : Result.isIntN(Bits);
  return false;
}

/// Build preinits statement for the given declarations.
static Stmt *buildPreInits(ASTContext &Context,
                           MutableArrayRef<Decl *> PreInits) {
  if (!PreInits.empty()) {
    return new (Context) DeclStmt(
        DeclGroupRef::Create(Context, PreInits.begin(), PreInits.size()),
        SourceLocation(), SourceLocation());
  }
  return nullptr;
}

/// Build preinits statement for the given declarations.
static Stmt *
buildPreInits(ASTContext &Context,
              const llvm::MapVector<Expr *, DeclRefExpr *> &Captures) {
  if (!Captures.empty()) {
    SmallVector<Decl *, 16> PreInits;
    for (auto &Pair : Captures)
      PreInits.push_back(Pair.second->getDecl());
    return buildPreInits(Context, PreInits);
  }
  return nullptr;
}

/// Build postupdate expression for the given list of postupdates expressions.
static Expr *buildPostUpdate(Sema &S, ArrayRef<Expr *> PostUpdates) {
  Expr *PostUpdate = nullptr;
  if (!PostUpdates.empty()) {
    for (auto *E : PostUpdates) {
      Expr *ConvE = S.BuildCStyleCastExpr(
                         E->getExprLoc(),
                         S.Context.getTrivialTypeSourceInfo(S.Context.VoidTy),
                         E->getExprLoc(), E)
                        .get();
      PostUpdate = PostUpdate
                       ? S.CreateBuiltinBinOp(ConvE->getExprLoc(), BO_Comma,
                                              PostUpdate, ConvE)
                             .get()
                       : ConvE;
    }
  }
  return PostUpdate;
}

/// \brief Called on a for stmt to check itself and nested loops (if any).
/// \return Returns 0 if one of the collapsed stmts is not canonical for loop,
/// number of collapsed loops otherwise.
static unsigned
CheckOpenACCLoop(OpenACCDirectiveKind DKind, Expr *CollapseLoopCountExpr,
                Expr *OrderedLoopCountExpr, Stmt *AStmt, Sema &SemaRef,
                DSAStackTy &DSA,
                llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA,
                ACCLoopDirective::HelperExprs &Built) {
  unsigned NestedLoopCount = 1;
  if (CollapseLoopCountExpr) {
    // Found 'collapse' clause - calculate collapse number.
    llvm::APSInt Result;
    if (CollapseLoopCountExpr->EvaluateAsInt(Result, SemaRef.getASTContext()))
      NestedLoopCount = Result.getLimitedValue();
  }
  if (OrderedLoopCountExpr) {
    // Found 'ordered' clause - calculate collapse number.
    llvm::APSInt Result;
    if (OrderedLoopCountExpr->EvaluateAsInt(Result, SemaRef.getASTContext())) {
      if (Result.getLimitedValue() < NestedLoopCount) {
        SemaRef.Diag(OrderedLoopCountExpr->getExprLoc(),
                     diag::err_acc_wrong_ordered_loop_count)
            << OrderedLoopCountExpr->getSourceRange();
        SemaRef.Diag(CollapseLoopCountExpr->getExprLoc(),
                     diag::note_acc_collapse_loop_count)
            << CollapseLoopCountExpr->getSourceRange();
      }
      NestedLoopCount = Result.getLimitedValue();
    }
  }
  // This is helper routine for loop directives (e.g., 'for', 'simd',
  // 'for simd', etc.).
  llvm::MapVector<Expr *, DeclRefExpr *> Captures;
  SmallVector<LoopIterationSpace, 4> IterSpaces;
  IterSpaces.resize(NestedLoopCount);
  Stmt *CurStmt = AStmt->IgnoreContainers(/* IgnoreCaptured */ true);
  for (unsigned Cnt = 0; Cnt < NestedLoopCount; ++Cnt) {
    if (CheckOpenACCIterationSpace(DKind, CurStmt, SemaRef, DSA, Cnt,
                                  NestedLoopCount, CollapseLoopCountExpr,
                                  OrderedLoopCountExpr, VarsWithImplicitDSA,
                                  IterSpaces[Cnt], Captures))
      return 0;
    // Move on to the next nested for loop, or to the loop body.
    // OpenACC [2.8.1, simd construct, Restrictions]
    // All loops associated with the construct must be perfectly nested; that
    // is, there must be no intervening code nor any OpenACC directive between
    // any two loops.
    CurStmt = cast<ForStmt>(CurStmt)->getBody()->IgnoreContainers();
  }

  Built.clear(/* size */ NestedLoopCount);

  if (SemaRef.CurContext->isDependentContext())
    return NestedLoopCount;

  // An example of what is generated for the following code:
  //
  //   #pragma acc simd collapse(2) ordered(2)
  //   for (i = 0; i < NI; ++i)
  //     for (k = 0; k < NK; ++k)
  //       for (j = J0; j < NJ; j+=2) {
  //         <loop body>
  //       }
  //
  // We generate the code below.
  // Note: the loop body may be outlined in CodeGen.
  // Note: some counters may be C++ classes, operator- is used to find number of
  // iterations and operator+= to calculate counter value.
  // Note: decltype(NumIterations) must be integer type (in 'acc for', only i32
  // or i64 is currently supported).
  //
  //   #define NumIterations (NI * ((NJ - J0 - 1 + 2) / 2))
  //   for (int[32|64]_t IV = 0; IV < NumIterations; ++IV ) {
  //     .local.i = IV / ((NJ - J0 - 1 + 2) / 2);
  //     .local.j = J0 + (IV % ((NJ - J0 - 1 + 2) / 2)) * 2;
  //     // similar updates for vars in clauses (e.g. 'linear')
  //     <loop body (using local i and j)>
  //   }
  //   i = NI; // assign final values of counters
  //   j = NJ;
  //

  // Last iteration number is (I1 * I2 * ... In) - 1, where I1, I2 ... In are
  // the iteration counts of the collapsed for loops.
  // Precondition tests if there is at least one iteration (all conditions are
  // true).
  auto PreCond = ExprResult(IterSpaces[0].PreCond);
  auto N0 = IterSpaces[0].NumIterations;
  ExprResult LastIteration32 = WidenIterationCount(
      32 /* Bits */, SemaRef
                         .PerformImplicitConversion(
                             N0->IgnoreImpCasts(), N0->getType(),
                             Sema::AA_Converting, /*AllowExplicit=*/true)
                         .get(),
      SemaRef);
  ExprResult LastIteration64 = WidenIterationCount(
      64 /* Bits */, SemaRef
                         .PerformImplicitConversion(
                             N0->IgnoreImpCasts(), N0->getType(),
                             Sema::AA_Converting, /*AllowExplicit=*/true)
                         .get(),
      SemaRef);

  if (!LastIteration32.isUsable() || !LastIteration64.isUsable())
    return NestedLoopCount;

  auto &C = SemaRef.Context;
  bool AllCountsNeedLessThan32Bits = C.getTypeSize(N0->getType()) < 32;

  Scope *CurScope = DSA.getCurScope();
  for (unsigned Cnt = 1; Cnt < NestedLoopCount; ++Cnt) {
    if (PreCond.isUsable()) {
      PreCond =
          SemaRef.BuildBinOp(CurScope, PreCond.get()->getExprLoc(), BO_LAnd,
                             PreCond.get(), IterSpaces[Cnt].PreCond);
    }
    auto N = IterSpaces[Cnt].NumIterations;
    SourceLocation Loc = N->getExprLoc();
    AllCountsNeedLessThan32Bits &= C.getTypeSize(N->getType()) < 32;
    if (LastIteration32.isUsable())
      LastIteration32 = SemaRef.BuildBinOp(
          CurScope, Loc, BO_Mul, LastIteration32.get(),
          SemaRef
              .PerformImplicitConversion(N->IgnoreImpCasts(), N->getType(),
                                         Sema::AA_Converting,
                                         /*AllowExplicit=*/true)
              .get());
    if (LastIteration64.isUsable())
      LastIteration64 = SemaRef.BuildBinOp(
          CurScope, Loc, BO_Mul, LastIteration64.get(),
          SemaRef
              .PerformImplicitConversion(N->IgnoreImpCasts(), N->getType(),
                                         Sema::AA_Converting,
                                         /*AllowExplicit=*/true)
              .get());
  }

  // Choose either the 32-bit or 64-bit version.
  ExprResult LastIteration = LastIteration64;
  if (LastIteration32.isUsable() &&
      C.getTypeSize(LastIteration32.get()->getType()) == 32 &&
      (AllCountsNeedLessThan32Bits || NestedLoopCount == 1 ||
       FitsInto(
           32 /* Bits */,
           LastIteration32.get()->getType()->hasSignedIntegerRepresentation(),
           LastIteration64.get(), SemaRef)))
    LastIteration = LastIteration32;
  QualType VType = LastIteration.get()->getType();
  QualType RealVType = VType;
  QualType StrideVType = VType;
  if (isOpenACCTaskLoopDirective(DKind)) {
    VType =
        SemaRef.Context.getIntTypeForBitwidth(/*DestWidth=*/64, /*Signed=*/0);
    StrideVType =
        SemaRef.Context.getIntTypeForBitwidth(/*DestWidth=*/64, /*Signed=*/1);
  }

  if (!LastIteration.isUsable())
    return 0;

  // Save the number of iterations.
  ExprResult NumIterations = LastIteration;
  {
    LastIteration = SemaRef.BuildBinOp(
        CurScope, LastIteration.get()->getExprLoc(), BO_Sub,
        LastIteration.get(),
        SemaRef.ActOnIntegerConstant(SourceLocation(), 1).get());
    if (!LastIteration.isUsable())
      return 0;
  }

  // Calculate the last iteration number beforehand instead of doing this on
  // each iteration. Do not do this if the number of iterations may be kfold-ed.
  llvm::APSInt Result;
  bool IsConstant =
      LastIteration.get()->isIntegerConstantExpr(Result, SemaRef.Context);
  ExprResult CalcLastIteration;
  if (!IsConstant) {
    ExprResult SaveRef =
        tryBuildCapture(SemaRef, LastIteration.get(), Captures);
    LastIteration = SaveRef;

    // Prepare SaveRef + 1.
    NumIterations = SemaRef.BuildBinOp(
        CurScope, SaveRef.get()->getExprLoc(), BO_Add, SaveRef.get(),
        SemaRef.ActOnIntegerConstant(SourceLocation(), 1).get());
    if (!NumIterations.isUsable())
      return 0;
  }

  SourceLocation InitLoc = IterSpaces[0].InitSrcRange.getBegin();

  // Build variables passed into runtime, necessary for worksharing directives.
  ExprResult LB, UB, IL, ST, EUB, CombLB, CombUB, PrevLB, PrevUB, CombEUB;
  if (isOpenACCWorksharingDirective(DKind) || isOpenACCTaskLoopDirective(DKind) ||
      isOpenACCDistributeDirective(DKind)) {
    // Lower bound variable, initialized with zero.
    VarDecl *LBDecl = buildVarDecl(SemaRef, InitLoc, VType, ".acc.lb");
    LB = buildDeclRefExpr(SemaRef, LBDecl, VType, InitLoc);
    SemaRef.AddInitializerToDecl(LBDecl,
                                 SemaRef.ActOnIntegerConstant(InitLoc, 0).get(),
                                 /*DirectInit*/ false);

    // Upper bound variable, initialized with last iteration number.
    VarDecl *UBDecl = buildVarDecl(SemaRef, InitLoc, VType, ".acc.ub");
    UB = buildDeclRefExpr(SemaRef, UBDecl, VType, InitLoc);
    SemaRef.AddInitializerToDecl(UBDecl, LastIteration.get(),
                                 /*DirectInit*/ false);

    // A 32-bit variable-flag where runtime returns 1 for the last iteration.
    // This will be used to implement clause 'lastprivate'.
    QualType Int32Ty = SemaRef.Context.getIntTypeForBitwidth(32, true);
    VarDecl *ILDecl = buildVarDecl(SemaRef, InitLoc, Int32Ty, ".acc.is_last");
    IL = buildDeclRefExpr(SemaRef, ILDecl, Int32Ty, InitLoc);
    SemaRef.AddInitializerToDecl(ILDecl,
                                 SemaRef.ActOnIntegerConstant(InitLoc, 0).get(),
                                 /*DirectInit*/ false);

    // Stride variable returned by runtime (we initialize it to 1 by default).
    VarDecl *STDecl =
        buildVarDecl(SemaRef, InitLoc, StrideVType, ".acc.stride");
    ST = buildDeclRefExpr(SemaRef, STDecl, StrideVType, InitLoc);
    SemaRef.AddInitializerToDecl(STDecl,
                                 SemaRef.ActOnIntegerConstant(InitLoc, 1).get(),
                                 /*DirectInit*/ false);

    // Build expression: UB = min(UB, LastIteration)
    // It is necessary for CodeGen of directives with static scheduling.
    ExprResult IsUBGreater = SemaRef.BuildBinOp(CurScope, InitLoc, BO_GT,
                                                UB.get(), LastIteration.get());
    ExprResult CondOp = SemaRef.ActOnConditionalOp(
        InitLoc, InitLoc, IsUBGreater.get(), LastIteration.get(), UB.get());
    EUB = SemaRef.BuildBinOp(CurScope, InitLoc, BO_Assign, UB.get(),
                             CondOp.get());
    EUB = SemaRef.ActOnFinishFullExpr(EUB.get());

    // If we have a combined directive that combines 'distribute', 'for' or
    // 'simd' we need to be able to access the bounds of the schedule of the
    // enclosing region. E.g. in 'distribute parallel for' the bounds obtained
    // by scheduling 'distribute' have to be passed to the schedule of 'for'.
    if (isOpenACCLoopBoundSharingDirective(DKind)) {

      // Lower bound variable, initialized with zero.
      VarDecl *CombLBDecl =
          buildVarDecl(SemaRef, InitLoc, VType, ".acc.comb.lb");
      CombLB = buildDeclRefExpr(SemaRef, CombLBDecl, VType, InitLoc);
      SemaRef.AddInitializerToDecl(
          CombLBDecl, SemaRef.ActOnIntegerConstant(InitLoc, 0).get(),
          /*DirectInit*/ false);

      // Upper bound variable, initialized with last iteration number.
      VarDecl *CombUBDecl =
          buildVarDecl(SemaRef, InitLoc, VType, ".acc.comb.ub");
      CombUB = buildDeclRefExpr(SemaRef, CombUBDecl, VType, InitLoc);
      SemaRef.AddInitializerToDecl(CombUBDecl, LastIteration.get(),
                                   /*DirectInit*/ false);

      ExprResult CombIsUBGreater = SemaRef.BuildBinOp(
          CurScope, InitLoc, BO_GT, CombUB.get(), LastIteration.get());
      ExprResult CombCondOp =
          SemaRef.ActOnConditionalOp(InitLoc, InitLoc, CombIsUBGreater.get(),
                                     LastIteration.get(), CombUB.get());
      CombEUB = SemaRef.BuildBinOp(CurScope, InitLoc, BO_Assign, CombUB.get(),
                                   CombCondOp.get());
      CombEUB = SemaRef.ActOnFinishFullExpr(CombEUB.get());

      auto *CD = cast<CapturedStmt>(AStmt)->getCapturedDecl();
      // We expect to have at least 2 more parameters than the 'parallel'
      // directive does - the lower and upper bounds of the previous schedule.
      assert(CD->getNumParams() >= 4 &&
             "Unexpected number of parameters in loop combined directive");

      // Set the proper type for the bounds given what we learned from the
      // enclosed loops.
      auto *PrevLBDecl = CD->getParam(/*PrevLB=*/2);
      auto *PrevUBDecl = CD->getParam(/*PrevUB=*/3);

      // Previous lower and upper bounds are obtained from the region
      // parameters.
      PrevLB =
          buildDeclRefExpr(SemaRef, PrevLBDecl, PrevLBDecl->getType(), InitLoc);
      PrevUB =
          buildDeclRefExpr(SemaRef, PrevUBDecl, PrevUBDecl->getType(), InitLoc);
    }
  }

  // Build the iteration variable and its initialization before loop.
  ExprResult IV;
  ExprResult Init, CombInit;
  {
    VarDecl *IVDecl = buildVarDecl(SemaRef, InitLoc, RealVType, ".acc.iv");
    IV = buildDeclRefExpr(SemaRef, IVDecl, RealVType, InitLoc);
    Expr *RHS =
        (isOpenACCWorksharingDirective(DKind) ||
         isOpenACCTaskLoopDirective(DKind) || isOpenACCDistributeDirective(DKind))
            ? LB.get()
            : SemaRef.ActOnIntegerConstant(SourceLocation(), 0).get();
    Init = SemaRef.BuildBinOp(CurScope, InitLoc, BO_Assign, IV.get(), RHS);
    Init = SemaRef.ActOnFinishFullExpr(Init.get());

    if (isOpenACCLoopBoundSharingDirective(DKind)) {
      Expr *CombRHS =
          (isOpenACCWorksharingDirective(DKind) ||
           isOpenACCTaskLoopDirective(DKind) ||
           isOpenACCDistributeDirective(DKind))
              ? CombLB.get()
              : SemaRef.ActOnIntegerConstant(SourceLocation(), 0).get();
      CombInit =
          SemaRef.BuildBinOp(CurScope, InitLoc, BO_Assign, IV.get(), CombRHS);
      CombInit = SemaRef.ActOnFinishFullExpr(CombInit.get());
    }
  }

  // Loop condition (IV < NumIterations) or (IV <= UB) for worksharing loops.
  SourceLocation CondLoc = AStmt->getLocStart();
  ExprResult Cond =
      (isOpenACCWorksharingDirective(DKind) ||
       isOpenACCTaskLoopDirective(DKind) || isOpenACCDistributeDirective(DKind))
          ? SemaRef.BuildBinOp(CurScope, CondLoc, BO_LE, IV.get(), UB.get())
          : SemaRef.BuildBinOp(CurScope, CondLoc, BO_LT, IV.get(),
                               NumIterations.get());
  ExprResult CombCond;
  if (isOpenACCLoopBoundSharingDirective(DKind)) {
    CombCond =
        SemaRef.BuildBinOp(CurScope, CondLoc, BO_LE, IV.get(), CombUB.get());
  }
  // Loop increment (IV = IV + 1)
  SourceLocation IncLoc = AStmt->getLocStart();
  ExprResult Inc =
      SemaRef.BuildBinOp(CurScope, IncLoc, BO_Add, IV.get(),
                         SemaRef.ActOnIntegerConstant(IncLoc, 1).get());
  if (!Inc.isUsable())
    return 0;
  Inc = SemaRef.BuildBinOp(CurScope, IncLoc, BO_Assign, IV.get(), Inc.get());
  Inc = SemaRef.ActOnFinishFullExpr(Inc.get());
  if (!Inc.isUsable())
    return 0;

  // Increments for worksharing loops (LB = LB + ST; UB = UB + ST).
  // Used for directives with static scheduling.
  // In combined construct, add combined version that use CombLB and CombUB
  // base variables for the update
  ExprResult NextLB, NextUB, CombNextLB, CombNextUB;
  if (isOpenACCWorksharingDirective(DKind) || isOpenACCTaskLoopDirective(DKind) ||
      isOpenACCDistributeDirective(DKind)) {
    // LB + ST
    NextLB = SemaRef.BuildBinOp(CurScope, IncLoc, BO_Add, LB.get(), ST.get());
    if (!NextLB.isUsable())
      return 0;
    // LB = LB + ST
    NextLB =
        SemaRef.BuildBinOp(CurScope, IncLoc, BO_Assign, LB.get(), NextLB.get());
    NextLB = SemaRef.ActOnFinishFullExpr(NextLB.get());
    if (!NextLB.isUsable())
      return 0;
    // UB + ST
    NextUB = SemaRef.BuildBinOp(CurScope, IncLoc, BO_Add, UB.get(), ST.get());
    if (!NextUB.isUsable())
      return 0;
    // UB = UB + ST
    NextUB =
        SemaRef.BuildBinOp(CurScope, IncLoc, BO_Assign, UB.get(), NextUB.get());
    NextUB = SemaRef.ActOnFinishFullExpr(NextUB.get());
    if (!NextUB.isUsable())
      return 0;
    if (isOpenACCLoopBoundSharingDirective(DKind)) {
      CombNextLB =
          SemaRef.BuildBinOp(CurScope, IncLoc, BO_Add, CombLB.get(), ST.get());
      if (!NextLB.isUsable())
        return 0;
      // LB = LB + ST
      CombNextLB = SemaRef.BuildBinOp(CurScope, IncLoc, BO_Assign, CombLB.get(),
                                      CombNextLB.get());
      CombNextLB = SemaRef.ActOnFinishFullExpr(CombNextLB.get());
      if (!CombNextLB.isUsable())
        return 0;
      // UB + ST
      CombNextUB =
          SemaRef.BuildBinOp(CurScope, IncLoc, BO_Add, CombUB.get(), ST.get());
      if (!CombNextUB.isUsable())
        return 0;
      // UB = UB + ST
      CombNextUB = SemaRef.BuildBinOp(CurScope, IncLoc, BO_Assign, CombUB.get(),
                                      CombNextUB.get());
      CombNextUB = SemaRef.ActOnFinishFullExpr(CombNextUB.get());
      if (!CombNextUB.isUsable())
        return 0;
    }
  }

  // Create increment expression for distribute loop when combined in a same
  // directive with for as IV = IV + ST; ensure upper bound expression based
  // on PrevUB instead of NumIterations - used to implement 'for' when found
  // in combination with 'distribute', like in 'distribute parallel for'
  SourceLocation DistIncLoc = AStmt->getLocStart();
  ExprResult DistCond, DistInc, PrevEUB;
  if (isOpenACCLoopBoundSharingDirective(DKind)) {
    DistCond = SemaRef.BuildBinOp(CurScope, CondLoc, BO_LE, IV.get(), UB.get());
    assert(DistCond.isUsable() && "distribute cond expr was not built");

    DistInc =
        SemaRef.BuildBinOp(CurScope, DistIncLoc, BO_Add, IV.get(), ST.get());
    assert(DistInc.isUsable() && "distribute inc expr was not built");
    DistInc = SemaRef.BuildBinOp(CurScope, DistIncLoc, BO_Assign, IV.get(),
                                 DistInc.get());
    DistInc = SemaRef.ActOnFinishFullExpr(DistInc.get());
    assert(DistInc.isUsable() && "distribute inc expr was not built");

    // Build expression: UB = min(UB, prevUB) for #for in composite or combined
    // construct
    SourceLocation DistEUBLoc = AStmt->getLocStart();
    ExprResult IsUBGreater =
        SemaRef.BuildBinOp(CurScope, DistEUBLoc, BO_GT, UB.get(), PrevUB.get());
    ExprResult CondOp = SemaRef.ActOnConditionalOp(
        DistEUBLoc, DistEUBLoc, IsUBGreater.get(), PrevUB.get(), UB.get());
    PrevEUB = SemaRef.BuildBinOp(CurScope, DistIncLoc, BO_Assign, UB.get(),
                                 CondOp.get());
    PrevEUB = SemaRef.ActOnFinishFullExpr(PrevEUB.get());
  }

  // Build updates and final values of the loop counters.
  bool HasErrors = false;
  Built.Counters.resize(NestedLoopCount);
  Built.Inits.resize(NestedLoopCount);
  Built.Updates.resize(NestedLoopCount);
  Built.Finals.resize(NestedLoopCount);
  SmallVector<Expr *, 4> LoopMultipliers;
  {
    ExprResult Div;
    // Go from inner nested loop to outer.
    for (int Cnt = NestedLoopCount - 1; Cnt >= 0; --Cnt) {
      LoopIterationSpace &IS = IterSpaces[Cnt];
      SourceLocation UpdLoc = IS.IncSrcRange.getBegin();
      // Build: Iter = (IV / Div) % IS.NumIters
      // where Div is product of previous iterations' IS.NumIters.
      ExprResult Iter;
      if (Div.isUsable()) {
        Iter =
            SemaRef.BuildBinOp(CurScope, UpdLoc, BO_Div, IV.get(), Div.get());
      } else {
        Iter = IV;
        assert((Cnt == (int)NestedLoopCount - 1) &&
               "unusable div expected on first iteration only");
      }

      if (Cnt != 0 && Iter.isUsable())
        Iter = SemaRef.BuildBinOp(CurScope, UpdLoc, BO_Rem, Iter.get(),
                                  IS.NumIterations);
      if (!Iter.isUsable()) {
        HasErrors = true;
        break;
      }

      // Build update: IS.CounterVar(Private) = IS.Start + Iter * IS.Step
      auto *VD = cast<VarDecl>(cast<DeclRefExpr>(IS.CounterVar)->getDecl());
      auto *CounterVar = buildDeclRefExpr(SemaRef, VD, IS.CounterVar->getType(),
                                          IS.CounterVar->getExprLoc(),
                                          /*RefersToCapture=*/true);
      ExprResult Init = BuildCounterInit(SemaRef, CurScope, UpdLoc, CounterVar,
                                         IS.CounterInit, Captures);
      if (!Init.isUsable()) {
        HasErrors = true;
        break;
      }
      ExprResult Update = BuildCounterUpdate(
          SemaRef, CurScope, UpdLoc, CounterVar, IS.CounterInit, Iter,
          IS.CounterStep, IS.Subtract, &Captures);
      if (!Update.isUsable()) {
        HasErrors = true;
        break;
      }

      // Build final: IS.CounterVar = IS.Start + IS.NumIters * IS.Step
      ExprResult Final = BuildCounterUpdate(
          SemaRef, CurScope, UpdLoc, CounterVar, IS.CounterInit,
          IS.NumIterations, IS.CounterStep, IS.Subtract, &Captures);
      if (!Final.isUsable()) {
        HasErrors = true;
        break;
      }

      // Build Div for the next iteration: Div <- Div * IS.NumIters
      if (Cnt != 0) {
        if (Div.isUnset())
          Div = IS.NumIterations;
        else
          Div = SemaRef.BuildBinOp(CurScope, UpdLoc, BO_Mul, Div.get(),
                                   IS.NumIterations);

        // Add parentheses (for debugging purposes only).
        if (Div.isUsable())
          Div = tryBuildCapture(SemaRef, Div.get(), Captures);
        if (!Div.isUsable()) {
          HasErrors = true;
          break;
        }
        LoopMultipliers.push_back(Div.get());
      }
      if (!Update.isUsable() || !Final.isUsable()) {
        HasErrors = true;
        break;
      }
      // Save results
      Built.Counters[Cnt] = IS.CounterVar;
      Built.PrivateCounters[Cnt] = IS.PrivateCounterVar;
      Built.Inits[Cnt] = Init.get();
      Built.Updates[Cnt] = Update.get();
      Built.Finals[Cnt] = Final.get();
    }
  }

  if (HasErrors)
    return 0;

  // Save results
  Built.IterationVarRef = IV.get();
  Built.LastIteration = LastIteration.get();
  Built.NumIterations = NumIterations.get();
  Built.CalcLastIteration =
      SemaRef.ActOnFinishFullExpr(CalcLastIteration.get()).get();
  Built.PreCond = PreCond.get();
  Built.PreInits = buildPreInits(C, Captures);
  Built.Cond = Cond.get();
  Built.Init = Init.get();
  Built.Inc = Inc.get();
  Built.LB = LB.get();
  Built.UB = UB.get();
  Built.IL = IL.get();
  Built.ST = ST.get();
  Built.EUB = EUB.get();
  Built.NLB = NextLB.get();
  Built.NUB = NextUB.get();
  Built.PrevLB = PrevLB.get();
  Built.PrevUB = PrevUB.get();
  Built.DistInc = DistInc.get();
  Built.PrevEUB = PrevEUB.get();
  Built.DistCombinedFields.LB = CombLB.get();
  Built.DistCombinedFields.UB = CombUB.get();
  Built.DistCombinedFields.EUB = CombEUB.get();
  Built.DistCombinedFields.Init = CombInit.get();
  Built.DistCombinedFields.Cond = CombCond.get();
  Built.DistCombinedFields.NLB = CombNextLB.get();
  Built.DistCombinedFields.NUB = CombNextUB.get();

  Expr *CounterVal = SemaRef.DefaultLvalueConversion(IV.get()).get();
  // Fill data for doacross depend clauses.
  for (auto Pair : DSA.getDoacrossDependClauses()) {
    if (Pair.first->getDependencyKind() == ACCC_DEPEND_source)
      Pair.first->setCounterValue(CounterVal);
    else {
      if (NestedLoopCount != Pair.second.size() ||
          NestedLoopCount != LoopMultipliers.size() + 1) {
        // Erroneous case - clause has some problems.
        Pair.first->setCounterValue(CounterVal);
        continue;
      }
      assert(Pair.first->getDependencyKind() == ACCC_DEPEND_sink);
      auto I = Pair.second.rbegin();
      auto IS = IterSpaces.rbegin();
      auto ILM = LoopMultipliers.rbegin();
      Expr *UpCounterVal = CounterVal;
      Expr *Multiplier = nullptr;
      for (int Cnt = NestedLoopCount - 1; Cnt >= 0; --Cnt) {
        if (I->first) {
          assert(IS->CounterStep);
          Expr *NormalizedOffset =
              SemaRef
                  .BuildBinOp(CurScope, I->first->getExprLoc(), BO_Div,
                              I->first, IS->CounterStep)
                  .get();
          if (Multiplier) {
            NormalizedOffset =
                SemaRef
                    .BuildBinOp(CurScope, I->first->getExprLoc(), BO_Mul,
                                NormalizedOffset, Multiplier)
                    .get();
          }
          assert(I->second == OO_Plus || I->second == OO_Minus);
          BinaryOperatorKind BOK = (I->second == OO_Plus) ? BO_Add : BO_Sub;
          UpCounterVal = SemaRef
                             .BuildBinOp(CurScope, I->first->getExprLoc(), BOK,
                                         UpCounterVal, NormalizedOffset)
                             .get();
        }
        Multiplier = *ILM;
        ++I;
        ++IS;
        ++ILM;
      }
      Pair.first->setCounterValue(UpCounterVal);
    }
  }

  return NestedLoopCount;
}

static Expr *getCollapseNumberExpr(ArrayRef<ACCClause *> Clauses) {
  auto CollapseClauses =
      ACCExecutableDirective::getClausesOfKind<ACCCollapseClause>(Clauses);
  if (CollapseClauses.begin() != CollapseClauses.end())
    return (*CollapseClauses.begin())->getNumForLoops();
  return nullptr;
}

static Expr *getOrderedNumberExpr(ArrayRef<ACCClause *> Clauses) {
  auto OrderedClauses =
      ACCExecutableDirective::getClausesOfKind<ACCOrderedClause>(Clauses);
  if (OrderedClauses.begin() != OrderedClauses.end())
    return (*OrderedClauses.begin())->getNumForLoops();
  return nullptr;
}

static bool checkSimdlenSafelenSpecified(Sema &S,
                                         const ArrayRef<ACCClause *> Clauses) {
  ACCSafelenClause *Safelen = nullptr;
  ACCSimdlenClause *Simdlen = nullptr;

  for (auto *Clause : Clauses) {
    if (Clause->getClauseKind() == ACCC_safelen)
      Safelen = cast<ACCSafelenClause>(Clause);
    else if (Clause->getClauseKind() == ACCC_simdlen)
      Simdlen = cast<ACCSimdlenClause>(Clause);
    if (Safelen && Simdlen)
      break;
  }

  if (Simdlen && Safelen) {
    llvm::APSInt SimdlenRes, SafelenRes;
    auto SimdlenLength = Simdlen->getSimdlen();
    auto SafelenLength = Safelen->getSafelen();
    if (SimdlenLength->isValueDependent() || SimdlenLength->isTypeDependent() ||
        SimdlenLength->isInstantiationDependent() ||
        SimdlenLength->containsUnexpandedParameterPack())
      return false;
    if (SafelenLength->isValueDependent() || SafelenLength->isTypeDependent() ||
        SafelenLength->isInstantiationDependent() ||
        SafelenLength->containsUnexpandedParameterPack())
      return false;
    SimdlenLength->EvaluateAsInt(SimdlenRes, S.Context);
    SafelenLength->EvaluateAsInt(SafelenRes, S.Context);
    // OpenACC 4.5 [2.8.1, simd Construct, Restrictions]
    // If both simdlen and safelen clauses are specified, the value of the
    // simdlen parameter must be less than or equal to the value of the safelen
    // parameter.
    if (SimdlenRes > SafelenRes) {
      S.Diag(SimdlenLength->getExprLoc(),
             diag::err_acc_wrong_simdlen_safelen_values)
          << SimdlenLength->getSourceRange() << SafelenLength->getSourceRange();
      return true;
    }
  }
  return false;
}

StmtResult Sema::ActOnOpenACCSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_simd, getCollapseNumberExpr(Clauses), getOrderedNumberExpr(Clauses),
      AStmt, *this, *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCSimdDirective::Create(Context, StartLoc, EndLoc, NestedLoopCount,
                                  Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCForDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_for, getCollapseNumberExpr(Clauses), getOrderedNumberExpr(Clauses),
      AStmt, *this, *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  getCurFunction()->setHasBranchProtectedScope();
  return ACCForDirective::Create(Context, StartLoc, EndLoc, NestedLoopCount,
                                 Clauses, AStmt, B, DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_for_simd, getCollapseNumberExpr(Clauses),
                      getOrderedNumberExpr(Clauses), AStmt, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCForSimdDirective::Create(Context, StartLoc, EndLoc, NestedLoopCount,
                                     Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCSectionsDirective(ArrayRef<ACCClause *> Clauses,
                                              Stmt *AStmt,
                                              SourceLocation StartLoc,
                                              SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  auto BaseStmt = AStmt;
  while (auto *CS = dyn_cast_or_null<CapturedStmt>(BaseStmt))
    BaseStmt = CS->getCapturedStmt();
  if (auto *C = dyn_cast_or_null<CompoundStmt>(BaseStmt)) {
    auto S = C->children();
    if (S.begin() == S.end())
      return StmtError();
    // All associated statements must be '#pragma acc section' except for
    // the first one.
    for (Stmt *SectionStmt : llvm::make_range(std::next(S.begin()), S.end())) {
      if (!SectionStmt || !isa<ACCSectionDirective>(SectionStmt)) {
        if (SectionStmt)
          Diag(SectionStmt->getLocStart(),
               diag::err_acc_sections_substmt_not_section);
        return StmtError();
      }
      cast<ACCSectionDirective>(SectionStmt)
          ->setHasCancel(DSAStack->isCancelRegion());
    }
  } else {
    Diag(AStmt->getLocStart(), diag::err_acc_sections_not_compound_stmt);
    return StmtError();
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCSectionsDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt,
                                      DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCSectionDirective(Stmt *AStmt,
                                             SourceLocation StartLoc,
                                             SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  getCurFunction()->setHasBranchProtectedScope();
  DSAStack->setParentCancelRegion(DSAStack->isCancelRegion());

  return ACCSectionDirective::Create(Context, StartLoc, EndLoc, AStmt,
                                     DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCSingleDirective(ArrayRef<ACCClause *> Clauses,
                                            Stmt *AStmt,
                                            SourceLocation StartLoc,
                                            SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  getCurFunction()->setHasBranchProtectedScope();

  // OpenACC [2.7.3, single Construct, Restrictions]
  // The copyprivate clause must not be used with the nowait clause.
  ACCClause *Nowait = nullptr;
  ACCClause *Copyprivate = nullptr;
  for (auto *Clause : Clauses) {
    if (Clause->getClauseKind() == ACCC_nowait)
      Nowait = Clause;
    else if (Clause->getClauseKind() == ACCC_copyprivate)
      Copyprivate = Clause;
    if (Copyprivate && Nowait) {
      Diag(Copyprivate->getLocStart(),
           diag::err_acc_single_copyprivate_with_nowait);
      Diag(Nowait->getLocStart(), diag::note_acc_nowait_clause_here);
      return StmtError();
    }
  }

  return ACCSingleDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt);
}

StmtResult Sema::ActOnOpenACCMasterDirective(Stmt *AStmt,
                                            SourceLocation StartLoc,
                                            SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  getCurFunction()->setHasBranchProtectedScope();

  return ACCMasterDirective::Create(Context, StartLoc, EndLoc, AStmt);
}

StmtResult Sema::ActOnOpenACCCriticalDirective(
    const DeclarationNameInfo &DirName, ArrayRef<ACCClause *> Clauses,
    Stmt *AStmt, SourceLocation StartLoc, SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  bool ErrorFound = false;
  llvm::APSInt Hint;
  SourceLocation HintLoc;
  bool DependentHint = false;
  for (auto *C : Clauses) {
    if (C->getClauseKind() == ACCC_hint) {
      if (!DirName.getName()) {
        Diag(C->getLocStart(), diag::err_acc_hint_clause_no_name);
        ErrorFound = true;
      }
      Expr *E = cast<ACCHintClause>(C)->getHint();
      if (E->isTypeDependent() || E->isValueDependent() ||
          E->isInstantiationDependent())
        DependentHint = true;
      else {
        Hint = E->EvaluateKnownConstInt(Context);
        HintLoc = C->getLocStart();
      }
    }
  }
  if (ErrorFound)
    return StmtError();
  auto Pair = DSAStack->getCriticalWithHint(DirName);
  if (Pair.first && DirName.getName() && !DependentHint) {
    if (llvm::APSInt::compareValues(Hint, Pair.second) != 0) {
      Diag(StartLoc, diag::err_acc_critical_with_hint);
      if (HintLoc.isValid()) {
        Diag(HintLoc, diag::note_acc_critical_hint_here)
            << 0 << Hint.toString(/*Radix=*/10, /*Signed=*/false);
      } else
        Diag(StartLoc, diag::note_acc_critical_no_hint) << 0;
      if (auto *C = Pair.first->getSingleClause<ACCHintClause>()) {
        Diag(C->getLocStart(), diag::note_acc_critical_hint_here)
            << 1
            << C->getHint()->EvaluateKnownConstInt(Context).toString(
                   /*Radix=*/10, /*Signed=*/false);
      } else
        Diag(Pair.first->getLocStart(), diag::note_acc_critical_no_hint) << 1;
    }
  }

  getCurFunction()->setHasBranchProtectedScope();

  auto *Dir = ACCCriticalDirective::Create(Context, DirName, StartLoc, EndLoc,
                                           Clauses, AStmt);
  if (!Pair.first && DirName.getName() && !DependentHint)
    DSAStack->addCriticalWithHint(Dir, Hint);
  return Dir;
}

StmtResult Sema::ActOnOpenACCParallelLoopDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  llvm::outs() << " F(CALL) : Sema::ActOnOpenACCParallelForDirective()\n";

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_parellel_loop, getCollapseNumberExpr(Clauses),
                      getOrderedNumberExpr(Clauses), AStmt, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc parallel for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  getCurFunction()->setHasBranchProtectedScope();
  return ACCParallelLoopDirective::Create(Context, StartLoc, EndLoc,
                                         NestedLoopCount, Clauses, AStmt, B,
                                         DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCParallelForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_parallel_for_simd, getCollapseNumberExpr(Clauses),
                      getOrderedNumberExpr(Clauses), AStmt, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCParallelForSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult
Sema::ActOnOpenACCParallelSectionsDirective(ArrayRef<ACCClause *> Clauses,
                                           Stmt *AStmt, SourceLocation StartLoc,
                                           SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  auto BaseStmt = AStmt;
  while (auto *CS = dyn_cast_or_null<CapturedStmt>(BaseStmt))
    BaseStmt = CS->getCapturedStmt();
  if (auto *C = dyn_cast_or_null<CompoundStmt>(BaseStmt)) {
    auto S = C->children();
    if (S.begin() == S.end())
      return StmtError();
    // All associated statements must be '#pragma acc section' except for
    // the first one.
    for (Stmt *SectionStmt : llvm::make_range(std::next(S.begin()), S.end())) {
      if (!SectionStmt || !isa<ACCSectionDirective>(SectionStmt)) {
        if (SectionStmt)
          Diag(SectionStmt->getLocStart(),
               diag::err_acc_parallel_sections_substmt_not_section);
        return StmtError();
      }
      cast<ACCSectionDirective>(SectionStmt)
          ->setHasCancel(DSAStack->isCancelRegion());
    }
  } else {
    Diag(AStmt->getLocStart(),
         diag::err_acc_parallel_sections_not_compound_stmt);
    return StmtError();
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCParallelSectionsDirective::Create(
      Context, StartLoc, EndLoc, Clauses, AStmt, DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCTaskDirective(ArrayRef<ACCClause *> Clauses,
                                          Stmt *AStmt, SourceLocation StartLoc,
                                          SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  auto *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  getCurFunction()->setHasBranchProtectedScope();

  return ACCTaskDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt,
                                  DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCTaskyieldDirective(SourceLocation StartLoc,
                                               SourceLocation EndLoc) {
  return ACCTaskyieldDirective::Create(Context, StartLoc, EndLoc);
}

StmtResult Sema::ActOnOpenACCBarrierDirective(SourceLocation StartLoc,
                                             SourceLocation EndLoc) {
  return ACCBarrierDirective::Create(Context, StartLoc, EndLoc);
}

StmtResult Sema::ActOnOpenACCTaskwaitDirective(SourceLocation StartLoc,
                                              SourceLocation EndLoc) {
  return ACCTaskwaitDirective::Create(Context, StartLoc, EndLoc);
}

StmtResult Sema::ActOnOpenACCTaskgroupDirective(ArrayRef<ACCClause *> Clauses,
                                               Stmt *AStmt,
                                               SourceLocation StartLoc,
                                               SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  getCurFunction()->setHasBranchProtectedScope();

  return ACCTaskgroupDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                       AStmt,
                                       DSAStack->getTaskgroupReductionRef());
}

StmtResult Sema::ActOnOpenACCFlushDirective(ArrayRef<ACCClause *> Clauses,
                                           SourceLocation StartLoc,
                                           SourceLocation EndLoc) {
  assert(Clauses.size() <= 1 && "Extra clauses in flush directive");
  return ACCFlushDirective::Create(Context, StartLoc, EndLoc, Clauses);
}

StmtResult Sema::ActOnOpenACCOrderedDirective(ArrayRef<ACCClause *> Clauses,
                                             Stmt *AStmt,
                                             SourceLocation StartLoc,
                                             SourceLocation EndLoc) {
  ACCClause *DependFound = nullptr;
  ACCClause *DependSourceClause = nullptr;
  ACCClause *DependSinkClause = nullptr;
  bool ErrorFound = false;
  ACCThreadsClause *TC = nullptr;
  ACCSIMDClause *SC = nullptr;
  for (auto *C : Clauses) {
    if (auto *DC = dyn_cast<ACCDependClause>(C)) {
      DependFound = C;
      if (DC->getDependencyKind() == ACCC_DEPEND_source) {
        if (DependSourceClause) {
          Diag(C->getLocStart(), diag::err_acc_more_one_clause)
              << getOpenACCDirectiveName(ACCD_ordered)
              << getOpenACCClauseName(ACCC_depend) << 2;
          ErrorFound = true;
        } else
          DependSourceClause = C;
        if (DependSinkClause) {
          Diag(C->getLocStart(), diag::err_acc_depend_sink_source_not_allowed)
              << 0;
          ErrorFound = true;
        }
      } else if (DC->getDependencyKind() == ACCC_DEPEND_sink) {
        if (DependSourceClause) {
          Diag(C->getLocStart(), diag::err_acc_depend_sink_source_not_allowed)
              << 1;
          ErrorFound = true;
        }
        DependSinkClause = C;
      }
    } else if (C->getClauseKind() == ACCC_threads)
      TC = cast<ACCThreadsClause>(C);
    else if (C->getClauseKind() == ACCC_simd)
      SC = cast<ACCSIMDClause>(C);
  }
  if (!ErrorFound && !SC &&
      isOpenACCSimdDirective(DSAStack->getParentDirective())) {
    // OpenACC [2.8.1,simd Construct, Restrictions]
    // An ordered construct with the simd clause is the only OpenACC construct
    // that can appear in the simd region.
    Diag(StartLoc, diag::err_acc_prohibited_region_simd);
    ErrorFound = true;
  } else if (DependFound && (TC || SC)) {
    Diag(DependFound->getLocStart(), diag::err_acc_depend_clause_thread_simd)
        << getOpenACCClauseName(TC ? TC->getClauseKind() : SC->getClauseKind());
    ErrorFound = true;
  } else if (DependFound && !DSAStack->getParentOrderedRegionParam()) {
    Diag(DependFound->getLocStart(),
         diag::err_acc_ordered_directive_without_param);
    ErrorFound = true;
  } else if (TC || Clauses.empty()) {
    if (auto *Param = DSAStack->getParentOrderedRegionParam()) {
      SourceLocation ErrLoc = TC ? TC->getLocStart() : StartLoc;
      Diag(ErrLoc, diag::err_acc_ordered_directive_with_param)
          << (TC != nullptr);
      Diag(Param->getLocStart(), diag::note_acc_ordered_param);
      ErrorFound = true;
    }
  }
  if ((!AStmt && !DependFound) || ErrorFound)
    return StmtError();

  if (AStmt) {
    assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

    getCurFunction()->setHasBranchProtectedScope();
  }

  return ACCOrderedDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt);
}

namespace {
/// \brief Helper class for checking expression in 'acc atomic [update]'
/// construct.
class OpenACCAtomicUpdateChecker {
  /// \brief Error results for atomic update expressions.
  enum ExprAnalysisErrorCode {
    /// \brief A statement is not an expression statement.
    NotAnExpression,
    /// \brief Expression is not builtin binary or unary operation.
    NotABinaryOrUnaryExpression,
    /// \brief Unary operation is not post-/pre- increment/decrement operation.
    NotAnUnaryIncDecExpression,
    /// \brief An expression is not of scalar type.
    NotAScalarType,
    /// \brief A binary operation is not an assignment operation.
    NotAnAssignmentOp,
    /// \brief RHS part of the binary operation is not a binary expression.
    NotABinaryExpression,
    /// \brief RHS part is not additive/multiplicative/shift/biwise binary
    /// expression.
    NotABinaryOperator,
    /// \brief RHS binary operation does not have reference to the updated LHS
    /// part.
    NotAnUpdateExpression,
    /// \brief No errors is found.
    NoError
  };
  /// \brief Reference to Sema.
  Sema &SemaRef;
  /// \brief A location for note diagnostics (when error is found).
  SourceLocation NoteLoc;
  /// \brief 'x' lvalue part of the source atomic expression.
  Expr *X;
  /// \brief 'expr' rvalue part of the source atomic expression.
  Expr *E;
  /// \brief Helper expression of the form
  /// 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' or
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  Expr *UpdateExpr;
  /// \brief Is 'x' a LHS in a RHS part of full update expression. It is
  /// important for non-associative operations.
  bool IsXLHSInRHSPart;
  BinaryOperatorKind Op;
  SourceLocation OpLoc;
  /// \brief true if the source expression is a postfix unary operation, false
  /// if it is a prefix unary operation.
  bool IsPostfixUpdate;

public:
  OpenACCAtomicUpdateChecker(Sema &SemaRef)
      : SemaRef(SemaRef), X(nullptr), E(nullptr), UpdateExpr(nullptr),
        IsXLHSInRHSPart(false), Op(BO_PtrMemD), IsPostfixUpdate(false) {}
  /// \brief Check specified statement that it is suitable for 'atomic update'
  /// constructs and extract 'x', 'expr' and Operation from the original
  /// expression. If DiagId and NoteId == 0, then only check is performed
  /// without error notification.
  /// \param DiagId Diagnostic which should be emitted if error is found.
  /// \param NoteId Diagnostic note for the main error message.
  /// \return true if statement is not an update expression, false otherwise.
  bool checkStatement(Stmt *S, unsigned DiagId = 0, unsigned NoteId = 0);
  /// \brief Return the 'x' lvalue part of the source atomic expression.
  Expr *getX() const { return X; }
  /// \brief Return the 'expr' rvalue part of the source atomic expression.
  Expr *getExpr() const { return E; }
  /// \brief Return the update expression used in calculation of the updated
  /// value. Always has form 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' or
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  Expr *getUpdateExpr() const { return UpdateExpr; }
  /// \brief Return true if 'x' is LHS in RHS part of full update expression,
  /// false otherwise.
  bool isXLHSInRHSPart() const { return IsXLHSInRHSPart; }

  /// \brief true if the source expression is a postfix unary operation, false
  /// if it is a prefix unary operation.
  bool isPostfixUpdate() const { return IsPostfixUpdate; }

private:
  bool checkBinaryOperation(BinaryOperator *AtomicBinOp, unsigned DiagId = 0,
                            unsigned NoteId = 0);
};
} // namespace

bool OpenACCAtomicUpdateChecker::checkBinaryOperation(
    BinaryOperator *AtomicBinOp, unsigned DiagId, unsigned NoteId) {
  ExprAnalysisErrorCode ErrorFound = NoError;
  SourceLocation ErrorLoc, NoteLoc;
  SourceRange ErrorRange, NoteRange;
  // Allowed constructs are:
  //  x = x binop expr;
  //  x = expr binop x;
  if (AtomicBinOp->getOpcode() == BO_Assign) {
    X = AtomicBinOp->getLHS();
    if (auto *AtomicInnerBinOp = dyn_cast<BinaryOperator>(
            AtomicBinOp->getRHS()->IgnoreParenImpCasts())) {
      if (AtomicInnerBinOp->isMultiplicativeOp() ||
          AtomicInnerBinOp->isAdditiveOp() || AtomicInnerBinOp->isShiftOp() ||
          AtomicInnerBinOp->isBitwiseOp()) {
        Op = AtomicInnerBinOp->getOpcode();
        OpLoc = AtomicInnerBinOp->getOperatorLoc();
        auto *LHS = AtomicInnerBinOp->getLHS();
        auto *RHS = AtomicInnerBinOp->getRHS();
        llvm::FoldingSetNodeID XId, LHSId, RHSId;
        X->IgnoreParenImpCasts()->Profile(XId, SemaRef.getASTContext(),
                                          /*Canonical=*/true);
        LHS->IgnoreParenImpCasts()->Profile(LHSId, SemaRef.getASTContext(),
                                            /*Canonical=*/true);
        RHS->IgnoreParenImpCasts()->Profile(RHSId, SemaRef.getASTContext(),
                                            /*Canonical=*/true);
        if (XId == LHSId) {
          E = RHS;
          IsXLHSInRHSPart = true;
        } else if (XId == RHSId) {
          E = LHS;
          IsXLHSInRHSPart = false;
        } else {
          ErrorLoc = AtomicInnerBinOp->getExprLoc();
          ErrorRange = AtomicInnerBinOp->getSourceRange();
          NoteLoc = X->getExprLoc();
          NoteRange = X->getSourceRange();
          ErrorFound = NotAnUpdateExpression;
        }
      } else {
        ErrorLoc = AtomicInnerBinOp->getExprLoc();
        ErrorRange = AtomicInnerBinOp->getSourceRange();
        NoteLoc = AtomicInnerBinOp->getOperatorLoc();
        NoteRange = SourceRange(NoteLoc, NoteLoc);
        ErrorFound = NotABinaryOperator;
      }
    } else {
      NoteLoc = ErrorLoc = AtomicBinOp->getRHS()->getExprLoc();
      NoteRange = ErrorRange = AtomicBinOp->getRHS()->getSourceRange();
      ErrorFound = NotABinaryExpression;
    }
  } else {
    ErrorLoc = AtomicBinOp->getExprLoc();
    ErrorRange = AtomicBinOp->getSourceRange();
    NoteLoc = AtomicBinOp->getOperatorLoc();
    NoteRange = SourceRange(NoteLoc, NoteLoc);
    ErrorFound = NotAnAssignmentOp;
  }
  if (ErrorFound != NoError && DiagId != 0 && NoteId != 0) {
    SemaRef.Diag(ErrorLoc, DiagId) << ErrorRange;
    SemaRef.Diag(NoteLoc, NoteId) << ErrorFound << NoteRange;
    return true;
  } else if (SemaRef.CurContext->isDependentContext())
    E = X = UpdateExpr = nullptr;
  return ErrorFound != NoError;
}

bool OpenACCAtomicUpdateChecker::checkStatement(Stmt *S, unsigned DiagId,
                                               unsigned NoteId) {
  ExprAnalysisErrorCode ErrorFound = NoError;
  SourceLocation ErrorLoc, NoteLoc;
  SourceRange ErrorRange, NoteRange;
  // Allowed constructs are:
  //  x++;
  //  x--;
  //  ++x;
  //  --x;
  //  x binop= expr;
  //  x = x binop expr;
  //  x = expr binop x;
  if (auto *AtomicBody = dyn_cast<Expr>(S)) {
    AtomicBody = AtomicBody->IgnoreParenImpCasts();
    if (AtomicBody->getType()->isScalarType() ||
        AtomicBody->isInstantiationDependent()) {
      if (auto *AtomicCompAssignOp = dyn_cast<CompoundAssignOperator>(
              AtomicBody->IgnoreParenImpCasts())) {
        // Check for Compound Assignment Operation
        Op = BinaryOperator::getOpForCompoundAssignment(
            AtomicCompAssignOp->getOpcode());
        OpLoc = AtomicCompAssignOp->getOperatorLoc();
        E = AtomicCompAssignOp->getRHS();
        X = AtomicCompAssignOp->getLHS()->IgnoreParens();
        IsXLHSInRHSPart = true;
      } else if (auto *AtomicBinOp = dyn_cast<BinaryOperator>(
                     AtomicBody->IgnoreParenImpCasts())) {
        // Check for Binary Operation
        if (checkBinaryOperation(AtomicBinOp, DiagId, NoteId))
          return true;
      } else if (auto *AtomicUnaryOp = dyn_cast<UnaryOperator>(
                     AtomicBody->IgnoreParenImpCasts())) {
        // Check for Unary Operation
        if (AtomicUnaryOp->isIncrementDecrementOp()) {
          IsPostfixUpdate = AtomicUnaryOp->isPostfix();
          Op = AtomicUnaryOp->isIncrementOp() ? BO_Add : BO_Sub;
          OpLoc = AtomicUnaryOp->getOperatorLoc();
          X = AtomicUnaryOp->getSubExpr()->IgnoreParens();
          E = SemaRef.ActOnIntegerConstant(OpLoc, /*uint64_t Val=*/1).get();
          IsXLHSInRHSPart = true;
        } else {
          ErrorFound = NotAnUnaryIncDecExpression;
          ErrorLoc = AtomicUnaryOp->getExprLoc();
          ErrorRange = AtomicUnaryOp->getSourceRange();
          NoteLoc = AtomicUnaryOp->getOperatorLoc();
          NoteRange = SourceRange(NoteLoc, NoteLoc);
        }
      } else if (!AtomicBody->isInstantiationDependent()) {
        ErrorFound = NotABinaryOrUnaryExpression;
        NoteLoc = ErrorLoc = AtomicBody->getExprLoc();
        NoteRange = ErrorRange = AtomicBody->getSourceRange();
      }
    } else {
      ErrorFound = NotAScalarType;
      NoteLoc = ErrorLoc = AtomicBody->getLocStart();
      NoteRange = ErrorRange = SourceRange(NoteLoc, NoteLoc);
    }
  } else {
    ErrorFound = NotAnExpression;
    NoteLoc = ErrorLoc = S->getLocStart();
    NoteRange = ErrorRange = SourceRange(NoteLoc, NoteLoc);
  }
  if (ErrorFound != NoError && DiagId != 0 && NoteId != 0) {
    SemaRef.Diag(ErrorLoc, DiagId) << ErrorRange;
    SemaRef.Diag(NoteLoc, NoteId) << ErrorFound << NoteRange;
    return true;
  } else if (SemaRef.CurContext->isDependentContext())
    E = X = UpdateExpr = nullptr;
  if (ErrorFound == NoError && E && X) {
    // Build an update expression of form 'OpaqueValueExpr(x) binop
    // OpaqueValueExpr(expr)' or 'OpaqueValueExpr(expr) binop
    // OpaqueValueExpr(x)' and then cast it to the type of the 'x' expression.
    auto *OVEX = new (SemaRef.getASTContext())
        OpaqueValueExpr(X->getExprLoc(), X->getType(), VK_RValue);
    auto *OVEExpr = new (SemaRef.getASTContext())
        OpaqueValueExpr(E->getExprLoc(), E->getType(), VK_RValue);
    auto Update =
        SemaRef.CreateBuiltinBinOp(OpLoc, Op, IsXLHSInRHSPart ? OVEX : OVEExpr,
                                   IsXLHSInRHSPart ? OVEExpr : OVEX);
    if (Update.isInvalid())
      return true;
    Update = SemaRef.PerformImplicitConversion(Update.get(), X->getType(),
                                               Sema::AA_Casting);
    if (Update.isInvalid())
      return true;
    UpdateExpr = Update.get();
  }
  return ErrorFound != NoError;
}

StmtResult Sema::ActOnOpenACCAtomicDirective(ArrayRef<ACCClause *> Clauses,
                                            Stmt *AStmt,
                                            SourceLocation StartLoc,
                                            SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  auto *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  OpenACCClauseKind AtomicKind = ACCC_unknown;
  SourceLocation AtomicKindLoc;
  for (auto *C : Clauses) {
    if (C->getClauseKind() == ACCC_read || C->getClauseKind() == ACCC_write ||
        C->getClauseKind() == ACCC_update ||
        C->getClauseKind() == ACCC_capture) {
      if (AtomicKind != ACCC_unknown) {
        Diag(C->getLocStart(), diag::err_acc_atomic_several_clauses)
            << SourceRange(C->getLocStart(), C->getLocEnd());
        Diag(AtomicKindLoc, diag::note_acc_atomic_previous_clause)
            << getOpenACCClauseName(AtomicKind);
      } else {
        AtomicKind = C->getClauseKind();
        AtomicKindLoc = C->getLocStart();
      }
    }
  }

  auto Body = CS->getCapturedStmt();
  if (auto *EWC = dyn_cast<ExprWithCleanups>(Body))
    Body = EWC->getSubExpr();

  Expr *X = nullptr;
  Expr *V = nullptr;
  Expr *E = nullptr;
  Expr *UE = nullptr;
  bool IsXLHSInRHSPart = false;
  bool IsPostfixUpdate = false;
  // OpenACC [2.12.6, atomic Construct]
  // In the next expressions:
  // * x and v (as applicable) are both l-value expressions with scalar type.
  // * During the execution of an atomic region, multiple syntactic
  // occurrences of x must designate the same storage location.
  // * Neither of v and expr (as applicable) may access the storage location
  // designated by x.
  // * Neither of x and expr (as applicable) may access the storage location
  // designated by v.
  // * expr is an expression with scalar type.
  // * binop is one of +, *, -, /, &, ^, |, <<, or >>.
  // * binop, binop=, ++, and -- are not overloaded operators.
  // * The expression x binop expr must be numerically equivalent to x binop
  // (expr). This requirement is satisfied if the operators in expr have
  // precedence greater than binop, or by using parentheses around expr or
  // subexpressions of expr.
  // * The expression expr binop x must be numerically equivalent to (expr)
  // binop x. This requirement is satisfied if the operators in expr have
  // precedence equal to or greater than binop, or by using parentheses around
  // expr or subexpressions of expr.
  // * For forms that allow multiple occurrences of x, the number of times
  // that x is evaluated is unspecified.
  if (AtomicKind == ACCC_read) {
    enum {
      NotAnExpression,
      NotAnAssignmentOp,
      NotAScalarType,
      NotAnLValue,
      NoError
    } ErrorFound = NoError;
    SourceLocation ErrorLoc, NoteLoc;
    SourceRange ErrorRange, NoteRange;
    // If clause is read:
    //  v = x;
    if (auto *AtomicBody = dyn_cast<Expr>(Body)) {
      auto *AtomicBinOp =
          dyn_cast<BinaryOperator>(AtomicBody->IgnoreParenImpCasts());
      if (AtomicBinOp && AtomicBinOp->getOpcode() == BO_Assign) {
        X = AtomicBinOp->getRHS()->IgnoreParenImpCasts();
        V = AtomicBinOp->getLHS()->IgnoreParenImpCasts();
        if ((X->isInstantiationDependent() || X->getType()->isScalarType()) &&
            (V->isInstantiationDependent() || V->getType()->isScalarType())) {
          if (!X->isLValue() || !V->isLValue()) {
            auto NotLValueExpr = X->isLValue() ? V : X;
            ErrorFound = NotAnLValue;
            ErrorLoc = AtomicBinOp->getExprLoc();
            ErrorRange = AtomicBinOp->getSourceRange();
            NoteLoc = NotLValueExpr->getExprLoc();
            NoteRange = NotLValueExpr->getSourceRange();
          }
        } else if (!X->isInstantiationDependent() ||
                   !V->isInstantiationDependent()) {
          auto NotScalarExpr =
              (X->isInstantiationDependent() || X->getType()->isScalarType())
                  ? V
                  : X;
          ErrorFound = NotAScalarType;
          ErrorLoc = AtomicBinOp->getExprLoc();
          ErrorRange = AtomicBinOp->getSourceRange();
          NoteLoc = NotScalarExpr->getExprLoc();
          NoteRange = NotScalarExpr->getSourceRange();
        }
      } else if (!AtomicBody->isInstantiationDependent()) {
        ErrorFound = NotAnAssignmentOp;
        ErrorLoc = AtomicBody->getExprLoc();
        ErrorRange = AtomicBody->getSourceRange();
        NoteLoc = AtomicBinOp ? AtomicBinOp->getOperatorLoc()
                              : AtomicBody->getExprLoc();
        NoteRange = AtomicBinOp ? AtomicBinOp->getSourceRange()
                                : AtomicBody->getSourceRange();
      }
    } else {
      ErrorFound = NotAnExpression;
      NoteLoc = ErrorLoc = Body->getLocStart();
      NoteRange = ErrorRange = SourceRange(NoteLoc, NoteLoc);
    }
    if (ErrorFound != NoError) {
      Diag(ErrorLoc, diag::err_acc_atomic_read_not_expression_statement)
          << ErrorRange;
      Diag(NoteLoc, diag::note_acc_atomic_read_write) << ErrorFound
                                                      << NoteRange;
      return StmtError();
    } else if (CurContext->isDependentContext())
      V = X = nullptr;
  } else if (AtomicKind == ACCC_write) {
    enum {
      NotAnExpression,
      NotAnAssignmentOp,
      NotAScalarType,
      NotAnLValue,
      NoError
    } ErrorFound = NoError;
    SourceLocation ErrorLoc, NoteLoc;
    SourceRange ErrorRange, NoteRange;
    // If clause is write:
    //  x = expr;
    if (auto *AtomicBody = dyn_cast<Expr>(Body)) {
      auto *AtomicBinOp =
          dyn_cast<BinaryOperator>(AtomicBody->IgnoreParenImpCasts());
      if (AtomicBinOp && AtomicBinOp->getOpcode() == BO_Assign) {
        X = AtomicBinOp->getLHS();
        E = AtomicBinOp->getRHS();
        if ((X->isInstantiationDependent() || X->getType()->isScalarType()) &&
            (E->isInstantiationDependent() || E->getType()->isScalarType())) {
          if (!X->isLValue()) {
            ErrorFound = NotAnLValue;
            ErrorLoc = AtomicBinOp->getExprLoc();
            ErrorRange = AtomicBinOp->getSourceRange();
            NoteLoc = X->getExprLoc();
            NoteRange = X->getSourceRange();
          }
        } else if (!X->isInstantiationDependent() ||
                   !E->isInstantiationDependent()) {
          auto NotScalarExpr =
              (X->isInstantiationDependent() || X->getType()->isScalarType())
                  ? E
                  : X;
          ErrorFound = NotAScalarType;
          ErrorLoc = AtomicBinOp->getExprLoc();
          ErrorRange = AtomicBinOp->getSourceRange();
          NoteLoc = NotScalarExpr->getExprLoc();
          NoteRange = NotScalarExpr->getSourceRange();
        }
      } else if (!AtomicBody->isInstantiationDependent()) {
        ErrorFound = NotAnAssignmentOp;
        ErrorLoc = AtomicBody->getExprLoc();
        ErrorRange = AtomicBody->getSourceRange();
        NoteLoc = AtomicBinOp ? AtomicBinOp->getOperatorLoc()
                              : AtomicBody->getExprLoc();
        NoteRange = AtomicBinOp ? AtomicBinOp->getSourceRange()
                                : AtomicBody->getSourceRange();
      }
    } else {
      ErrorFound = NotAnExpression;
      NoteLoc = ErrorLoc = Body->getLocStart();
      NoteRange = ErrorRange = SourceRange(NoteLoc, NoteLoc);
    }
    if (ErrorFound != NoError) {
      Diag(ErrorLoc, diag::err_acc_atomic_write_not_expression_statement)
          << ErrorRange;
      Diag(NoteLoc, diag::note_acc_atomic_read_write) << ErrorFound
                                                      << NoteRange;
      return StmtError();
    } else if (CurContext->isDependentContext())
      E = X = nullptr;
  } else if (AtomicKind == ACCC_update || AtomicKind == ACCC_unknown) {
    // If clause is update:
    //  x++;
    //  x--;
    //  ++x;
    //  --x;
    //  x binop= expr;
    //  x = x binop expr;
    //  x = expr binop x;
    OpenACCAtomicUpdateChecker Checker(*this);
    if (Checker.checkStatement(
            Body, (AtomicKind == ACCC_update)
                      ? diag::err_acc_atomic_update_not_expression_statement
                      : diag::err_acc_atomic_not_expression_statement,
            diag::note_acc_atomic_update))
      return StmtError();
    if (!CurContext->isDependentContext()) {
      E = Checker.getExpr();
      X = Checker.getX();
      UE = Checker.getUpdateExpr();
      IsXLHSInRHSPart = Checker.isXLHSInRHSPart();
    }
  } else if (AtomicKind == ACCC_capture) {
    enum {
      NotAnAssignmentOp,
      NotACompoundStatement,
      NotTwoSubstatements,
      NotASpecificExpression,
      NoError
    } ErrorFound = NoError;
    SourceLocation ErrorLoc, NoteLoc;
    SourceRange ErrorRange, NoteRange;
    if (auto *AtomicBody = dyn_cast<Expr>(Body)) {
      // If clause is a capture:
      //  v = x++;
      //  v = x--;
      //  v = ++x;
      //  v = --x;
      //  v = x binop= expr;
      //  v = x = x binop expr;
      //  v = x = expr binop x;
      auto *AtomicBinOp =
          dyn_cast<BinaryOperator>(AtomicBody->IgnoreParenImpCasts());
      if (AtomicBinOp && AtomicBinOp->getOpcode() == BO_Assign) {
        V = AtomicBinOp->getLHS();
        Body = AtomicBinOp->getRHS()->IgnoreParenImpCasts();
        OpenACCAtomicUpdateChecker Checker(*this);
        if (Checker.checkStatement(
                Body, diag::err_acc_atomic_capture_not_expression_statement,
                diag::note_acc_atomic_update))
          return StmtError();
        E = Checker.getExpr();
        X = Checker.getX();
        UE = Checker.getUpdateExpr();
        IsXLHSInRHSPart = Checker.isXLHSInRHSPart();
        IsPostfixUpdate = Checker.isPostfixUpdate();
      } else if (!AtomicBody->isInstantiationDependent()) {
        ErrorLoc = AtomicBody->getExprLoc();
        ErrorRange = AtomicBody->getSourceRange();
        NoteLoc = AtomicBinOp ? AtomicBinOp->getOperatorLoc()
                              : AtomicBody->getExprLoc();
        NoteRange = AtomicBinOp ? AtomicBinOp->getSourceRange()
                                : AtomicBody->getSourceRange();
        ErrorFound = NotAnAssignmentOp;
      }
      if (ErrorFound != NoError) {
        Diag(ErrorLoc, diag::err_acc_atomic_capture_not_expression_statement)
            << ErrorRange;
        Diag(NoteLoc, diag::note_acc_atomic_capture) << ErrorFound << NoteRange;
        return StmtError();
      } else if (CurContext->isDependentContext()) {
        UE = V = E = X = nullptr;
      }
    } else {
      // If clause is a capture:
      //  { v = x; x = expr; }
      //  { v = x; x++; }
      //  { v = x; x--; }
      //  { v = x; ++x; }
      //  { v = x; --x; }
      //  { v = x; x binop= expr; }
      //  { v = x; x = x binop expr; }
      //  { v = x; x = expr binop x; }
      //  { x++; v = x; }
      //  { x--; v = x; }
      //  { ++x; v = x; }
      //  { --x; v = x; }
      //  { x binop= expr; v = x; }
      //  { x = x binop expr; v = x; }
      //  { x = expr binop x; v = x; }
      if (auto *CS = dyn_cast<CompoundStmt>(Body)) {
        // Check that this is { expr1; expr2; }
        if (CS->size() == 2) {
          auto *First = CS->body_front();
          auto *Second = CS->body_back();
          if (auto *EWC = dyn_cast<ExprWithCleanups>(First))
            First = EWC->getSubExpr()->IgnoreParenImpCasts();
          if (auto *EWC = dyn_cast<ExprWithCleanups>(Second))
            Second = EWC->getSubExpr()->IgnoreParenImpCasts();
          // Need to find what subexpression is 'v' and what is 'x'.
          OpenACCAtomicUpdateChecker Checker(*this);
          bool IsUpdateExprFound = !Checker.checkStatement(Second);
          BinaryOperator *BinOp = nullptr;
          if (IsUpdateExprFound) {
            BinOp = dyn_cast<BinaryOperator>(First);
            IsUpdateExprFound = BinOp && BinOp->getOpcode() == BO_Assign;
          }
          if (IsUpdateExprFound && !CurContext->isDependentContext()) {
            //  { v = x; x++; }
            //  { v = x; x--; }
            //  { v = x; ++x; }
            //  { v = x; --x; }
            //  { v = x; x binop= expr; }
            //  { v = x; x = x binop expr; }
            //  { v = x; x = expr binop x; }
            // Check that the first expression has form v = x.
            auto *PossibleX = BinOp->getRHS()->IgnoreParenImpCasts();
            llvm::FoldingSetNodeID XId, PossibleXId;
            Checker.getX()->Profile(XId, Context, /*Canonical=*/true);
            PossibleX->Profile(PossibleXId, Context, /*Canonical=*/true);
            IsUpdateExprFound = XId == PossibleXId;
            if (IsUpdateExprFound) {
              V = BinOp->getLHS();
              X = Checker.getX();
              E = Checker.getExpr();
              UE = Checker.getUpdateExpr();
              IsXLHSInRHSPart = Checker.isXLHSInRHSPart();
              IsPostfixUpdate = true;
            }
          }
          if (!IsUpdateExprFound) {
            IsUpdateExprFound = !Checker.checkStatement(First);
            BinOp = nullptr;
            if (IsUpdateExprFound) {
              BinOp = dyn_cast<BinaryOperator>(Second);
              IsUpdateExprFound = BinOp && BinOp->getOpcode() == BO_Assign;
            }
            if (IsUpdateExprFound && !CurContext->isDependentContext()) {
              //  { x++; v = x; }
              //  { x--; v = x; }
              //  { ++x; v = x; }
              //  { --x; v = x; }
              //  { x binop= expr; v = x; }
              //  { x = x binop expr; v = x; }
              //  { x = expr binop x; v = x; }
              // Check that the second expression has form v = x.
              auto *PossibleX = BinOp->getRHS()->IgnoreParenImpCasts();
              llvm::FoldingSetNodeID XId, PossibleXId;
              Checker.getX()->Profile(XId, Context, /*Canonical=*/true);
              PossibleX->Profile(PossibleXId, Context, /*Canonical=*/true);
              IsUpdateExprFound = XId == PossibleXId;
              if (IsUpdateExprFound) {
                V = BinOp->getLHS();
                X = Checker.getX();
                E = Checker.getExpr();
                UE = Checker.getUpdateExpr();
                IsXLHSInRHSPart = Checker.isXLHSInRHSPart();
                IsPostfixUpdate = false;
              }
            }
          }
          if (!IsUpdateExprFound) {
            //  { v = x; x = expr; }
            auto *FirstExpr = dyn_cast<Expr>(First);
            auto *SecondExpr = dyn_cast<Expr>(Second);
            if (!FirstExpr || !SecondExpr ||
                !(FirstExpr->isInstantiationDependent() ||
                  SecondExpr->isInstantiationDependent())) {
              auto *FirstBinOp = dyn_cast<BinaryOperator>(First);
              if (!FirstBinOp || FirstBinOp->getOpcode() != BO_Assign) {
                ErrorFound = NotAnAssignmentOp;
                NoteLoc = ErrorLoc = FirstBinOp ? FirstBinOp->getOperatorLoc()
                                                : First->getLocStart();
                NoteRange = ErrorRange = FirstBinOp
                                             ? FirstBinOp->getSourceRange()
                                             : SourceRange(ErrorLoc, ErrorLoc);
              } else {
                auto *SecondBinOp = dyn_cast<BinaryOperator>(Second);
                if (!SecondBinOp || SecondBinOp->getOpcode() != BO_Assign) {
                  ErrorFound = NotAnAssignmentOp;
                  NoteLoc = ErrorLoc = SecondBinOp
                                           ? SecondBinOp->getOperatorLoc()
                                           : Second->getLocStart();
                  NoteRange = ErrorRange =
                      SecondBinOp ? SecondBinOp->getSourceRange()
                                  : SourceRange(ErrorLoc, ErrorLoc);
                } else {
                  auto *PossibleXRHSInFirst =
                      FirstBinOp->getRHS()->IgnoreParenImpCasts();
                  auto *PossibleXLHSInSecond =
                      SecondBinOp->getLHS()->IgnoreParenImpCasts();
                  llvm::FoldingSetNodeID X1Id, X2Id;
                  PossibleXRHSInFirst->Profile(X1Id, Context,
                                               /*Canonical=*/true);
                  PossibleXLHSInSecond->Profile(X2Id, Context,
                                                /*Canonical=*/true);
                  IsUpdateExprFound = X1Id == X2Id;
                  if (IsUpdateExprFound) {
                    V = FirstBinOp->getLHS();
                    X = SecondBinOp->getLHS();
                    E = SecondBinOp->getRHS();
                    UE = nullptr;
                    IsXLHSInRHSPart = false;
                    IsPostfixUpdate = true;
                  } else {
                    ErrorFound = NotASpecificExpression;
                    ErrorLoc = FirstBinOp->getExprLoc();
                    ErrorRange = FirstBinOp->getSourceRange();
                    NoteLoc = SecondBinOp->getLHS()->getExprLoc();
                    NoteRange = SecondBinOp->getRHS()->getSourceRange();
                  }
                }
              }
            }
          }
        } else {
          NoteLoc = ErrorLoc = Body->getLocStart();
          NoteRange = ErrorRange =
              SourceRange(Body->getLocStart(), Body->getLocStart());
          ErrorFound = NotTwoSubstatements;
        }
      } else {
        NoteLoc = ErrorLoc = Body->getLocStart();
        NoteRange = ErrorRange =
            SourceRange(Body->getLocStart(), Body->getLocStart());
        ErrorFound = NotACompoundStatement;
      }
      if (ErrorFound != NoError) {
        Diag(ErrorLoc, diag::err_acc_atomic_capture_not_compound_statement)
            << ErrorRange;
        Diag(NoteLoc, diag::note_acc_atomic_capture) << ErrorFound << NoteRange;
        return StmtError();
      } else if (CurContext->isDependentContext()) {
        UE = V = E = X = nullptr;
      }
    }
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCAtomicDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt,
                                    X, V, E, UE, IsXLHSInRHSPart,
                                    IsPostfixUpdate);
}

StmtResult Sema::ActOnOpenACCTargetDirective(ArrayRef<ACCClause *> Clauses,
                                            Stmt *AStmt,
                                            SourceLocation StartLoc,
                                            SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  // OpenACC [2.16, Nesting of Regions]
  // If specified, a teams construct must be contained within a target
  // construct. That target construct must contain no statements or directives
  // outside of the teams construct.
  if (DSAStack->hasInnerTeamsRegion()) {
    Stmt *S = CS->IgnoreContainers(/*IgnoreCaptured=*/true);
    bool ACCTeamsFound = true;
    if (auto *CS = dyn_cast<CompoundStmt>(S)) {
      auto I = CS->body_begin();
      while (I != CS->body_end()) {
        auto *OED = dyn_cast<ACCExecutableDirective>(*I);
        if (!OED || !isOpenACCTeamsDirective(OED->getDirectiveKind())) {
          ACCTeamsFound = false;
          break;
        }
        ++I;
      }
      assert(I != CS->body_end() && "Not found statement");
      S = *I;
    } else {
      auto *OED = dyn_cast<ACCExecutableDirective>(S);
      ACCTeamsFound = OED && isOpenACCTeamsDirective(OED->getDirectiveKind());
    }
    if (!ACCTeamsFound) {
      Diag(StartLoc, diag::err_acc_target_contains_not_only_teams);
      Diag(DSAStack->getInnerTeamsRegionLoc(),
           diag::note_acc_nested_teams_construct_here);
      Diag(S->getLocStart(), diag::note_acc_nested_statement_here)
          << isa<ACCExecutableDirective>(S);
      return StmtError();
    }
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCTargetDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt);
}

StmtResult
Sema::ActOnOpenACCTargetParallelDirective(ArrayRef<ACCClause *> Clauses,
                                         Stmt *AStmt, SourceLocation StartLoc,
                                         SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_parallel);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCTargetParallelDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                            AStmt);
}

StmtResult Sema::ActOnOpenACCTargetParallelForDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_parallel_for);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_target_parallel_for, getCollapseNumberExpr(Clauses),
                      getOrderedNumberExpr(Clauses), CS, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target parallel for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetParallelForDirective::Create(Context, StartLoc, EndLoc,
                                               NestedLoopCount, Clauses, AStmt,
                                               B, DSAStack->isCancelRegion());
}

/// Check for existence of a map clause in the list of clauses.
static bool hasClauses(ArrayRef<ACCClause *> Clauses,
                       const OpenACCClauseKind K) {
  return llvm::any_of(
      Clauses, [K](const ACCClause *C) { return C->getClauseKind() == K; });
}

template <typename... Params>
static bool hasClauses(ArrayRef<ACCClause *> Clauses, const OpenACCClauseKind K,
                       const Params... ClauseTypes) {
  return hasClauses(Clauses, K) || hasClauses(Clauses, ClauseTypes...);
}

StmtResult Sema::ActOnOpenACCTargetDataDirective(ArrayRef<ACCClause *> Clauses,
                                                Stmt *AStmt,
                                                SourceLocation StartLoc,
                                                SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");

  // OpenACC [2.10.1, Restrictions, p. 97]
  // At least one map clause must appear on the directive.
  if (!hasClauses(Clauses, ACCC_map, ACCC_use_device_ptr)) {
    Diag(StartLoc, diag::err_acc_no_clause_for_directive)
        << "'map' or 'use_device_ptr'"
        << getOpenACCDirectiveName(ACCD_target_data);
    return StmtError();
  }

  getCurFunction()->setHasBranchProtectedScope();

  return ACCTargetDataDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                        AStmt);
}

StmtResult
Sema::ActOnOpenACCTargetEnterDataDirective(ArrayRef<ACCClause *> Clauses,
                                          SourceLocation StartLoc,
                                          SourceLocation EndLoc, Stmt *AStmt) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_enter_data);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  // OpenACC [2.10.2, Restrictions, p. 99]
  // At least one map clause must appear on the directive.
  if (!hasClauses(Clauses, ACCC_map)) {
    Diag(StartLoc, diag::err_acc_no_clause_for_directive)
        << "'map'" << getOpenACCDirectiveName(ACCD_target_enter_data);
    return StmtError();
  }

  return ACCTargetEnterDataDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                             AStmt);
}

StmtResult
Sema::ActOnOpenACCTargetExitDataDirective(ArrayRef<ACCClause *> Clauses,
                                         SourceLocation StartLoc,
                                         SourceLocation EndLoc, Stmt *AStmt) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_exit_data);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  // OpenACC [2.10.3, Restrictions, p. 102]
  // At least one map clause must appear on the directive.
  if (!hasClauses(Clauses, ACCC_map)) {
    Diag(StartLoc, diag::err_acc_no_clause_for_directive)
        << "'map'" << getOpenACCDirectiveName(ACCD_target_exit_data);
    return StmtError();
  }

  return ACCTargetExitDataDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                            AStmt);
}

StmtResult Sema::ActOnOpenACCTargetUpdateDirective(ArrayRef<ACCClause *> Clauses,
                                                  SourceLocation StartLoc,
                                                  SourceLocation EndLoc,
                                                  Stmt *AStmt) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_update);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  if (!hasClauses(Clauses, ACCC_to, ACCC_from)) {
    Diag(StartLoc, diag::err_acc_at_least_one_motion_clause_required);
    return StmtError();
  }
  return ACCTargetUpdateDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                          AStmt);
}

StmtResult Sema::ActOnOpenACCTeamsDirective(ArrayRef<ACCClause *> Clauses,
                                           Stmt *AStmt, SourceLocation StartLoc,
                                           SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  getCurFunction()->setHasBranchProtectedScope();

  DSAStack->setParentTeamsRegionLoc(StartLoc);

  return ACCTeamsDirective::Create(Context, StartLoc, EndLoc, Clauses, AStmt);
}

StmtResult
Sema::ActOnOpenACCCancellationPointDirective(SourceLocation StartLoc,
                                            SourceLocation EndLoc,
                                            OpenACCDirectiveKind CancelRegion) {
  if (DSAStack->isParentNowaitRegion()) {
    Diag(StartLoc, diag::err_acc_parent_cancel_region_nowait) << 0;
    return StmtError();
  }
  if (DSAStack->isParentOrderedRegion()) {
    Diag(StartLoc, diag::err_acc_parent_cancel_region_ordered) << 0;
    return StmtError();
  }
  return ACCCancellationPointDirective::Create(Context, StartLoc, EndLoc,
                                               CancelRegion);
}

StmtResult Sema::ActOnOpenACCCancelDirective(ArrayRef<ACCClause *> Clauses,
                                            SourceLocation StartLoc,
                                            SourceLocation EndLoc,
                                            OpenACCDirectiveKind CancelRegion) {
  if (DSAStack->isParentNowaitRegion()) {
    Diag(StartLoc, diag::err_acc_parent_cancel_region_nowait) << 1;
    return StmtError();
  }
  if (DSAStack->isParentOrderedRegion()) {
    Diag(StartLoc, diag::err_acc_parent_cancel_region_ordered) << 1;
    return StmtError();
  }
  DSAStack->setParentCancelRegion(/*Cancel=*/true);
  return ACCCancelDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                    CancelRegion);
}

static bool checkGrainsizeNumTasksClauses(Sema &S,
                                          ArrayRef<ACCClause *> Clauses) {
  ACCClause *PrevClause = nullptr;
  bool ErrorFound = false;
  for (auto *C : Clauses) {
    if (C->getClauseKind() == ACCC_grainsize ||
        C->getClauseKind() == ACCC_num_tasks) {
      if (!PrevClause)
        PrevClause = C;
      else if (PrevClause->getClauseKind() != C->getClauseKind()) {
        S.Diag(C->getLocStart(),
               diag::err_acc_grainsize_num_tasks_mutually_exclusive)
            << getOpenACCClauseName(C->getClauseKind())
            << getOpenACCClauseName(PrevClause->getClauseKind());
        S.Diag(PrevClause->getLocStart(),
               diag::note_acc_previous_grainsize_num_tasks)
            << getOpenACCClauseName(PrevClause->getClauseKind());
        ErrorFound = true;
      }
    }
  }
  return ErrorFound;
}

static bool checkReductionClauseWithNogroup(Sema &S,
                                            ArrayRef<ACCClause *> Clauses) {
  ACCClause *ReductionClause = nullptr;
  ACCClause *NogroupClause = nullptr;
  for (auto *C : Clauses) {
    if (C->getClauseKind() == ACCC_reduction) {
      ReductionClause = C;
      if (NogroupClause)
        break;
      continue;
    }
    if (C->getClauseKind() == ACCC_nogroup) {
      NogroupClause = C;
      if (ReductionClause)
        break;
      continue;
    }
  }
  if (ReductionClause && NogroupClause) {
    S.Diag(ReductionClause->getLocStart(), diag::err_acc_reduction_with_nogroup)
        << SourceRange(NogroupClause->getLocStart(),
                       NogroupClause->getLocEnd());
    return true;
  }
  return false;
}

StmtResult Sema::ActOnOpenACCTaskLoopDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_taskloop, getCollapseNumberExpr(Clauses),
                      /*OrderedLoopCountExpr=*/nullptr, AStmt, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  // OpenACC, [2.9.2 taskloop Construct, Restrictions]
  // The grainsize clause and num_tasks clause are mutually exclusive and may
  // not appear on the same taskloop directive.
  if (checkGrainsizeNumTasksClauses(*this, Clauses))
    return StmtError();
  // OpenACC, [2.9.2 taskloop Construct, Restrictions]
  // If a reduction clause is present on the taskloop directive, the nogroup
  // clause must not be specified.
  if (checkReductionClauseWithNogroup(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTaskLoopDirective::Create(Context, StartLoc, EndLoc,
                                      NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTaskLoopSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_taskloop_simd, getCollapseNumberExpr(Clauses),
                      /*OrderedLoopCountExpr=*/nullptr, AStmt, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  // OpenACC, [2.9.2 taskloop Construct, Restrictions]
  // The grainsize clause and num_tasks clause are mutually exclusive and may
  // not appear on the same taskloop directive.
  if (checkGrainsizeNumTasksClauses(*this, Clauses))
    return StmtError();
  // OpenACC, [2.9.2 taskloop Construct, Restrictions]
  // If a reduction clause is present on the taskloop directive, the nogroup
  // clause must not be specified.
  if (checkReductionClauseWithNogroup(*this, Clauses))
    return StmtError();
  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTaskLoopSimdDirective::Create(Context, StartLoc, EndLoc,
                                          NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCDistributeDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  assert(isa<CapturedStmt>(AStmt) && "Captured statement expected");
  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_distribute, getCollapseNumberExpr(Clauses),
                      nullptr /*ordered not a clause on distribute*/, AStmt,
                      *this, *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  getCurFunction()->setHasBranchProtectedScope();
  return ACCDistributeDirective::Create(Context, StartLoc, EndLoc,
                                        NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCDistributeParallelForDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_distribute_parallel_for);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_distribute_parallel_for, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  getCurFunction()->setHasBranchProtectedScope();
  return ACCDistributeParallelForDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B,
      DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCDistributeParallelForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_distribute_parallel_for_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_distribute_parallel_for_simd, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCDistributeParallelForSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCDistributeSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_distribute_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_distribute_simd, getCollapseNumberExpr(Clauses),
                      nullptr /*ordered not a clause on distribute*/, CS, *this,
                      *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCDistributeSimdDirective::Create(Context, StartLoc, EndLoc,
                                            NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTargetParallelForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_parallel_for);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' or 'ordered' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_target_parallel_for_simd, getCollapseNumberExpr(Clauses),
      getOrderedNumberExpr(Clauses), CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target parallel for simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }
  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetParallelForSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTargetSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will define the
  // nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_target_simd, getCollapseNumberExpr(Clauses),
                      getOrderedNumberExpr(Clauses), CS, *this, *DSAStack,
                      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetSimdDirective::Create(Context, StartLoc, EndLoc,
                                        NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTeamsDistributeDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_teams_distribute);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount =
      CheckOpenACCLoop(ACCD_teams_distribute, getCollapseNumberExpr(Clauses),
                      nullptr /*ordered not a clause on distribute*/, CS, *this,
                      *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc teams distribute loop exprs were not built");

  getCurFunction()->setHasBranchProtectedScope();

  DSAStack->setParentTeamsRegionLoc(StartLoc);

  return ACCTeamsDistributeDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTeamsDistributeSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_teams_distribute_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }


  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_teams_distribute_simd, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);

  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc teams distribute simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();

  DSAStack->setParentTeamsRegionLoc(StartLoc);

  return ACCTeamsDistributeSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTeamsDistributeParallelForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_teams_distribute_parallel_for_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  auto NestedLoopCount = CheckOpenACCLoop(
      ACCD_teams_distribute_parallel_for_simd, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);

  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();

  DSAStack->setParentTeamsRegionLoc(StartLoc);

  return ACCTeamsDistributeParallelForSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTeamsDistributeParallelForDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_teams_distribute_parallel_for);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  unsigned NestedLoopCount = CheckOpenACCLoop(
      ACCD_teams_distribute_parallel_for, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);

  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc for loop exprs were not built");

  getCurFunction()->setHasBranchProtectedScope();

  DSAStack->setParentTeamsRegionLoc(StartLoc);

  return ACCTeamsDistributeParallelForDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B,
      DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCTargetTeamsDirective(ArrayRef<ACCClause *> Clauses,
                                                 Stmt *AStmt,
                                                 SourceLocation StartLoc,
                                                 SourceLocation EndLoc) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();

  for (int ThisCaptureLevel = getOpenACCCaptureLevels(ACCD_target_teams);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }
  getCurFunction()->setHasBranchProtectedScope();

  return ACCTargetTeamsDirective::Create(Context, StartLoc, EndLoc, Clauses,
                                         AStmt);
}

StmtResult Sema::ActOnOpenACCTargetTeamsDistributeDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_target_teams_distribute);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  auto NestedLoopCount = CheckOpenACCLoop(
      ACCD_target_teams_distribute, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target teams distribute loop exprs were not built");

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetTeamsDistributeDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTargetTeamsDistributeParallelForDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_target_teams_distribute_parallel_for);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  auto NestedLoopCount = CheckOpenACCLoop(
      ACCD_target_teams_distribute_parallel_for, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target teams distribute parallel for loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetTeamsDistributeParallelForDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B,
      DSAStack->isCancelRegion());
}

StmtResult Sema::ActOnOpenACCTargetTeamsDistributeParallelForSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  CapturedStmt *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel = getOpenACCCaptureLevels(
           ACCD_target_teams_distribute_parallel_for_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  auto NestedLoopCount =
      CheckOpenACCLoop(ACCD_target_teams_distribute_parallel_for_simd,
                      getCollapseNumberExpr(Clauses),
                      nullptr /*ordered not a clause on distribute*/, CS, *this,
                      *DSAStack, VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target teams distribute parallel for simd loop exprs were not "
         "built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetTeamsDistributeParallelForSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

StmtResult Sema::ActOnOpenACCTargetTeamsDistributeSimdDirective(
    ArrayRef<ACCClause *> Clauses, Stmt *AStmt, SourceLocation StartLoc,
    SourceLocation EndLoc,
    llvm::DenseMap<ValueDecl *, Expr *> &VarsWithImplicitDSA) {
  if (!AStmt)
    return StmtError();

  auto *CS = cast<CapturedStmt>(AStmt);
  // 1.2.2 OpenACC Language Terminology
  // Structured block - An executable statement with a single entry at the
  // top and a single exit at the bottom.
  // The point of exit cannot be a branch out of the structured block.
  // longjmp() and throw() must not violate the entry/exit criteria.
  CS->getCapturedDecl()->setNothrow();
  for (int ThisCaptureLevel =
           getOpenACCCaptureLevels(ACCD_target_teams_distribute_simd);
       ThisCaptureLevel > 1; --ThisCaptureLevel) {
    CS = cast<CapturedStmt>(CS->getCapturedStmt());
    // 1.2.2 OpenACC Language Terminology
    // Structured block - An executable statement with a single entry at the
    // top and a single exit at the bottom.
    // The point of exit cannot be a branch out of the structured block.
    // longjmp() and throw() must not violate the entry/exit criteria.
    CS->getCapturedDecl()->setNothrow();
  }

  ACCLoopDirective::HelperExprs B;
  // In presence of clause 'collapse' with number of loops, it will
  // define the nested loops number.
  auto NestedLoopCount = CheckOpenACCLoop(
      ACCD_target_teams_distribute_simd, getCollapseNumberExpr(Clauses),
      nullptr /*ordered not a clause on distribute*/, CS, *this, *DSAStack,
      VarsWithImplicitDSA, B);
  if (NestedLoopCount == 0)
    return StmtError();

  assert((CurContext->isDependentContext() || B.builtAll()) &&
         "acc target teams distribute simd loop exprs were not built");

  if (!CurContext->isDependentContext()) {
    // Finalize the clauses that need pre-built expressions for CodeGen.
    for (auto C : Clauses) {
      if (auto *LC = dyn_cast<ACCLinearClause>(C))
        if (FinishOpenACCLinearClause(*LC, cast<DeclRefExpr>(B.IterationVarRef),
                                     B.NumIterations, *this, CurScope,
                                     DSAStack))
          return StmtError();
    }
  }

  if (checkSimdlenSafelenSpecified(*this, Clauses))
    return StmtError();

  getCurFunction()->setHasBranchProtectedScope();
  return ACCTargetTeamsDistributeSimdDirective::Create(
      Context, StartLoc, EndLoc, NestedLoopCount, Clauses, AStmt, B);
}

ACCClause *Sema::ActOnOpenACCSingleExprClause(OpenACCClauseKind Kind, Expr *Expr,
                                             SourceLocation StartLoc,
                                             SourceLocation LParenLoc,
                                             SourceLocation EndLoc) {
  ACCClause *Res = nullptr;
  switch (Kind) {
  case ACCC_final:
    Res = ActOnOpenACCFinalClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_num_threads:
    Res = ActOnOpenACCNumThreadsClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_safelen:
    Res = ActOnOpenACCSafelenClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_simdlen:
    Res = ActOnOpenACCSimdlenClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_collapse:
    Res = ActOnOpenACCCollapseClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_ordered:
    Res = ActOnOpenACCOrderedClause(StartLoc, EndLoc, LParenLoc, Expr);
    break;
  case ACCC_device:
    Res = ActOnOpenACCDeviceClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_num_teams:
    Res = ActOnOpenACCNumTeamsClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_thread_limit:
    Res = ActOnOpenACCThreadLimitClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_priority:
    Res = ActOnOpenACCPriorityClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_grainsize:
    Res = ActOnOpenACCGrainsizeClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_num_tasks:
    Res = ActOnOpenACCNumTasksClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_hint:
    Res = ActOnOpenACCHintClause(Expr, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_if:
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_schedule:
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
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_threadprivate:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_depend:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_map:
  case ACCC_nogroup:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
  case ACCC_unknown:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Clause is not allowed.");
  }
  return Res;
}

// An OpenACC directive such as 'target parallel' has two captured regions:
// for the 'target' and 'parallel' respectively.  This function returns
// the region in which to capture expressions associated with a clause.
// A return value of ACCD_unknown signifies that the expression should not
// be captured.
static OpenACCDirectiveKind getOpenACCCaptureRegionForClause(
    OpenACCDirectiveKind DKind, OpenACCClauseKind CKind,
    OpenACCDirectiveKind NameModifier = ACCD_unknown) {
  OpenACCDirectiveKind CaptureRegion = ACCD_unknown;
  switch (CKind) {
  case ACCC_if:
    switch (DKind) {
    case ACCD_target_parallel:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
      // If this clause applies to the nested 'parallel' region, capture within
      // the 'target' region, otherwise do not capture.
      if (NameModifier == ACCD_unknown || NameModifier == ACCD_parallel)
        CaptureRegion = ACCD_target;
      break;
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      // If this clause applies to the nested 'parallel' region, capture within
      // the 'teams' region, otherwise do not capture.
      if (NameModifier == ACCD_unknown || NameModifier == ACCD_parallel)
        CaptureRegion = ACCD_teams;
      break;
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_teams;
      break;
    case ACCD_target_update:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
      CaptureRegion = ACCD_task;
      break;
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_teams:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_target_data:
      // Do not capture if-clause expressions.
      break;
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_teams:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
      llvm_unreachable("Unexpected OpenACC directive with if-clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_num_threads:
    switch (DKind) {
    case ACCD_target_parallel:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
      CaptureRegion = ACCD_target;
      break;
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_teams;
      break;
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
      // Do not capture num_threads-clause expressions.
      break;
    case ACCD_target_data:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target_update:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_teams:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_cancel:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_teams:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
      llvm_unreachable("Unexpected OpenACC directive with num_threads-clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_num_teams:
    switch (DKind) {
    case ACCD_target_teams:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_target;
      break;
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_teams:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
      // Do not capture num_teams-clause expressions.
      break;
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_target_data:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target_update:
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_parallel:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
      llvm_unreachable("Unexpected OpenACC directive with num_teams-clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_thread_limit:
    switch (DKind) {
    case ACCD_target_teams:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_target;
      break;
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_teams:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
      // Do not capture thread_limit-clause expressions.
      break;
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_target_data:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target_update:
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_parallel:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
      llvm_unreachable("Unexpected OpenACC directive with thread_limit-clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_schedule:
    switch (DKind) {
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_parallel;
      break;
    case ACCD_for:
    case ACCD_for_simd:
      // Do not capture schedule-clause expressions.
      break;
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_target_data:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target_update:
    case ACCD_teams:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_parallel:
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
    case ACCD_target_teams:
      llvm_unreachable("Unexpected OpenACC directive with schedule clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_dist_schedule:
    switch (DKind) {
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
      CaptureRegion = ACCD_teams;
      break;
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_distribute:
    case ACCD_distribute_simd:
      // Do not capture thread_limit-clause expressions.
      break;
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_target_parallel_for_simd:
    case ACCD_target_parallel_for:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_target_data:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target_update:
    case ACCD_teams:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_parallel:
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_target_teams:
      llvm_unreachable("Unexpected OpenACC directive with schedule clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_device:
    switch (DKind) {
    case ACCD_target_update:
    case ACCD_target_enter_data:
    case ACCD_target_exit_data:
    case ACCD_target:
    case ACCD_target_simd:
    case ACCD_target_teams:
    case ACCD_target_parallel:
    case ACCD_target_teams_distribute:
    case ACCD_target_teams_distribute_simd:
    case ACCD_target_parallel_for:
    case ACCD_target_parallel_for_simd:
    case ACCD_target_teams_distribute_parallel_for:
    case ACCD_target_teams_distribute_parallel_for_simd:
      CaptureRegion = ACCD_task;
      break;
    case ACCD_target_data:
      // Do not capture device-clause expressions.
      break;
    case ACCD_teams_distribute_parallel_for:
    case ACCD_teams_distribute_parallel_for_simd:
    case ACCD_teams:
    case ACCD_teams_distribute:
    case ACCD_teams_distribute_simd:
    case ACCD_distribute_parallel_for:
    case ACCD_distribute_parallel_for_simd:
    case ACCD_task:
    case ACCD_taskloop:
    case ACCD_taskloop_simd:
    case ACCD_cancel:
    case ACCD_parallel:
    case ACCD_parallel_sections:
    case ACCD_parellel_loop:
    case ACCD_parallel_for_simd:
    case ACCD_threadprivate:
    case ACCD_taskyield:
    case ACCD_barrier:
    case ACCD_taskwait:
    case ACCD_cancellation_point:
    case ACCD_flush:
    case ACCD_declare_reduction:
    case ACCD_declare_simd:
    case ACCD_declare_target:
    case ACCD_end_declare_target:
    case ACCD_simd:
    case ACCD_for:
    case ACCD_for_simd:
    case ACCD_sections:
    case ACCD_section:
    case ACCD_single:
    case ACCD_master:
    case ACCD_critical:
    case ACCD_taskgroup:
    case ACCD_distribute:
    case ACCD_ordered:
    case ACCD_atomic:
    case ACCD_distribute_simd:
      llvm_unreachable("Unexpected OpenACC directive with num_teams-clause");
    case ACCD_unknown:
      llvm_unreachable("Unknown OpenACC directive");
    }
    break;
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_linear:
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_final:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_shared:
  case ACCC_aligned:
  case ACCC_copyin:
  case ACCC_copyprivate:
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_threadprivate:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_depend:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_map:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_defaultmap:
  case ACCC_unknown:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Unexpected OpenACC clause.");
  }
  return CaptureRegion;
}

ACCClause *Sema::ActOnOpenACCIfClause(OpenACCDirectiveKind NameModifier,
                                     Expr *Condition, SourceLocation StartLoc,
                                     SourceLocation LParenLoc,
                                     SourceLocation NameModifierLoc,
                                     SourceLocation ColonLoc,
                                     SourceLocation EndLoc) {
  Expr *ValExpr = Condition;
  Stmt *HelperValStmt = nullptr;
  OpenACCDirectiveKind CaptureRegion = ACCD_unknown;
  if (!Condition->isValueDependent() && !Condition->isTypeDependent() &&
      !Condition->isInstantiationDependent() &&
      !Condition->containsUnexpandedParameterPack()) {
    ExprResult Val = CheckBooleanCondition(StartLoc, Condition);
    if (Val.isInvalid())
      return nullptr;

    ValExpr = Val.get();

    OpenACCDirectiveKind DKind = DSAStack->getCurrentDirective();
    CaptureRegion =
        getOpenACCCaptureRegionForClause(DKind, ACCC_if, NameModifier);
    if (CaptureRegion != ACCD_unknown && !CurContext->isDependentContext()) {
      ValExpr = MakeFullExpr(ValExpr).get();
      llvm::MapVector<Expr *, DeclRefExpr *> Captures;
      ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
      HelperValStmt = buildPreInits(Context, Captures);
    }
  }

  return new (Context)
      ACCIfClause(NameModifier, ValExpr, HelperValStmt, CaptureRegion, StartLoc,
                  LParenLoc, NameModifierLoc, ColonLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCFinalClause(Expr *Condition,
                                        SourceLocation StartLoc,
                                        SourceLocation LParenLoc,
                                        SourceLocation EndLoc) {
  Expr *ValExpr = Condition;
  if (!Condition->isValueDependent() && !Condition->isTypeDependent() &&
      !Condition->isInstantiationDependent() &&
      !Condition->containsUnexpandedParameterPack()) {
    ExprResult Val = CheckBooleanCondition(StartLoc, Condition);
    if (Val.isInvalid())
      return nullptr;

    ValExpr = MakeFullExpr(Val.get()).get();
  }

  return new (Context) ACCFinalClause(ValExpr, StartLoc, LParenLoc, EndLoc);
}
ExprResult Sema::PerformOpenACCImplicitIntegerConversion(SourceLocation Loc,
                                                        Expr *Op) {
  if (!Op)
    return ExprError();

  class IntConvertDiagnoser : public ICEConvertDiagnoser {
  public:
    IntConvertDiagnoser()
        : ICEConvertDiagnoser(/*AllowScopedEnumerations*/ false, false, true) {}
    SemaDiagnosticBuilder diagnoseNotInt(Sema &S, SourceLocation Loc,
                                         QualType T) override {
      return S.Diag(Loc, diag::err_acc_not_integral) << T;
    }
    SemaDiagnosticBuilder diagnoseIncomplete(Sema &S, SourceLocation Loc,
                                             QualType T) override {
      return S.Diag(Loc, diag::err_acc_incomplete_type) << T;
    }
    SemaDiagnosticBuilder diagnoseExplicitConv(Sema &S, SourceLocation Loc,
                                               QualType T,
                                               QualType ConvTy) override {
      return S.Diag(Loc, diag::err_acc_explicit_conversion) << T << ConvTy;
    }
    SemaDiagnosticBuilder noteExplicitConv(Sema &S, CXXConversionDecl *Conv,
                                           QualType ConvTy) override {
      return S.Diag(Conv->getLocation(), diag::note_acc_conversion_here)
             << ConvTy->isEnumeralType() << ConvTy;
    }
    SemaDiagnosticBuilder diagnoseAmbiguous(Sema &S, SourceLocation Loc,
                                            QualType T) override {
      return S.Diag(Loc, diag::err_acc_ambiguous_conversion) << T;
    }
    SemaDiagnosticBuilder noteAmbiguous(Sema &S, CXXConversionDecl *Conv,
                                        QualType ConvTy) override {
      return S.Diag(Conv->getLocation(), diag::note_acc_conversion_here)
             << ConvTy->isEnumeralType() << ConvTy;
    }
    SemaDiagnosticBuilder diagnoseConversion(Sema &, SourceLocation, QualType,
                                             QualType) override {
      llvm_unreachable("conversion functions are permitted");
    }
  } ConvertDiagnoser;
  return PerformContextualImplicitConversion(Loc, Op, ConvertDiagnoser);
}

static bool IsNonNegativeIntegerValue(Expr *&ValExpr, Sema &SemaRef,
                                      OpenACCClauseKind CKind,
                                      bool StrictlyPositive) {
  if (!ValExpr->isTypeDependent() && !ValExpr->isValueDependent() &&
      !ValExpr->isInstantiationDependent()) {
    SourceLocation Loc = ValExpr->getExprLoc();
    ExprResult Value =
        SemaRef.PerformOpenACCImplicitIntegerConversion(Loc, ValExpr);
    if (Value.isInvalid())
      return false;

    ValExpr = Value.get();
    // The expression must evaluate to a non-negative integer value.
    llvm::APSInt Result;
    if (ValExpr->isIntegerConstantExpr(Result, SemaRef.Context) &&
        Result.isSigned() &&
        !((!StrictlyPositive && Result.isNonNegative()) ||
          (StrictlyPositive && Result.isStrictlyPositive()))) {
      SemaRef.Diag(Loc, diag::err_acc_negative_expression_in_clause)
          << getOpenACCClauseName(CKind) << (StrictlyPositive ? 1 : 0)
          << ValExpr->getSourceRange();
      return false;
    }
  }
  return true;
}

ACCClause *Sema::ActOnOpenACCNumThreadsClause(Expr *NumThreads,
                                             SourceLocation StartLoc,
                                             SourceLocation LParenLoc,
                                             SourceLocation EndLoc) {
  Expr *ValExpr = NumThreads;
  Stmt *HelperValStmt = nullptr;

  // OpenACC [2.5, Restrictions]
  //  The num_threads expression must evaluate to a positive integer value.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_num_threads,
                                 /*StrictlyPositive=*/true))
    return nullptr;

  OpenACCDirectiveKind DKind = DSAStack->getCurrentDirective();
  OpenACCDirectiveKind CaptureRegion =
      getOpenACCCaptureRegionForClause(DKind, ACCC_num_threads);
  if (CaptureRegion != ACCD_unknown && !CurContext->isDependentContext()) {
    ValExpr = MakeFullExpr(ValExpr).get();
    llvm::MapVector<Expr *, DeclRefExpr *> Captures;
    ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
    HelperValStmt = buildPreInits(Context, Captures);
  }

  return new (Context) ACCNumThreadsClause(
      ValExpr, HelperValStmt, CaptureRegion, StartLoc, LParenLoc, EndLoc);
}

ExprResult Sema::VerifyPositiveIntegerConstantInClause(Expr *E,
                                                       OpenACCClauseKind CKind,
                                                       bool StrictlyPositive) {
  if (!E)
    return ExprError();
  if (E->isValueDependent() || E->isTypeDependent() ||
      E->isInstantiationDependent() || E->containsUnexpandedParameterPack())
    return E;
  llvm::APSInt Result;
  ExprResult ICE = VerifyIntegerConstantExpression(E, &Result);
  if (ICE.isInvalid())
    return ExprError();
  if ((StrictlyPositive && !Result.isStrictlyPositive()) ||
      (!StrictlyPositive && !Result.isNonNegative())) {
    Diag(E->getExprLoc(), diag::err_acc_negative_expression_in_clause)
        << getOpenACCClauseName(CKind) << (StrictlyPositive ? 1 : 0)
        << E->getSourceRange();
    return ExprError();
  }
  if (CKind == ACCC_aligned && !Result.isPowerOf2()) {
    Diag(E->getExprLoc(), diag::warn_acc_alignment_not_power_of_two)
        << E->getSourceRange();
    return ExprError();
  }
  if (CKind == ACCC_collapse && DSAStack->getAssociatedLoops() == 1)
    DSAStack->setAssociatedLoops(Result.getExtValue());
  else if (CKind == ACCC_ordered)
    DSAStack->setAssociatedLoops(Result.getExtValue());
  return ICE;
}

ACCClause *Sema::ActOnOpenACCSafelenClause(Expr *Len, SourceLocation StartLoc,
                                          SourceLocation LParenLoc,
                                          SourceLocation EndLoc) {
  // OpenACC [2.8.1, simd construct, Description]
  // The parameter of the safelen clause must be a constant
  // positive integer expression.
  ExprResult Safelen = VerifyPositiveIntegerConstantInClause(Len, ACCC_safelen);
  if (Safelen.isInvalid())
    return nullptr;
  return new (Context)
      ACCSafelenClause(Safelen.get(), StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCSimdlenClause(Expr *Len, SourceLocation StartLoc,
                                          SourceLocation LParenLoc,
                                          SourceLocation EndLoc) {
  // OpenACC [2.8.1, simd construct, Description]
  // The parameter of the simdlen clause must be a constant
  // positive integer expression.
  ExprResult Simdlen = VerifyPositiveIntegerConstantInClause(Len, ACCC_simdlen);
  if (Simdlen.isInvalid())
    return nullptr;
  return new (Context)
      ACCSimdlenClause(Simdlen.get(), StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCCollapseClause(Expr *NumForLoops,
                                           SourceLocation StartLoc,
                                           SourceLocation LParenLoc,
                                           SourceLocation EndLoc) {
  // OpenACC [2.7.1, loop construct, Description]
  // OpenACC [2.8.1, simd construct, Description]
  // OpenACC [2.9.6, distribute construct, Description]
  // The parameter of the collapse clause must be a constant
  // positive integer expression.
  ExprResult NumForLoopsResult =
      VerifyPositiveIntegerConstantInClause(NumForLoops, ACCC_collapse);
  if (NumForLoopsResult.isInvalid())
    return nullptr;
  return new (Context)
      ACCCollapseClause(NumForLoopsResult.get(), StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCOrderedClause(SourceLocation StartLoc,
                                          SourceLocation EndLoc,
                                          SourceLocation LParenLoc,
                                          Expr *NumForLoops) {
  // OpenACC [2.7.1, loop construct, Description]
  // OpenACC [2.8.1, simd construct, Description]
  // OpenACC [2.9.6, distribute construct, Description]
  // The parameter of the ordered clause must be a constant
  // positive integer expression if any.
  if (NumForLoops && LParenLoc.isValid()) {
    ExprResult NumForLoopsResult =
        VerifyPositiveIntegerConstantInClause(NumForLoops, ACCC_ordered);
    if (NumForLoopsResult.isInvalid())
      return nullptr;
    NumForLoops = NumForLoopsResult.get();
  } else
    NumForLoops = nullptr;
  DSAStack->setOrderedRegion(/*IsOrdered=*/true, NumForLoops);
  return new (Context)
      ACCOrderedClause(NumForLoops, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCSimpleClause(
    OpenACCClauseKind Kind, unsigned Argument, SourceLocation ArgumentLoc,
    SourceLocation StartLoc, SourceLocation LParenLoc, SourceLocation EndLoc) {
  ACCClause *Res = nullptr;
  switch (Kind) {
  case ACCC_default:
    Res =
        ActOnOpenACCDefaultClause(static_cast<OpenACCDefaultClauseKind>(Argument),
                                 ArgumentLoc, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_proc_bind:
    Res = ActOnOpenACCProcBindClause(
        static_cast<OpenACCProcBindClauseKind>(Argument), ArgumentLoc, StartLoc,
        LParenLoc, EndLoc);
    break;
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_schedule:
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
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_threadprivate:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_depend:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_map:
  case ACCC_num_teams:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
  case ACCC_unknown:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Clause is not allowed.");
  }
  return Res;
}

static std::string
getListOfPossibleValues(OpenACCClauseKind K, unsigned First, unsigned Last,
                        ArrayRef<unsigned> Exclude = llvm::None) {
  std::string Values;
  unsigned Bound = Last >= 2 ? Last - 2 : 0;
  unsigned Skipped = Exclude.size();
  auto S = Exclude.begin(), E = Exclude.end();
  for (unsigned i = First; i < Last; ++i) {
    if (std::find(S, E, i) != E) {
      --Skipped;
      continue;
    }
    Values += "'";
    Values += getOpenACCSimpleClauseTypeName(K, i);
    Values += "'";
    if (i == Bound - Skipped)
      Values += " or ";
    else if (i != Bound + 1 - Skipped)
      Values += ", ";
  }
  return Values;
}

ACCClause *Sema::ActOnOpenACCDefaultClause(OpenACCDefaultClauseKind Kind,
                                          SourceLocation KindKwLoc,
                                          SourceLocation StartLoc,
                                          SourceLocation LParenLoc,
                                          SourceLocation EndLoc) {
  if (Kind == ACCC_DEFAULT_unknown) {
    static_assert(ACCC_DEFAULT_unknown > 0,
                  "ACCC_DEFAULT_unknown not greater than 0");
    Diag(KindKwLoc, diag::err_acc_unexpected_clause_value)
        << getListOfPossibleValues(ACCC_default, /*First=*/0,
                                   /*Last=*/ACCC_DEFAULT_unknown)
        << getOpenACCClauseName(ACCC_default);
    return nullptr;
  }
  switch (Kind) {
  case ACCC_DEFAULT_none:
    DSAStack->setDefaultDSANone(KindKwLoc);
    break;
  case ACCC_DEFAULT_shared:
    DSAStack->setDefaultDSAShared(KindKwLoc);
    break;
  case ACCC_DEFAULT_unknown:
    llvm_unreachable("Clause kind is not allowed.");
    break;
  }
  return new (Context)
      ACCDefaultClause(Kind, KindKwLoc, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCProcBindClause(OpenACCProcBindClauseKind Kind,
                                           SourceLocation KindKwLoc,
                                           SourceLocation StartLoc,
                                           SourceLocation LParenLoc,
                                           SourceLocation EndLoc) {
  if (Kind == ACCC_PROC_BIND_unknown) {
    Diag(KindKwLoc, diag::err_acc_unexpected_clause_value)
        << getListOfPossibleValues(ACCC_proc_bind, /*First=*/0,
                                   /*Last=*/ACCC_PROC_BIND_unknown)
        << getOpenACCClauseName(ACCC_proc_bind);
    return nullptr;
  }
  return new (Context)
      ACCProcBindClause(Kind, KindKwLoc, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCSingleExprWithArgClause(
    OpenACCClauseKind Kind, ArrayRef<unsigned> Argument, Expr *Expr,
    SourceLocation StartLoc, SourceLocation LParenLoc,
    ArrayRef<SourceLocation> ArgumentLoc, SourceLocation DelimLoc,
    SourceLocation EndLoc) {
  ACCClause *Res = nullptr;
  switch (Kind) {
  case ACCC_schedule:
    enum { Modifier1, Modifier2, ScheduleKind, NumberOfElements };
    assert(Argument.size() == NumberOfElements &&
           ArgumentLoc.size() == NumberOfElements);
    Res = ActOnOpenACCScheduleClause(
        static_cast<OpenACCScheduleClauseModifier>(Argument[Modifier1]),
        static_cast<OpenACCScheduleClauseModifier>(Argument[Modifier2]),
        static_cast<OpenACCScheduleClauseKind>(Argument[ScheduleKind]), Expr,
        StartLoc, LParenLoc, ArgumentLoc[Modifier1], ArgumentLoc[Modifier2],
        ArgumentLoc[ScheduleKind], DelimLoc, EndLoc);
    break;
  case ACCC_if:
    assert(Argument.size() == 1 && ArgumentLoc.size() == 1);
    Res = ActOnOpenACCIfClause(static_cast<OpenACCDirectiveKind>(Argument.back()),
                              Expr, StartLoc, LParenLoc, ArgumentLoc.back(),
                              DelimLoc, EndLoc);
    break;
  case ACCC_dist_schedule:
    Res = ActOnOpenACCDistScheduleClause(
        static_cast<OpenACCDistScheduleClauseKind>(Argument.back()), Expr,
        StartLoc, LParenLoc, ArgumentLoc.back(), DelimLoc, EndLoc);
    break;
  case ACCC_defaultmap:
    enum { Modifier, DefaultmapKind };
    Res = ActOnOpenACCDefaultmapClause(
        static_cast<OpenACCDefaultmapClauseModifier>(Argument[Modifier]),
        static_cast<OpenACCDefaultmapClauseKind>(Argument[DefaultmapKind]),
        StartLoc, LParenLoc, ArgumentLoc[Modifier], ArgumentLoc[DefaultmapKind],
        EndLoc);
    break;
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_default:
  case ACCC_proc_bind:
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
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_threadprivate:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_depend:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_map:
  case ACCC_num_teams:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_unknown:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Clause is not allowed.");
  }
  return Res;
}

static bool checkScheduleModifiers(Sema &S, OpenACCScheduleClauseModifier M1,
                                   OpenACCScheduleClauseModifier M2,
                                   SourceLocation M1Loc, SourceLocation M2Loc) {
  if (M1 == ACCC_SCHEDULE_MODIFIER_unknown && M1Loc.isValid()) {
    SmallVector<unsigned, 2> Excluded;
    if (M2 != ACCC_SCHEDULE_MODIFIER_unknown)
      Excluded.push_back(M2);
    if (M2 == ACCC_SCHEDULE_MODIFIER_nonmonotonic)
      Excluded.push_back(ACCC_SCHEDULE_MODIFIER_monotonic);
    if (M2 == ACCC_SCHEDULE_MODIFIER_monotonic)
      Excluded.push_back(ACCC_SCHEDULE_MODIFIER_nonmonotonic);
    S.Diag(M1Loc, diag::err_acc_unexpected_clause_value)
        << getListOfPossibleValues(ACCC_schedule,
                                   /*First=*/ACCC_SCHEDULE_MODIFIER_unknown + 1,
                                   /*Last=*/ACCC_SCHEDULE_MODIFIER_last,
                                   Excluded)
        << getOpenACCClauseName(ACCC_schedule);
    return true;
  }
  return false;
}

ACCClause *Sema::ActOnOpenACCScheduleClause(
    OpenACCScheduleClauseModifier M1, OpenACCScheduleClauseModifier M2,
    OpenACCScheduleClauseKind Kind, Expr *ChunkSize, SourceLocation StartLoc,
    SourceLocation LParenLoc, SourceLocation M1Loc, SourceLocation M2Loc,
    SourceLocation KindLoc, SourceLocation CommaLoc, SourceLocation EndLoc) {
  if (checkScheduleModifiers(*this, M1, M2, M1Loc, M2Loc) ||
      checkScheduleModifiers(*this, M2, M1, M2Loc, M1Loc))
    return nullptr;
  // OpenACC, 2.7.1, Loop Construct, Restrictions
  // Either the monotonic modifier or the nonmonotonic modifier can be specified
  // but not both.
  if ((M1 == M2 && M1 != ACCC_SCHEDULE_MODIFIER_unknown) ||
      (M1 == ACCC_SCHEDULE_MODIFIER_monotonic &&
       M2 == ACCC_SCHEDULE_MODIFIER_nonmonotonic) ||
      (M1 == ACCC_SCHEDULE_MODIFIER_nonmonotonic &&
       M2 == ACCC_SCHEDULE_MODIFIER_monotonic)) {
    Diag(M2Loc, diag::err_acc_unexpected_schedule_modifier)
        << getOpenACCSimpleClauseTypeName(ACCC_schedule, M2)
        << getOpenACCSimpleClauseTypeName(ACCC_schedule, M1);
    return nullptr;
  }
  if (Kind == ACCC_SCHEDULE_unknown) {
    std::string Values;
    if (M1Loc.isInvalid() && M2Loc.isInvalid()) {
      unsigned Exclude[] = {ACCC_SCHEDULE_unknown};
      Values = getListOfPossibleValues(ACCC_schedule, /*First=*/0,
                                       /*Last=*/ACCC_SCHEDULE_MODIFIER_last,
                                       Exclude);
    } else {
      Values = getListOfPossibleValues(ACCC_schedule, /*First=*/0,
                                       /*Last=*/ACCC_SCHEDULE_unknown);
    }
    Diag(KindLoc, diag::err_acc_unexpected_clause_value)
        << Values << getOpenACCClauseName(ACCC_schedule);
    return nullptr;
  }
  // OpenACC, 2.7.1, Loop Construct, Restrictions
  // The nonmonotonic modifier can only be specified with schedule(dynamic) or
  // schedule(guided).
  if ((M1 == ACCC_SCHEDULE_MODIFIER_nonmonotonic ||
       M2 == ACCC_SCHEDULE_MODIFIER_nonmonotonic) &&
      Kind != ACCC_SCHEDULE_dynamic && Kind != ACCC_SCHEDULE_guided) {
    Diag(M1 == ACCC_SCHEDULE_MODIFIER_nonmonotonic ? M1Loc : M2Loc,
         diag::err_acc_schedule_nonmonotonic_static);
    return nullptr;
  }
  Expr *ValExpr = ChunkSize;
  Stmt *HelperValStmt = nullptr;
  if (ChunkSize) {
    if (!ChunkSize->isValueDependent() && !ChunkSize->isTypeDependent() &&
        !ChunkSize->isInstantiationDependent() &&
        !ChunkSize->containsUnexpandedParameterPack()) {
      SourceLocation ChunkSizeLoc = ChunkSize->getLocStart();
      ExprResult Val =
          PerformOpenACCImplicitIntegerConversion(ChunkSizeLoc, ChunkSize);
      if (Val.isInvalid())
        return nullptr;

      ValExpr = Val.get();

      // OpenACC [2.7.1, Restrictions]
      //  chunk_size must be a loop invariant integer expression with a positive
      //  value.
      llvm::APSInt Result;
      if (ValExpr->isIntegerConstantExpr(Result, Context)) {
        if (Result.isSigned() && !Result.isStrictlyPositive()) {
          Diag(ChunkSizeLoc, diag::err_acc_negative_expression_in_clause)
              << "schedule" << 1 << ChunkSize->getSourceRange();
          return nullptr;
        }
      } else if (getOpenACCCaptureRegionForClause(
                     DSAStack->getCurrentDirective(), ACCC_schedule) !=
                     ACCD_unknown &&
                 !CurContext->isDependentContext()) {
        ValExpr = MakeFullExpr(ValExpr).get();
        llvm::MapVector<Expr *, DeclRefExpr *> Captures;
        ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
        HelperValStmt = buildPreInits(Context, Captures);
      }
    }
  }

  return new (Context)
      ACCScheduleClause(StartLoc, LParenLoc, KindLoc, CommaLoc, EndLoc, Kind,
                        ValExpr, HelperValStmt, M1, M1Loc, M2, M2Loc);
}

ACCClause *Sema::ActOnOpenACCClause(OpenACCClauseKind Kind,
                                   SourceLocation StartLoc,
                                   SourceLocation EndLoc) {
  ACCClause *Res = nullptr;
  switch (Kind) {
  case ACCC_ordered:
    Res = ActOnOpenACCOrderedClause(StartLoc, EndLoc);
    break;
  case ACCC_nowait:
    Res = ActOnOpenACCNowaitClause(StartLoc, EndLoc);
    break;
  case ACCC_untied:
    Res = ActOnOpenACCUntiedClause(StartLoc, EndLoc);
    break;
  case ACCC_mergeable:
    Res = ActOnOpenACCMergeableClause(StartLoc, EndLoc);
    break;
  case ACCC_read:
    Res = ActOnOpenACCReadClause(StartLoc, EndLoc);
    break;
  case ACCC_write:
    Res = ActOnOpenACCWriteClause(StartLoc, EndLoc);
    break;
  case ACCC_update:
    Res = ActOnOpenACCUpdateClause(StartLoc, EndLoc);
    break;
  case ACCC_capture:
    Res = ActOnOpenACCCaptureClause(StartLoc, EndLoc);
    break;
  case ACCC_seq_cst:
    Res = ActOnOpenACCSeqCstClause(StartLoc, EndLoc);
    break;
  case ACCC_threads:
    Res = ActOnOpenACCThreadsClause(StartLoc, EndLoc);
    break;
  case ACCC_simd:
    Res = ActOnOpenACCSIMDClause(StartLoc, EndLoc);
    break;
  case ACCC_nogroup:
    Res = ActOnOpenACCNogroupClause(StartLoc, EndLoc);
    break;
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_schedule:
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
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_threadprivate:
  case ACCC_flush:
  case ACCC_depend:
  case ACCC_device:
  case ACCC_map:
  case ACCC_num_teams:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
  case ACCC_unknown:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    llvm_unreachable("Clause is not allowed.");
  }
  return Res;
}

ACCClause *Sema::ActOnOpenACCNowaitClause(SourceLocation StartLoc,
                                         SourceLocation EndLoc) {
  DSAStack->setNowaitRegion();
  return new (Context) ACCNowaitClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCUntiedClause(SourceLocation StartLoc,
                                         SourceLocation EndLoc) {
  return new (Context) ACCUntiedClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCMergeableClause(SourceLocation StartLoc,
                                            SourceLocation EndLoc) {
  return new (Context) ACCMergeableClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCReadClause(SourceLocation StartLoc,
                                       SourceLocation EndLoc) {
  return new (Context) ACCReadClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCWriteClause(SourceLocation StartLoc,
                                        SourceLocation EndLoc) {
  return new (Context) ACCWriteClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCUpdateClause(SourceLocation StartLoc,
                                         SourceLocation EndLoc) {
  return new (Context) ACCUpdateClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCCaptureClause(SourceLocation StartLoc,
                                          SourceLocation EndLoc) {
  return new (Context) ACCCaptureClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCSeqCstClause(SourceLocation StartLoc,
                                         SourceLocation EndLoc) {
  return new (Context) ACCSeqCstClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCThreadsClause(SourceLocation StartLoc,
                                          SourceLocation EndLoc) {
  return new (Context) ACCThreadsClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCSIMDClause(SourceLocation StartLoc,
                                       SourceLocation EndLoc) {
  return new (Context) ACCSIMDClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCNogroupClause(SourceLocation StartLoc,
                                          SourceLocation EndLoc) {
  return new (Context) ACCNogroupClause(StartLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCVarListClause(
    OpenACCClauseKind Kind, ArrayRef<Expr *> VarList, Expr *TailExpr,
    SourceLocation StartLoc, SourceLocation LParenLoc, SourceLocation ColonLoc,
    SourceLocation EndLoc, CXXScopeSpec &ReductionIdScopeSpec,
    const DeclarationNameInfo &ReductionId, OpenACCDependClauseKind DepKind,
    OpenACCLinearClauseKind LinKind, OpenACCMapClauseKind MapTypeModifier,
    OpenACCMapClauseKind MapType, bool IsMapTypeImplicit,
    SourceLocation DepLinMapLoc) {
  ACCClause *Res = nullptr;
  switch (Kind) {
  case ACCC_private:
    Res = ActOnOpenACCPrivateClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_firstprivate:
    Res = ActOnOpenACCFirstprivateClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_lastprivate:
    Res = ActOnOpenACCLastprivateClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_shared:
    Res = ActOnOpenACCSharedClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_reduction:
    Res = ActOnOpenACCReductionClause(VarList, StartLoc, LParenLoc, ColonLoc,
                                     EndLoc, ReductionIdScopeSpec, ReductionId);
    break;
  case ACCC_task_reduction:
    Res = ActOnOpenACCTaskReductionClause(VarList, StartLoc, LParenLoc, ColonLoc,
                                         EndLoc, ReductionIdScopeSpec,
                                         ReductionId);
    break;
  case ACCC_in_reduction:
    Res =
        ActOnOpenACCInReductionClause(VarList, StartLoc, LParenLoc, ColonLoc,
                                     EndLoc, ReductionIdScopeSpec, ReductionId);
    break;
  case ACCC_linear:
    Res = ActOnOpenACCLinearClause(VarList, TailExpr, StartLoc, LParenLoc,
                                  LinKind, DepLinMapLoc, ColonLoc, EndLoc);
    break;
  case ACCC_aligned:
    Res = ActOnOpenACCAlignedClause(VarList, TailExpr, StartLoc, LParenLoc,
                                   ColonLoc, EndLoc);
    break;
  case ACCC_copyin:
    Res = ActOnOpenACCCopyinClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_copyprivate:
    Res = ActOnOpenACCCopyprivateClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_flush:
    Res = ActOnOpenACCFlushClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_depend:
    Res = ActOnOpenACCDependClause(DepKind, DepLinMapLoc, ColonLoc, VarList,
                                  StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_map:
    Res = ActOnOpenACCMapClause(MapTypeModifier, MapType, IsMapTypeImplicit,
                               DepLinMapLoc, ColonLoc, VarList, StartLoc,
                               LParenLoc, EndLoc);
    break;
  case ACCC_to:
    Res = ActOnOpenACCToClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_from:
    Res = ActOnOpenACCFromClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_use_device_ptr:
    Res = ActOnOpenACCUseDevicePtrClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_is_device_ptr:
    Res = ActOnOpenACCIsDevicePtrClause(VarList, StartLoc, LParenLoc, EndLoc);
    break;
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_schedule:
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_threadprivate:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_simd:
  case ACCC_num_teams:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_dist_schedule:
  case ACCC_defaultmap:
  case ACCC_unknown:
  case ACCC_uniform:
    llvm_unreachable("Clause is not allowed.");
  }
  return Res;
}

ExprResult Sema::getOpenACCCapturedExpr(VarDecl *Capture, ExprValueKind VK,
                                       ExprObjectKind OK, SourceLocation Loc) {
  ExprResult Res = BuildDeclRefExpr(
      Capture, Capture->getType().getNonReferenceType(), VK_LValue, Loc);
  if (!Res.isUsable())
    return ExprError();
  if (OK == OK_Ordinary && !getLangOpts().CPlusPlus) {
    Res = CreateBuiltinUnaryOp(Loc, UO_Deref, Res.get());
    if (!Res.isUsable())
      return ExprError();
  }
  if (VK != VK_LValue && Res.get()->isGLValue()) {
    Res = DefaultLvalueConversion(Res.get());
    if (!Res.isUsable())
      return ExprError();
  }
  return Res;
}

static std::pair<ValueDecl *, bool>
getPrivateItem(Sema &S, Expr *&RefExpr, SourceLocation &ELoc,
               SourceRange &ERange, bool AllowArraySection = false) {
  if (RefExpr->isTypeDependent() || RefExpr->isValueDependent() ||
      RefExpr->containsUnexpandedParameterPack())
    return std::make_pair(nullptr, true);

  // OpenACC [3.1, C/C++]
  //  A list item is a variable name.
  // OpenACC  [2.9.3.3, Restrictions, p.1]
  //  A variable that is part of another variable (as an array or
  //  structure element) cannot appear in a private clause.
  RefExpr = RefExpr->IgnoreParens();
  enum {
    NoArrayExpr = -1,
    ArraySubscript = 0,
    ACCArraySection = 1
  } IsArrayExpr = NoArrayExpr;
  if (AllowArraySection) {
    if (auto *ASE = dyn_cast_or_null<ArraySubscriptExpr>(RefExpr)) {
      auto *Base = ASE->getBase()->IgnoreParenImpCasts();
      while (auto *TempASE = dyn_cast<ArraySubscriptExpr>(Base))
        Base = TempASE->getBase()->IgnoreParenImpCasts();
      RefExpr = Base;
      IsArrayExpr = ArraySubscript;
    } else if (auto *OASE = dyn_cast_or_null<ACCArraySectionExpr>(RefExpr)) {
      auto *Base = OASE->getBase()->IgnoreParenImpCasts();
      while (auto *TempOASE = dyn_cast<ACCArraySectionExpr>(Base))
        Base = TempOASE->getBase()->IgnoreParenImpCasts();
      while (auto *TempASE = dyn_cast<ArraySubscriptExpr>(Base))
        Base = TempASE->getBase()->IgnoreParenImpCasts();
      RefExpr = Base;
      IsArrayExpr = ACCArraySection;
    }
  }
  ELoc = RefExpr->getExprLoc();
  ERange = RefExpr->getSourceRange();
  RefExpr = RefExpr->IgnoreParenImpCasts();
  auto *DE = dyn_cast_or_null<DeclRefExpr>(RefExpr);
  auto *ME = dyn_cast_or_null<MemberExpr>(RefExpr);
  if ((!DE || !isa<VarDecl>(DE->getDecl())) &&
      (S.getCurrentThisType().isNull() || !ME ||
       !isa<CXXThisExpr>(ME->getBase()->IgnoreParenImpCasts()) ||
       !isa<FieldDecl>(ME->getMemberDecl()))) {
    if (IsArrayExpr != NoArrayExpr)
      S.Diag(ELoc, diag::err_acc_expected_base_var_name) << IsArrayExpr
                                                         << ERange;
    else {
      S.Diag(ELoc,
             AllowArraySection
                 ? diag::err_acc_expected_var_name_member_expr_or_array_item
                 : diag::err_acc_expected_var_name_member_expr)
          << (S.getCurrentThisType().isNull() ? 0 : 1) << ERange;
    }
    return std::make_pair(nullptr, false);
  }
  return std::make_pair(
      getCanonicalDecl(DE ? DE->getDecl() : ME->getMemberDecl()), false);
}

ACCClause *Sema::ActOnOpenACCPrivateClause(ArrayRef<Expr *> VarList,
                                          SourceLocation StartLoc,
                                          SourceLocation LParenLoc,
                                          SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> PrivateCopies;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC private clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      PrivateCopies.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.9.3.3, Restrictions, C/C++, p.3]
    //  A variable that appears in a private clause must not have an incomplete
    //  type or a reference type.
    if (RequireCompleteType(ELoc, Type, diag::err_acc_private_incomplete_type))
      continue;
    Type = Type.getNonReferenceType();

    // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct]
    //  Variables with the predetermined data-sharing attributes may not be
    //  listed in data-sharing attributes clauses, except for the cases
    //  listed below. For these exceptions only, listing a predetermined
    //  variable in a data-sharing attribute clause is allowed and overrides
    //  the variable's predetermined data-sharing attributes.
    DSAStackTy::DSAVarData DVar = DSAStack->getTopDSA(D, false);
    if (DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_private) {
      Diag(ELoc, diag::err_acc_wrong_dsa) << getOpenACCClauseName(DVar.CKind)
                                          << getOpenACCClauseName(ACCC_private);
      ReportOriginalDSA(*this, DSAStack, D, DVar);
      continue;
    }

    auto CurrDir = DSAStack->getCurrentDirective();
    // Variably modified types are not supported for tasks.
    if (!Type->isAnyPointerType() && Type->isVariablyModifiedType() &&
        isOpenACCTaskingDirective(CurrDir)) {
      Diag(ELoc, diag::err_acc_variably_modified_type_not_supported)
          << getOpenACCClauseName(ACCC_private) << Type
          << getOpenACCDirectiveName(CurrDir);
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
      continue;
    }

    // OpenACC 4.5 [2.15.5.1, Restrictions, p.3]
    // A list item cannot appear in both a map clause and a data-sharing
    // attribute clause on the same construct
    if (CurrDir == ACCD_target || CurrDir == ACCD_target_parallel ||
        CurrDir == ACCD_target_teams ||
        CurrDir == ACCD_target_teams_distribute ||
        CurrDir == ACCD_target_teams_distribute_parallel_for ||
        CurrDir == ACCD_target_teams_distribute_parallel_for_simd ||
        CurrDir == ACCD_target_teams_distribute_simd ||
        CurrDir == ACCD_target_parallel_for_simd ||
        CurrDir == ACCD_target_parallel_for) {
      OpenACCClauseKind ConflictKind;
      if (DSAStack->checkMappableExprComponentListsForDecl(
              VD, /*CurrentRegionOnly=*/true,
              [&](ACCClauseMappableExprCommon::MappableExprComponentListRef,
                  OpenACCClauseKind WhereFoundClauseKind) -> bool {
                ConflictKind = WhereFoundClauseKind;
                return true;
              })) {
        Diag(ELoc, diag::err_acc_variable_in_given_clause_and_dsa)
            << getOpenACCClauseName(ACCC_private)
            << getOpenACCClauseName(ConflictKind)
            << getOpenACCDirectiveName(CurrDir);
        ReportOriginalDSA(*this, DSAStack, D, DVar);
        continue;
      }
    }

    // OpenACC [2.9.3.3, Restrictions, C/C++, p.1]
    //  A variable of class type (or array thereof) that appears in a private
    //  clause requires an accessible, unambiguous default constructor for the
    //  class type.
    // Generate helper private variable and initialize it with the default
    // value. The address of the original variable is replaced by the address of
    // the new private variable in CodeGen. This new variable is not added to
    // IdResolver, so the code in the OpenACC region uses original variable for
    // proper diagnostics.
    Type = Type.getUnqualifiedType();
    auto VDPrivate = buildVarDecl(*this, ELoc, Type, D->getName(),
                                  D->hasAttrs() ? &D->getAttrs() : nullptr);
    ActOnUninitializedDecl(VDPrivate);
    if (VDPrivate->isInvalidDecl())
      continue;
    auto VDPrivateRefExpr = buildDeclRefExpr(
        *this, VDPrivate, RefExpr->getType().getUnqualifiedType(), ELoc);

    DeclRefExpr *Ref = nullptr;
    if (!VD && !CurContext->isDependentContext())
      Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/false);
    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_private, Ref);
    Vars.push_back((VD || CurContext->isDependentContext())
                       ? RefExpr->IgnoreParens()
                       : Ref);
    PrivateCopies.push_back(VDPrivateRefExpr);
  }

  if (Vars.empty())
    return nullptr;

  return ACCPrivateClause::Create(Context, StartLoc, LParenLoc, EndLoc, Vars,
                                  PrivateCopies);
}

namespace {
class DiagsUninitializedSeveretyRAII {
private:
  DiagnosticsEngine &Diags;
  SourceLocation SavedLoc;
  bool IsIgnored;

public:
  DiagsUninitializedSeveretyRAII(DiagnosticsEngine &Diags, SourceLocation Loc,
                                 bool IsIgnored)
      : Diags(Diags), SavedLoc(Loc), IsIgnored(IsIgnored) {
    if (!IsIgnored) {
      Diags.setSeverity(/*Diag*/ diag::warn_uninit_self_reference_in_init,
                        /*Map*/ diag::Severity::Ignored, Loc);
    }
  }
  ~DiagsUninitializedSeveretyRAII() {
    if (!IsIgnored)
      Diags.popMappings(SavedLoc);
  }
};
}

ACCClause *Sema::ActOnOpenACCFirstprivateClause(ArrayRef<Expr *> VarList,
                                               SourceLocation StartLoc,
                                               SourceLocation LParenLoc,
                                               SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> PrivateCopies;
  SmallVector<Expr *, 8> Inits;
  SmallVector<Decl *, 4> ExprCaptures;
  bool IsImplicitClause =
      StartLoc.isInvalid() && LParenLoc.isInvalid() && EndLoc.isInvalid();
  auto ImplicitClauseLoc = DSAStack->getConstructLoc();

  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC firstprivate clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      PrivateCopies.push_back(nullptr);
      Inits.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    ELoc = IsImplicitClause ? ImplicitClauseLoc : ELoc;
    QualType Type = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.9.3.3, Restrictions, C/C++, p.3]
    //  A variable that appears in a private clause must not have an incomplete
    //  type or a reference type.
    if (RequireCompleteType(ELoc, Type,
                            diag::err_acc_firstprivate_incomplete_type))
      continue;
    Type = Type.getNonReferenceType();

    // OpenACC [2.9.3.4, Restrictions, C/C++, p.1]
    //  A variable of class type (or array thereof) that appears in a private
    //  clause requires an accessible, unambiguous copy constructor for the
    //  class type.
    auto ElemType = Context.getBaseElementType(Type).getNonReferenceType();

    // If an implicit firstprivate variable found it was checked already.
    DSAStackTy::DSAVarData TopDVar;
    if (!IsImplicitClause) {
      DSAStackTy::DSAVarData DVar = DSAStack->getTopDSA(D, false);
      TopDVar = DVar;
      OpenACCDirectiveKind CurrDir = DSAStack->getCurrentDirective();
      bool IsConstant = ElemType.isConstant(Context);
      // OpenACC [2.4.13, Data-sharing Attribute Clauses]
      //  A list item that specifies a given variable may not appear in more
      // than one clause on the same directive, except that a variable may be
      //  specified in both firstprivate and lastprivate clauses.
      // OpenACC 4.5 [2.10.8, Distribute Construct, p.3]
      // A list item may appear in a firstprivate or lastprivate clause but not
      // both.
      if (DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_firstprivate &&
          (isOpenACCDistributeDirective(CurrDir) ||
           DVar.CKind != ACCC_lastprivate) &&
          DVar.RefExpr) {
        Diag(ELoc, diag::err_acc_wrong_dsa)
            << getOpenACCClauseName(DVar.CKind)
            << getOpenACCClauseName(ACCC_firstprivate);
        ReportOriginalDSA(*this, DSAStack, D, DVar);
        continue;
      }

      // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
      // in a Construct]
      //  Variables with the predetermined data-sharing attributes may not be
      //  listed in data-sharing attributes clauses, except for the cases
      //  listed below. For these exceptions only, listing a predetermined
      //  variable in a data-sharing attribute clause is allowed and overrides
      //  the variable's predetermined data-sharing attributes.
      // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
      // in a Construct, C/C++, p.2]
      //  Variables with const-qualified type having no mutable member may be
      //  listed in a firstprivate clause, even if they are static data members.
      if (!(IsConstant || (VD && VD->isStaticDataMember())) && !DVar.RefExpr &&
          DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_shared) {
        Diag(ELoc, diag::err_acc_wrong_dsa)
            << getOpenACCClauseName(DVar.CKind)
            << getOpenACCClauseName(ACCC_firstprivate);
        ReportOriginalDSA(*this, DSAStack, D, DVar);
        continue;
      }

      // OpenACC [2.9.3.4, Restrictions, p.2]
      //  A list item that is private within a parallel region must not appear
      //  in a firstprivate clause on a worksharing construct if any of the
      //  worksharing regions arising from the worksharing construct ever bind
      //  to any of the parallel regions arising from the parallel construct.
      // OpenACC 4.5 [2.15.3.4, Restrictions, p.3]
      // A list item that is private within a teams region must not appear in a
      // firstprivate clause on a distribute construct if any of the distribute
      // regions arising from the distribute construct ever bind to any of the
      // teams regions arising from the teams construct.
      // OpenACC 4.5 [2.15.3.4, Restrictions, p.3]
      // A list item that appears in a reduction clause of a teams construct
      // must not appear in a firstprivate clause on a distribute construct if
      // any of the distribute regions arising from the distribute construct
      // ever bind to any of the teams regions arising from the teams construct.
      if ((isOpenACCWorksharingDirective(CurrDir) ||
           isOpenACCDistributeDirective(CurrDir)) &&
          !isOpenACCParallelDirective(CurrDir) &&
          !isOpenACCTeamsDirective(CurrDir)) {
        DVar = DSAStack->getImplicitDSA(D, true);
        if (DVar.CKind != ACCC_shared &&
            (isOpenACCParallelDirective(DVar.DKind) ||
             isOpenACCTeamsDirective(DVar.DKind) ||
             DVar.DKind == ACCD_unknown)) {
          Diag(ELoc, diag::err_acc_required_access)
              << getOpenACCClauseName(ACCC_firstprivate)
              << getOpenACCClauseName(ACCC_shared);
          ReportOriginalDSA(*this, DSAStack, D, DVar);
          continue;
        }
      }
      // OpenACC [2.9.3.4, Restrictions, p.3]
      //  A list item that appears in a reduction clause of a parallel construct
      //  must not appear in a firstprivate clause on a worksharing or task
      //  construct if any of the worksharing or task regions arising from the
      //  worksharing or task construct ever bind to any of the parallel regions
      //  arising from the parallel construct.
      // OpenACC [2.9.3.4, Restrictions, p.4]
      //  A list item that appears in a reduction clause in worksharing
      //  construct must not appear in a firstprivate clause in a task construct
      //  encountered during execution of any of the worksharing regions arising
      //  from the worksharing construct.
      if (isOpenACCTaskingDirective(CurrDir)) {
        DVar = DSAStack->hasInnermostDSA(
            D, [](OpenACCClauseKind C) -> bool { return C == ACCC_reduction; },
            [](OpenACCDirectiveKind K) -> bool {
              return isOpenACCParallelDirective(K) ||
                     isOpenACCWorksharingDirective(K) ||
                     isOpenACCTeamsDirective(K);
            },
            /*FromParent=*/true);
        if (DVar.CKind == ACCC_reduction &&
            (isOpenACCParallelDirective(DVar.DKind) ||
             isOpenACCWorksharingDirective(DVar.DKind) ||
             isOpenACCTeamsDirective(DVar.DKind))) {
          Diag(ELoc, diag::err_acc_parallel_reduction_in_task_firstprivate)
              << getOpenACCDirectiveName(DVar.DKind);
          ReportOriginalDSA(*this, DSAStack, D, DVar);
          continue;
        }
      }

      // OpenACC 4.5 [2.15.5.1, Restrictions, p.3]
      // A list item cannot appear in both a map clause and a data-sharing
      // attribute clause on the same construct
      if (isOpenACCTargetExecutionDirective(CurrDir)) {
        OpenACCClauseKind ConflictKind;
        if (DSAStack->checkMappableExprComponentListsForDecl(
                VD, /*CurrentRegionOnly=*/true,
                [&](ACCClauseMappableExprCommon::MappableExprComponentListRef,
                    OpenACCClauseKind WhereFoundClauseKind) -> bool {
                  ConflictKind = WhereFoundClauseKind;
                  return true;
                })) {
          Diag(ELoc, diag::err_acc_variable_in_given_clause_and_dsa)
              << getOpenACCClauseName(ACCC_firstprivate)
              << getOpenACCClauseName(ConflictKind)
              << getOpenACCDirectiveName(DSAStack->getCurrentDirective());
          ReportOriginalDSA(*this, DSAStack, D, DVar);
          continue;
        }
      }
    }

    // Variably modified types are not supported for tasks.
    if (!Type->isAnyPointerType() && Type->isVariablyModifiedType() &&
        isOpenACCTaskingDirective(DSAStack->getCurrentDirective())) {
      Diag(ELoc, diag::err_acc_variably_modified_type_not_supported)
          << getOpenACCClauseName(ACCC_firstprivate) << Type
          << getOpenACCDirectiveName(DSAStack->getCurrentDirective());
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
      continue;
    }

    Type = Type.getUnqualifiedType();
    auto VDPrivate = buildVarDecl(*this, ELoc, Type, D->getName(),
                                  D->hasAttrs() ? &D->getAttrs() : nullptr);
    // Generate helper private variable and initialize it with the value of the
    // original variable. The address of the original variable is replaced by
    // the address of the new private variable in the CodeGen. This new variable
    // is not added to IdResolver, so the code in the OpenACC region uses
    // original variable for proper diagnostics and variable capturing.
    Expr *VDInitRefExpr = nullptr;
    // For arrays generate initializer for single element and replace it by the
    // original array element in CodeGen.
    if (Type->isArrayType()) {
      auto VDInit =
          buildVarDecl(*this, RefExpr->getExprLoc(), ElemType, D->getName());
      VDInitRefExpr = buildDeclRefExpr(*this, VDInit, ElemType, ELoc);
      auto Init = DefaultLvalueConversion(VDInitRefExpr).get();
      ElemType = ElemType.getUnqualifiedType();
      auto *VDInitTemp = buildVarDecl(*this, RefExpr->getExprLoc(), ElemType,
                                      ".firstprivate.temp");
      InitializedEntity Entity =
          InitializedEntity::InitializeVariable(VDInitTemp);
      InitializationKind Kind = InitializationKind::CreateCopy(ELoc, ELoc);

      InitializationSequence InitSeq(*this, Entity, Kind, Init);
      ExprResult Result = InitSeq.Perform(*this, Entity, Kind, Init);
      if (Result.isInvalid())
        VDPrivate->setInvalidDecl();
      else
        VDPrivate->setInit(Result.getAs<Expr>());
      // Remove temp variable declaration.
      Context.Deallocate(VDInitTemp);
    } else {
      auto *VDInit = buildVarDecl(*this, RefExpr->getExprLoc(), Type,
                                  ".firstprivate.temp");
      VDInitRefExpr = buildDeclRefExpr(*this, VDInit, RefExpr->getType(),
                                       RefExpr->getExprLoc());
      AddInitializerToDecl(VDPrivate,
                           DefaultLvalueConversion(VDInitRefExpr).get(),
                           /*DirectInit=*/false);
    }
    if (VDPrivate->isInvalidDecl()) {
      if (IsImplicitClause) {
        Diag(RefExpr->getExprLoc(),
             diag::note_acc_task_predetermined_firstprivate_here);
      }
      continue;
    }
    CurContext->addDecl(VDPrivate);
    auto VDPrivateRefExpr = buildDeclRefExpr(
        *this, VDPrivate, RefExpr->getType().getUnqualifiedType(),
        RefExpr->getExprLoc());
    DeclRefExpr *Ref = nullptr;
    if (!VD && !CurContext->isDependentContext()) {
      if (TopDVar.CKind == ACCC_lastprivate)
        Ref = TopDVar.PrivateCopy;
      else {
        Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/true);
        if (!IsOpenACCCapturedDecl(D))
          ExprCaptures.push_back(Ref->getDecl());
      }
    }
    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_firstprivate, Ref);
    Vars.push_back((VD || CurContext->isDependentContext())
                       ? RefExpr->IgnoreParens()
                       : Ref);
    PrivateCopies.push_back(VDPrivateRefExpr);
    Inits.push_back(VDInitRefExpr);
  }

  if (Vars.empty())
    return nullptr;

  return ACCFirstprivateClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                                       Vars, PrivateCopies, Inits,
                                       buildPreInits(Context, ExprCaptures));
}

ACCClause *Sema::ActOnOpenACCLastprivateClause(ArrayRef<Expr *> VarList,
                                              SourceLocation StartLoc,
                                              SourceLocation LParenLoc,
                                              SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> SrcExprs;
  SmallVector<Expr *, 8> DstExprs;
  SmallVector<Expr *, 8> AssignmentOps;
  SmallVector<Decl *, 4> ExprCaptures;
  SmallVector<Expr *, 4> ExprPostUpdates;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC lastprivate clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      SrcExprs.push_back(nullptr);
      DstExprs.push_back(nullptr);
      AssignmentOps.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.14.3.5, Restrictions, C/C++, p.2]
    //  A variable that appears in a lastprivate clause must not have an
    //  incomplete type or a reference type.
    if (RequireCompleteType(ELoc, Type,
                            diag::err_acc_lastprivate_incomplete_type))
      continue;
    Type = Type.getNonReferenceType();

    OpenACCDirectiveKind CurrDir = DSAStack->getCurrentDirective();
    // OpenACC [2.14.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct]
    //  Variables with the predetermined data-sharing attributes may not be
    //  listed in data-sharing attributes clauses, except for the cases
    //  listed below.
    // OpenACC 4.5 [2.10.8, Distribute Construct, p.3]
    // A list item may appear in a firstprivate or lastprivate clause but not
    // both.
    DSAStackTy::DSAVarData DVar = DSAStack->getTopDSA(D, false);
    if (DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_lastprivate &&
        (isOpenACCDistributeDirective(CurrDir) ||
         DVar.CKind != ACCC_firstprivate) &&
        (DVar.CKind != ACCC_private || DVar.RefExpr != nullptr)) {
      Diag(ELoc, diag::err_acc_wrong_dsa)
          << getOpenACCClauseName(DVar.CKind)
          << getOpenACCClauseName(ACCC_lastprivate);
      ReportOriginalDSA(*this, DSAStack, D, DVar);
      continue;
    }

    // OpenACC [2.14.3.5, Restrictions, p.2]
    // A list item that is private within a parallel region, or that appears in
    // the reduction clause of a parallel construct, must not appear in a
    // lastprivate clause on a worksharing construct if any of the corresponding
    // worksharing regions ever binds to any of the corresponding parallel
    // regions.
    DSAStackTy::DSAVarData TopDVar = DVar;
    if (isOpenACCWorksharingDirective(CurrDir) &&
        !isOpenACCParallelDirective(CurrDir) &&
        !isOpenACCTeamsDirective(CurrDir)) {
      DVar = DSAStack->getImplicitDSA(D, true);
      if (DVar.CKind != ACCC_shared) {
        Diag(ELoc, diag::err_acc_required_access)
            << getOpenACCClauseName(ACCC_lastprivate)
            << getOpenACCClauseName(ACCC_shared);
        ReportOriginalDSA(*this, DSAStack, D, DVar);
        continue;
      }
    }

    // OpenACC [2.14.3.5, Restrictions, C++, p.1,2]
    //  A variable of class type (or array thereof) that appears in a
    //  lastprivate clause requires an accessible, unambiguous default
    //  constructor for the class type, unless the list item is also specified
    //  in a firstprivate clause.
    //  A variable of class type (or array thereof) that appears in a
    //  lastprivate clause requires an accessible, unambiguous copy assignment
    //  operator for the class type.
    Type = Context.getBaseElementType(Type).getNonReferenceType();
    auto *SrcVD = buildVarDecl(*this, ERange.getBegin(),
                               Type.getUnqualifiedType(), ".lastprivate.src",
                               D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *PseudoSrcExpr =
        buildDeclRefExpr(*this, SrcVD, Type.getUnqualifiedType(), ELoc);
    auto *DstVD =
        buildVarDecl(*this, ERange.getBegin(), Type, ".lastprivate.dst",
                     D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *PseudoDstExpr = buildDeclRefExpr(*this, DstVD, Type, ELoc);
    // For arrays generate assignment operation for single element and replace
    // it by the original array element in CodeGen.
    auto AssignmentOp = BuildBinOp(/*S=*/nullptr, ELoc, BO_Assign,
                                   PseudoDstExpr, PseudoSrcExpr);
    if (AssignmentOp.isInvalid())
      continue;
    AssignmentOp = ActOnFinishFullExpr(AssignmentOp.get(), ELoc,
                                       /*DiscardedValue=*/true);
    if (AssignmentOp.isInvalid())
      continue;

    DeclRefExpr *Ref = nullptr;
    if (!VD && !CurContext->isDependentContext()) {
      if (TopDVar.CKind == ACCC_firstprivate)
        Ref = TopDVar.PrivateCopy;
      else {
        Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/false);
        if (!IsOpenACCCapturedDecl(D))
          ExprCaptures.push_back(Ref->getDecl());
      }
      if (TopDVar.CKind == ACCC_firstprivate ||
          (!IsOpenACCCapturedDecl(D) &&
           Ref->getDecl()->hasAttr<ACCCaptureNoInitAttr>())) {
        ExprResult RefRes = DefaultLvalueConversion(Ref);
        if (!RefRes.isUsable())
          continue;
        ExprResult PostUpdateRes =
            BuildBinOp(DSAStack->getCurScope(), ELoc, BO_Assign, SimpleRefExpr,
                       RefRes.get());
        if (!PostUpdateRes.isUsable())
          continue;
        ExprPostUpdates.push_back(
            IgnoredValueConversions(PostUpdateRes.get()).get());
      }
    }
    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_lastprivate, Ref);
    Vars.push_back((VD || CurContext->isDependentContext())
                       ? RefExpr->IgnoreParens()
                       : Ref);
    SrcExprs.push_back(PseudoSrcExpr);
    DstExprs.push_back(PseudoDstExpr);
    AssignmentOps.push_back(AssignmentOp.get());
  }

  if (Vars.empty())
    return nullptr;

  return ACCLastprivateClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                                      Vars, SrcExprs, DstExprs, AssignmentOps,
                                      buildPreInits(Context, ExprCaptures),
                                      buildPostUpdate(*this, ExprPostUpdates));
}

ACCClause *Sema::ActOnOpenACCSharedClause(ArrayRef<Expr *> VarList,
                                         SourceLocation StartLoc,
                                         SourceLocation LParenLoc,
                                         SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC lastprivate clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    auto *VD = dyn_cast<VarDecl>(D);
    // OpenACC [2.9.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct]
    //  Variables with the predetermined data-sharing attributes may not be
    //  listed in data-sharing attributes clauses, except for the cases
    //  listed below. For these exceptions only, listing a predetermined
    //  variable in a data-sharing attribute clause is allowed and overrides
    //  the variable's predetermined data-sharing attributes.
    DSAStackTy::DSAVarData DVar = DSAStack->getTopDSA(D, false);
    if (DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_shared &&
        DVar.RefExpr) {
      Diag(ELoc, diag::err_acc_wrong_dsa) << getOpenACCClauseName(DVar.CKind)
                                          << getOpenACCClauseName(ACCC_shared);
      ReportOriginalDSA(*this, DSAStack, D, DVar);
      continue;
    }

    DeclRefExpr *Ref = nullptr;
    if (!VD && IsOpenACCCapturedDecl(D) && !CurContext->isDependentContext())
      Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/true);
    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_shared, Ref);
    Vars.push_back((VD || !Ref || CurContext->isDependentContext())
                       ? RefExpr->IgnoreParens()
                       : Ref);
  }

  if (Vars.empty())
    return nullptr;

  return ACCSharedClause::Create(Context, StartLoc, LParenLoc, EndLoc, Vars);
}

namespace {
class DSARefChecker : public StmtVisitor<DSARefChecker, bool> {
  DSAStackTy *Stack;

public:
  bool VisitDeclRefExpr(DeclRefExpr *E) {
    if (VarDecl *VD = dyn_cast<VarDecl>(E->getDecl())) {
      DSAStackTy::DSAVarData DVar = Stack->getTopDSA(VD, false);
      if (DVar.CKind == ACCC_shared && !DVar.RefExpr)
        return false;
      if (DVar.CKind != ACCC_unknown)
        return true;
      DSAStackTy::DSAVarData DVarPrivate = Stack->hasDSA(
          VD, isOpenACCPrivate, [](OpenACCDirectiveKind) -> bool { return true; },
          /*FromParent=*/true);
      if (DVarPrivate.CKind != ACCC_unknown)
        return true;
      return false;
    }
    return false;
  }
  bool VisitStmt(Stmt *S) {
    for (auto Child : S->children()) {
      if (Child && Visit(Child))
        return true;
    }
    return false;
  }
  explicit DSARefChecker(DSAStackTy *S) : Stack(S) {}
};
} // namespace

namespace {
// Transform MemberExpression for specified FieldDecl of current class to
// DeclRefExpr to specified ACCCapturedExprDecl.
class TransformExprToCaptures : public TreeTransform<TransformExprToCaptures> {
  typedef TreeTransform<TransformExprToCaptures> BaseTransform;
  ValueDecl *Field;
  DeclRefExpr *CapturedExpr;

public:
  TransformExprToCaptures(Sema &SemaRef, ValueDecl *FieldDecl)
      : BaseTransform(SemaRef), Field(FieldDecl), CapturedExpr(nullptr) {}

  ExprResult TransformMemberExpr(MemberExpr *E) {
    if (isa<CXXThisExpr>(E->getBase()->IgnoreParenImpCasts()) &&
        E->getMemberDecl() == Field) {
      CapturedExpr = buildCapture(SemaRef, Field, E, /*WithInit=*/false);
      return CapturedExpr;
    }
    return BaseTransform::TransformMemberExpr(E);
  }
  DeclRefExpr *getCapturedExpr() { return CapturedExpr; }
};
} // namespace

template <typename T>
static T filterLookupForUDR(SmallVectorImpl<UnresolvedSet<8>> &Lookups,
                            const llvm::function_ref<T(ValueDecl *)> &Gen) {
  for (auto &Set : Lookups) {
    for (auto *D : Set) {
      if (auto Res = Gen(cast<ValueDecl>(D)))
        return Res;
    }
  }
  return T();
}

static ExprResult
buildDeclareReductionRef(Sema &SemaRef, SourceLocation Loc, SourceRange Range,
                         Scope *S, CXXScopeSpec &ReductionIdScopeSpec,
                         const DeclarationNameInfo &ReductionId, QualType Ty,
                         CXXCastPath &BasePath, Expr *UnresolvedReduction) {
  if (ReductionIdScopeSpec.isInvalid())
    return ExprError();
  SmallVector<UnresolvedSet<8>, 4> Lookups;
  if (S) {
    LookupResult Lookup(SemaRef, ReductionId, Sema::LookupACCReductionName);
    Lookup.suppressDiagnostics();
    while (S && SemaRef.LookupParsedName(Lookup, S, &ReductionIdScopeSpec)) {
      auto *D = Lookup.getRepresentativeDecl();
      do {
        S = S->getParent();
      } while (S && !S->isDeclScope(D));
      if (S)
        S = S->getParent();
      Lookups.push_back(UnresolvedSet<8>());
      Lookups.back().append(Lookup.begin(), Lookup.end());
      Lookup.clear();
    }
  } else if (auto *ULE =
                 cast_or_null<UnresolvedLookupExpr>(UnresolvedReduction)) {
    Lookups.push_back(UnresolvedSet<8>());
    Decl *PrevD = nullptr;
    for (auto *D : ULE->decls()) {
      if (D == PrevD)
        Lookups.push_back(UnresolvedSet<8>());
      else if (auto *DRD = cast<ACCDeclareReductionDecl>(D))
        Lookups.back().addDecl(DRD);
      PrevD = D;
    }
  }
  if (SemaRef.CurContext->isDependentContext() || Ty->isDependentType() ||
      Ty->isInstantiationDependentType() ||
      Ty->containsUnexpandedParameterPack() ||
      filterLookupForUDR<bool>(Lookups, [](ValueDecl *D) -> bool {
        return !D->isInvalidDecl() &&
               (D->getType()->isDependentType() ||
                D->getType()->isInstantiationDependentType() ||
                D->getType()->containsUnexpandedParameterPack());
      })) {
    UnresolvedSet<8> ResSet;
    for (auto &Set : Lookups) {
      ResSet.append(Set.begin(), Set.end());
      // The last item marks the end of all declarations at the specified scope.
      ResSet.addDecl(Set[Set.size() - 1]);
    }
    return UnresolvedLookupExpr::Create(
        SemaRef.Context, /*NamingClass=*/nullptr,
        ReductionIdScopeSpec.getWithLocInContext(SemaRef.Context), ReductionId,
        /*ADL=*/true, /*Overloaded=*/true, ResSet.begin(), ResSet.end());
  }
  if (auto *VD = filterLookupForUDR<ValueDecl *>(
          Lookups, [&SemaRef, Ty](ValueDecl *D) -> ValueDecl * {
            if (!D->isInvalidDecl() &&
                SemaRef.Context.hasSameType(D->getType(), Ty))
              return D;
            return nullptr;
          }))
    return SemaRef.BuildDeclRefExpr(VD, Ty, VK_LValue, Loc);
  if (auto *VD = filterLookupForUDR<ValueDecl *>(
          Lookups, [&SemaRef, Ty, Loc](ValueDecl *D) -> ValueDecl * {
            if (!D->isInvalidDecl() &&
                SemaRef.IsDerivedFrom(Loc, Ty, D->getType()) &&
                !Ty.isMoreQualifiedThan(D->getType()))
              return D;
            return nullptr;
          })) {
    CXXBasePaths Paths(/*FindAmbiguities=*/true, /*RecordPaths=*/true,
                       /*DetectVirtual=*/false);
    if (SemaRef.IsDerivedFrom(Loc, Ty, VD->getType(), Paths)) {
      if (!Paths.isAmbiguous(SemaRef.Context.getCanonicalType(
              VD->getType().getUnqualifiedType()))) {
        if (SemaRef.CheckBaseClassAccess(Loc, VD->getType(), Ty, Paths.front(),
                                         /*DiagID=*/0) !=
            Sema::AR_inaccessible) {
          SemaRef.BuildBasePathArray(Paths, BasePath);
          return SemaRef.BuildDeclRefExpr(VD, Ty, VK_LValue, Loc);
        }
      }
    }
  }
  if (ReductionIdScopeSpec.isSet()) {
    SemaRef.Diag(Loc, diag::err_acc_not_resolved_reduction_identifier) << Range;
    return ExprError();
  }
  return ExprEmpty();
}

namespace {
/// Data for the reduction-based clauses.
struct ReductionData {
  /// List of original reduction items.
  SmallVector<Expr *, 8> Vars;
  /// List of private copies of the reduction items.
  SmallVector<Expr *, 8> Privates;
  /// LHS expressions for the reduction_op expressions.
  SmallVector<Expr *, 8> LHSs;
  /// RHS expressions for the reduction_op expressions.
  SmallVector<Expr *, 8> RHSs;
  /// Reduction operation expression.
  SmallVector<Expr *, 8> ReductionOps;
  /// Taskgroup descriptors for the corresponding reduction items in
  /// in_reduction clauses.
  SmallVector<Expr *, 8> TaskgroupDescriptors;
  /// List of captures for clause.
  SmallVector<Decl *, 4> ExprCaptures;
  /// List of postupdate expressions.
  SmallVector<Expr *, 4> ExprPostUpdates;
  ReductionData() = delete;
  /// Reserves required memory for the reduction data.
  ReductionData(unsigned Size) {
    Vars.reserve(Size);
    Privates.reserve(Size);
    LHSs.reserve(Size);
    RHSs.reserve(Size);
    ReductionOps.reserve(Size);
    TaskgroupDescriptors.reserve(Size);
    ExprCaptures.reserve(Size);
    ExprPostUpdates.reserve(Size);
  }
  /// Stores reduction item and reduction operation only (required for dependent
  /// reduction item).
  void push(Expr *Item, Expr *ReductionOp) {
    Vars.emplace_back(Item);
    Privates.emplace_back(nullptr);
    LHSs.emplace_back(nullptr);
    RHSs.emplace_back(nullptr);
    ReductionOps.emplace_back(ReductionOp);
    TaskgroupDescriptors.emplace_back(nullptr);
  }
  /// Stores reduction data.
  void push(Expr *Item, Expr *Private, Expr *LHS, Expr *RHS, Expr *ReductionOp,
            Expr *TaskgroupDescriptor) {
    Vars.emplace_back(Item);
    Privates.emplace_back(Private);
    LHSs.emplace_back(LHS);
    RHSs.emplace_back(RHS);
    ReductionOps.emplace_back(ReductionOp);
    TaskgroupDescriptors.emplace_back(TaskgroupDescriptor);
  }
};
} // namespace

static bool CheckACCArraySectionConstantForReduction(
    ASTContext &Context, const ACCArraySectionExpr *OASE, bool &SingleElement,
    SmallVectorImpl<llvm::APSInt> &ArraySizes) {
  const Expr *Length = OASE->getLength();
  if (Length == nullptr) {
    // For array sections of the form [1:] or [:], we would need to analyze
    // the lower bound...
    if (OASE->getColonLoc().isValid())
      return false;

    // This is an array subscript which has implicit length 1!
    SingleElement = true;
    ArraySizes.push_back(llvm::APSInt::get(1));
  } else {
    llvm::APSInt ConstantLengthValue;
    if (!Length->EvaluateAsInt(ConstantLengthValue, Context))
      return false;

    SingleElement = (ConstantLengthValue.getSExtValue() == 1);
    ArraySizes.push_back(ConstantLengthValue);
  }

  // Get the base of this array section and walk up from there.
  const Expr *Base = OASE->getBase()->IgnoreParenImpCasts();

  // We require length = 1 for all array sections except the right-most to
  // guarantee that the memory region is contiguous and has no holes in it.
  while (const auto *TempOASE = dyn_cast<ACCArraySectionExpr>(Base)) {
    Length = TempOASE->getLength();
    if (Length == nullptr) {
      // For array sections of the form [1:] or [:], we would need to analyze
      // the lower bound...
      if (OASE->getColonLoc().isValid())
        return false;

      // This is an array subscript which has implicit length 1!
      ArraySizes.push_back(llvm::APSInt::get(1));
    } else {
      llvm::APSInt ConstantLengthValue;
      if (!Length->EvaluateAsInt(ConstantLengthValue, Context) ||
          ConstantLengthValue.getSExtValue() != 1)
        return false;

      ArraySizes.push_back(ConstantLengthValue);
    }
    Base = TempOASE->getBase()->IgnoreParenImpCasts();
  }

  // If we have a single element, we don't need to add the implicit lengths.
  if (!SingleElement) {
    while (const auto *TempASE = dyn_cast<ArraySubscriptExpr>(Base)) {
      // Has implicit length 1!
      ArraySizes.push_back(llvm::APSInt::get(1));
      Base = TempASE->getBase()->IgnoreParenImpCasts();
    }
  }

  // This array section can be privatized as a single value or as a constant
  // sized array.
  return true;
}

static bool ActOnACCReductionKindClause(
    Sema &S, DSAStackTy *Stack, OpenACCClauseKind ClauseKind,
    ArrayRef<Expr *> VarList, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation ColonLoc, SourceLocation EndLoc,
    CXXScopeSpec &ReductionIdScopeSpec, const DeclarationNameInfo &ReductionId,
    ArrayRef<Expr *> UnresolvedReductions, ReductionData &RD) {
  auto DN = ReductionId.getName();
  auto OOK = DN.getCXXOverloadedOperator();
  BinaryOperatorKind BOK = BO_Comma;

  ASTContext &Context = S.Context;
  // OpenACC [2.14.3.6, reduction clause]
  // C
  // reduction-identifier is either an identifier or one of the following
  // operators: +, -, *,  &, |, ^, && and ||
  // C++
  // reduction-identifier is either an id-expression or one of the following
  // operators: +, -, *, &, |, ^, && and ||
  switch (OOK) {
  case OO_Plus:
  case OO_Minus:
    BOK = BO_Add;
    break;
  case OO_Star:
    BOK = BO_Mul;
    break;
  case OO_Amp:
    BOK = BO_And;
    break;
  case OO_Pipe:
    BOK = BO_Or;
    break;
  case OO_Caret:
    BOK = BO_Xor;
    break;
  case OO_AmpAmp:
    BOK = BO_LAnd;
    break;
  case OO_PipePipe:
    BOK = BO_LOr;
    break;
  case OO_New:
  case OO_Delete:
  case OO_Array_New:
  case OO_Array_Delete:
  case OO_Slash:
  case OO_Percent:
  case OO_Tilde:
  case OO_Exclaim:
  case OO_Equal:
  case OO_Less:
  case OO_Greater:
  case OO_LessEqual:
  case OO_GreaterEqual:
  case OO_PlusEqual:
  case OO_MinusEqual:
  case OO_StarEqual:
  case OO_SlashEqual:
  case OO_PercentEqual:
  case OO_CaretEqual:
  case OO_AmpEqual:
  case OO_PipeEqual:
  case OO_LessLess:
  case OO_GreaterGreater:
  case OO_LessLessEqual:
  case OO_GreaterGreaterEqual:
  case OO_EqualEqual:
  case OO_ExclaimEqual:
  case OO_Spaceship:
  case OO_PlusPlus:
  case OO_MinusMinus:
  case OO_Comma:
  case OO_ArrowStar:
  case OO_Arrow:
  case OO_Call:
  case OO_Subscript:
  case OO_Conditional:
  case OO_Coawait:
  case NUM_OVERLOADED_OPERATORS:
    llvm_unreachable("Unexpected reduction identifier");
  case OO_None:
    if (auto *II = DN.getAsIdentifierInfo()) {
      if (II->isStr("max"))
        BOK = BO_GT;
      else if (II->isStr("min"))
        BOK = BO_LT;
    }
    break;
  }
  SourceRange ReductionIdRange;
  if (ReductionIdScopeSpec.isValid())
    ReductionIdRange.setBegin(ReductionIdScopeSpec.getBeginLoc());
  else
    ReductionIdRange.setBegin(ReductionId.getBeginLoc());
  ReductionIdRange.setEnd(ReductionId.getEndLoc());

  auto IR = UnresolvedReductions.begin(), ER = UnresolvedReductions.end();
  bool FirstIter = true;
  for (auto RefExpr : VarList) {
    assert(RefExpr && "nullptr expr in OpenACC reduction clause.");
    // OpenACC [2.1, C/C++]
    //  A list item is a variable or array section, subject to the restrictions
    //  specified in Section 2.4 on page 42 and in each of the sections
    // describing clauses and directives for which a list appears.
    // OpenACC  [2.14.3.3, Restrictions, p.1]
    //  A variable that is part of another variable (as an array or
    //  structure element) cannot appear in a private clause.
    if (!FirstIter && IR != ER)
      ++IR;
    FirstIter = false;
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(S, SimpleRefExpr, ELoc, ERange,
                              /*AllowArraySection=*/true);
    if (Res.second) {
      // Try to find 'declare reduction' corresponding construct before using
      // builtin/overloaded operators.
      QualType Type = Context.DependentTy;
      CXXCastPath BasePath;
      ExprResult DeclareReductionRef = buildDeclareReductionRef(
          S, ELoc, ERange, Stack->getCurScope(), ReductionIdScopeSpec,
          ReductionId, Type, BasePath, IR == ER ? nullptr : *IR);
      Expr *ReductionOp = nullptr;
      if (S.CurContext->isDependentContext() &&
          (DeclareReductionRef.isUnset() ||
           isa<UnresolvedLookupExpr>(DeclareReductionRef.get())))
        ReductionOp = DeclareReductionRef.get();
      // It will be analyzed later.
      RD.push(RefExpr, ReductionOp);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    Expr *TaskgroupDescriptor = nullptr;
    QualType Type;
    auto *ASE = dyn_cast<ArraySubscriptExpr>(RefExpr->IgnoreParens());
    auto *OASE = dyn_cast<ACCArraySectionExpr>(RefExpr->IgnoreParens());
    if (ASE)
      Type = ASE->getType().getNonReferenceType();
    else if (OASE) {
      auto BaseType = ACCArraySectionExpr::getBaseOriginalType(OASE->getBase());
      if (auto *ATy = BaseType->getAsArrayTypeUnsafe())
        Type = ATy->getElementType();
      else
        Type = BaseType->getPointeeType();
      Type = Type.getNonReferenceType();
    } else
      Type = Context.getBaseElementType(D->getType().getNonReferenceType());
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.9.3.3, Restrictions, C/C++, p.3]
    //  A variable that appears in a private clause must not have an incomplete
    //  type or a reference type.
    if (S.RequireCompleteType(ELoc, Type,
                              diag::err_acc_reduction_incomplete_type))
      continue;
    // OpenACC [2.14.3.6, reduction clause, Restrictions]
    // A list item that appears in a reduction clause must not be
    // const-qualified.
    if (Type.getNonReferenceType().isConstant(Context)) {
      S.Diag(ELoc, diag::err_acc_const_reduction_list_item) << ERange;
      if (!ASE && !OASE) {
        bool IsDecl = !VD || VD->isThisDeclarationADefinition(Context) ==
                                 VarDecl::DeclarationOnly;
        S.Diag(D->getLocation(),
               IsDecl ? diag::note_previous_decl : diag::note_defined_here)
            << D;
      }
      continue;
    }
    // OpenACC [2.9.3.6, Restrictions, C/C++, p.4]
    //  If a list-item is a reference type then it must bind to the same object
    //  for all threads of the team.
    if (!ASE && !OASE && VD) {
      VarDecl *VDDef = VD->getDefinition();
      if (VD->getType()->isReferenceType() && VDDef && VDDef->hasInit()) {
        DSARefChecker Check(Stack);
        if (Check.Visit(VDDef->getInit())) {
          S.Diag(ELoc, diag::err_acc_reduction_ref_type_arg)
              << getOpenACCClauseName(ClauseKind) << ERange;
          S.Diag(VDDef->getLocation(), diag::note_defined_here) << VDDef;
          continue;
        }
      }
    }

    // OpenACC [2.14.1.1, Data-sharing Attribute Rules for Variables Referenced
    // in a Construct]
    //  Variables with the predetermined data-sharing attributes may not be
    //  listed in data-sharing attributes clauses, except for the cases
    //  listed below. For these exceptions only, listing a predetermined
    //  variable in a data-sharing attribute clause is allowed and overrides
    //  the variable's predetermined data-sharing attributes.
    // OpenACC [2.14.3.6, Restrictions, p.3]
    //  Any number of reduction clauses can be specified on the directive,
    //  but a list item can appear only once in the reduction clauses for that
    //  directive.
    DSAStackTy::DSAVarData DVar;
    DVar = Stack->getTopDSA(D, false);
    if (DVar.CKind == ACCC_reduction) {
      S.Diag(ELoc, diag::err_acc_once_referenced)
          << getOpenACCClauseName(ClauseKind);
      if (DVar.RefExpr)
        S.Diag(DVar.RefExpr->getExprLoc(), diag::note_acc_referenced);
      continue;
    } else if (DVar.CKind != ACCC_unknown) {
      S.Diag(ELoc, diag::err_acc_wrong_dsa)
          << getOpenACCClauseName(DVar.CKind)
          << getOpenACCClauseName(ACCC_reduction);
      ReportOriginalDSA(S, Stack, D, DVar);
      continue;
    }

    // OpenACC [2.14.3.6, Restrictions, p.1]
    //  A list item that appears in a reduction clause of a worksharing
    //  construct must be shared in the parallel regions to which any of the
    //  worksharing regions arising from the worksharing construct bind.
    OpenACCDirectiveKind CurrDir = Stack->getCurrentDirective();
    if (isOpenACCWorksharingDirective(CurrDir) &&
        !isOpenACCParallelDirective(CurrDir) &&
        !isOpenACCTeamsDirective(CurrDir)) {
      DVar = Stack->getImplicitDSA(D, true);
      if (DVar.CKind != ACCC_shared) {
        S.Diag(ELoc, diag::err_acc_required_access)
            << getOpenACCClauseName(ACCC_reduction)
            << getOpenACCClauseName(ACCC_shared);
        ReportOriginalDSA(S, Stack, D, DVar);
        continue;
      }
    }

    // Try to find 'declare reduction' corresponding construct before using
    // builtin/overloaded operators.
    CXXCastPath BasePath;
    ExprResult DeclareReductionRef = buildDeclareReductionRef(
        S, ELoc, ERange, Stack->getCurScope(), ReductionIdScopeSpec,
        ReductionId, Type, BasePath, IR == ER ? nullptr : *IR);
    if (DeclareReductionRef.isInvalid())
      continue;
    if (S.CurContext->isDependentContext() &&
        (DeclareReductionRef.isUnset() ||
         isa<UnresolvedLookupExpr>(DeclareReductionRef.get()))) {
      RD.push(RefExpr, DeclareReductionRef.get());
      continue;
    }
    if (BOK == BO_Comma && DeclareReductionRef.isUnset()) {
      // Not allowed reduction identifier is found.
      S.Diag(ReductionId.getLocStart(),
             diag::err_acc_unknown_reduction_identifier)
          << Type << ReductionIdRange;
      continue;
    }

    // OpenACC [2.14.3.6, reduction clause, Restrictions]
    // The type of a list item that appears in a reduction clause must be valid
    // for the reduction-identifier. For a max or min reduction in C, the type
    // of the list item must be an allowed arithmetic data type: char, int,
    // float, double, or _Bool, possibly modified with long, short, signed, or
    // unsigned. For a max or min reduction in C++, the type of the list item
    // must be an allowed arithmetic data type: char, wchar_t, int, float,
    // double, or bool, possibly modified with long, short, signed, or unsigned.
    if (DeclareReductionRef.isUnset()) {
      if ((BOK == BO_GT || BOK == BO_LT) &&
          !(Type->isScalarType() ||
            (S.getLangOpts().CPlusPlus && Type->isArithmeticType()))) {
        S.Diag(ELoc, diag::err_acc_clause_not_arithmetic_type_arg)
            << getOpenACCClauseName(ClauseKind) << S.getLangOpts().CPlusPlus;
        if (!ASE && !OASE) {
          bool IsDecl = !VD || VD->isThisDeclarationADefinition(Context) ==
                                   VarDecl::DeclarationOnly;
          S.Diag(D->getLocation(),
                 IsDecl ? diag::note_previous_decl : diag::note_defined_here)
              << D;
        }
        continue;
      }
      if ((BOK == BO_OrAssign || BOK == BO_AndAssign || BOK == BO_XorAssign) &&
          !S.getLangOpts().CPlusPlus && Type->isFloatingType()) {
        S.Diag(ELoc, diag::err_acc_clause_floating_type_arg)
            << getOpenACCClauseName(ClauseKind);
        if (!ASE && !OASE) {
          bool IsDecl = !VD || VD->isThisDeclarationADefinition(Context) ==
                                   VarDecl::DeclarationOnly;
          S.Diag(D->getLocation(),
                 IsDecl ? diag::note_previous_decl : diag::note_defined_here)
              << D;
        }
        continue;
      }
    }

    Type = Type.getNonLValueExprType(Context).getUnqualifiedType();
    auto *LHSVD = buildVarDecl(S, ELoc, Type, ".reduction.lhs",
                               D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *RHSVD = buildVarDecl(S, ELoc, Type, D->getName(),
                               D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto PrivateTy = Type;

    // Try if we can determine constant lengths for all array sections and avoid
    // the VLA.
    bool ConstantLengthOASE = false;
    if (OASE) {
      bool SingleElement;
      llvm::SmallVector<llvm::APSInt, 4> ArraySizes;
      ConstantLengthOASE = CheckACCArraySectionConstantForReduction(
          Context, OASE, SingleElement, ArraySizes);

      // If we don't have a single element, we must emit a constant array type.
      if (ConstantLengthOASE && !SingleElement) {
        for (auto &Size : ArraySizes) {
          PrivateTy = Context.getConstantArrayType(
              PrivateTy, Size, ArrayType::Normal, /*IndexTypeQuals=*/0);
        }
      }
    }

    if ((OASE && !ConstantLengthOASE) ||
        (!OASE && !ASE &&
         D->getType().getNonReferenceType()->isVariablyModifiedType())) {
      if (!Context.getTargetInfo().isVLASupported() &&
          S.shouldDiagnoseTargetSupportFromOpenACC()) {
        S.Diag(ELoc, diag::err_acc_reduction_vla_unsupported) << !!OASE;
        S.Diag(ELoc, diag::note_vla_unsupported);
        continue;
      }
      // For arrays/array sections only:
      // Create pseudo array type for private copy. The size for this array will
      // be generated during codegen.
      // For array subscripts or single variables Private Ty is the same as Type
      // (type of the variable or single array element).
      PrivateTy = Context.getVariableArrayType(
          Type,
          new (Context) OpaqueValueExpr(ELoc, Context.getSizeType(), VK_RValue),
          ArrayType::Normal, /*IndexTypeQuals=*/0, SourceRange());
    } else if (!ASE && !OASE &&
               Context.getAsArrayType(D->getType().getNonReferenceType()))
      PrivateTy = D->getType().getNonReferenceType();
    // Private copy.
    auto *PrivateVD = buildVarDecl(S, ELoc, PrivateTy, D->getName(),
                                   D->hasAttrs() ? &D->getAttrs() : nullptr);
    // Add initializer for private variable.
    Expr *Init = nullptr;
    auto *LHSDRE = buildDeclRefExpr(S, LHSVD, Type, ELoc);
    auto *RHSDRE = buildDeclRefExpr(S, RHSVD, Type, ELoc);
    if (DeclareReductionRef.isUsable()) {
      auto *DRDRef = DeclareReductionRef.getAs<DeclRefExpr>();
      auto *DRD = cast<ACCDeclareReductionDecl>(DRDRef->getDecl());
      if (DRD->getInitializer()) {
        Init = DRDRef;
        RHSVD->setInit(DRDRef);
        RHSVD->setInitStyle(VarDecl::CallInit);
      }
    } else {
      switch (BOK) {
      case BO_Add:
      case BO_Xor:
      case BO_Or:
      case BO_LOr:
        // '+', '-', '^', '|', '||' reduction ops - initializer is '0'.
        if (Type->isScalarType() || Type->isAnyComplexType())
          Init = S.ActOnIntegerConstant(ELoc, /*Val=*/0).get();
        break;
      case BO_Mul:
      case BO_LAnd:
        if (Type->isScalarType() || Type->isAnyComplexType()) {
          // '*' and '&&' reduction ops - initializer is '1'.
          Init = S.ActOnIntegerConstant(ELoc, /*Val=*/1).get();
        }
        break;
      case BO_And: {
        // '&' reduction op - initializer is '~0'.
        QualType OrigType = Type;
        if (auto *ComplexTy = OrigType->getAs<ComplexType>())
          Type = ComplexTy->getElementType();
        if (Type->isRealFloatingType()) {
          llvm::APFloat InitValue =
              llvm::APFloat::getAllOnesValue(Context.getTypeSize(Type),
                                             /*isIEEE=*/true);
          Init = FloatingLiteral::Create(Context, InitValue, /*isexact=*/true,
                                         Type, ELoc);
        } else if (Type->isScalarType()) {
          auto Size = Context.getTypeSize(Type);
          QualType IntTy = Context.getIntTypeForBitwidth(Size, /*Signed=*/0);
          llvm::APInt InitValue = llvm::APInt::getAllOnesValue(Size);
          Init = IntegerLiteral::Create(Context, InitValue, IntTy, ELoc);
        }
        if (Init && OrigType->isAnyComplexType()) {
          // Init = 0xFFFF + 0xFFFFi;
          auto *Im = new (Context) ImaginaryLiteral(Init, OrigType);
          Init = S.CreateBuiltinBinOp(ELoc, BO_Add, Init, Im).get();
        }
        Type = OrigType;
        break;
      }
      case BO_LT:
      case BO_GT: {
        // 'min' reduction op - initializer is 'Largest representable number in
        // the reduction list item type'.
        // 'max' reduction op - initializer is 'Least representable number in
        // the reduction list item type'.
        if (Type->isIntegerType() || Type->isPointerType()) {
          bool IsSigned = Type->hasSignedIntegerRepresentation();
          auto Size = Context.getTypeSize(Type);
          QualType IntTy =
              Context.getIntTypeForBitwidth(Size, /*Signed=*/IsSigned);
          llvm::APInt InitValue =
              (BOK != BO_LT) ? IsSigned ? llvm::APInt::getSignedMinValue(Size)
                                        : llvm::APInt::getMinValue(Size)
                             : IsSigned ? llvm::APInt::getSignedMaxValue(Size)
                                        : llvm::APInt::getMaxValue(Size);
          Init = IntegerLiteral::Create(Context, InitValue, IntTy, ELoc);
          if (Type->isPointerType()) {
            // Cast to pointer type.
            auto CastExpr = S.BuildCStyleCastExpr(
                ELoc, Context.getTrivialTypeSourceInfo(Type, ELoc), ELoc, Init);
            if (CastExpr.isInvalid())
              continue;
            Init = CastExpr.get();
          }
        } else if (Type->isRealFloatingType()) {
          llvm::APFloat InitValue = llvm::APFloat::getLargest(
              Context.getFloatTypeSemantics(Type), BOK != BO_LT);
          Init = FloatingLiteral::Create(Context, InitValue, /*isexact=*/true,
                                         Type, ELoc);
        }
        break;
      }
      case BO_PtrMemD:
      case BO_PtrMemI:
      case BO_MulAssign:
      case BO_Div:
      case BO_Rem:
      case BO_Sub:
      case BO_Shl:
      case BO_Shr:
      case BO_LE:
      case BO_GE:
      case BO_EQ:
      case BO_NE:
      case BO_Cmp:
      case BO_AndAssign:
      case BO_XorAssign:
      case BO_OrAssign:
      case BO_Assign:
      case BO_AddAssign:
      case BO_SubAssign:
      case BO_DivAssign:
      case BO_RemAssign:
      case BO_ShlAssign:
      case BO_ShrAssign:
      case BO_Comma:
        llvm_unreachable("Unexpected reduction operation");
      }
    }
    if (Init && DeclareReductionRef.isUnset())
      S.AddInitializerToDecl(RHSVD, Init, /*DirectInit=*/false);
    else if (!Init)
      S.ActOnUninitializedDecl(RHSVD);
    if (RHSVD->isInvalidDecl())
      continue;
    if (!RHSVD->hasInit() && DeclareReductionRef.isUnset()) {
      S.Diag(ELoc, diag::err_acc_reduction_id_not_compatible)
          << Type << ReductionIdRange;
      bool IsDecl = !VD || VD->isThisDeclarationADefinition(Context) ==
                               VarDecl::DeclarationOnly;
      S.Diag(D->getLocation(),
             IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
      continue;
    }
    // Store initializer for single element in private copy. Will be used during
    // codegen.
    PrivateVD->setInit(RHSVD->getInit());
    PrivateVD->setInitStyle(RHSVD->getInitStyle());
    auto *PrivateDRE = buildDeclRefExpr(S, PrivateVD, PrivateTy, ELoc);
    ExprResult ReductionOp;
    if (DeclareReductionRef.isUsable()) {
      QualType RedTy = DeclareReductionRef.get()->getType();
      QualType PtrRedTy = Context.getPointerType(RedTy);
      ExprResult LHS = S.CreateBuiltinUnaryOp(ELoc, UO_AddrOf, LHSDRE);
      ExprResult RHS = S.CreateBuiltinUnaryOp(ELoc, UO_AddrOf, RHSDRE);
      if (!BasePath.empty()) {
        LHS = S.DefaultLvalueConversion(LHS.get());
        RHS = S.DefaultLvalueConversion(RHS.get());
        LHS = ImplicitCastExpr::Create(Context, PtrRedTy,
                                       CK_UncheckedDerivedToBase, LHS.get(),
                                       &BasePath, LHS.get()->getValueKind());
        RHS = ImplicitCastExpr::Create(Context, PtrRedTy,
                                       CK_UncheckedDerivedToBase, RHS.get(),
                                       &BasePath, RHS.get()->getValueKind());
      }
      FunctionProtoType::ExtProtoInfo EPI;
      QualType Params[] = {PtrRedTy, PtrRedTy};
      QualType FnTy = Context.getFunctionType(Context.VoidTy, Params, EPI);
      auto *OVE = new (Context) OpaqueValueExpr(
          ELoc, Context.getPointerType(FnTy), VK_RValue, OK_Ordinary,
          S.DefaultLvalueConversion(DeclareReductionRef.get()).get());
      Expr *Args[] = {LHS.get(), RHS.get()};
      ReductionOp = new (Context)
          CallExpr(Context, OVE, Args, Context.VoidTy, VK_RValue, ELoc);
    } else {
      ReductionOp = S.BuildBinOp(
          Stack->getCurScope(), ReductionId.getLocStart(), BOK, LHSDRE, RHSDRE);
      if (ReductionOp.isUsable()) {
        if (BOK != BO_LT && BOK != BO_GT) {
          ReductionOp =
              S.BuildBinOp(Stack->getCurScope(), ReductionId.getLocStart(),
                           BO_Assign, LHSDRE, ReductionOp.get());
        } else {
          auto *ConditionalOp = new (Context)
              ConditionalOperator(ReductionOp.get(), ELoc, LHSDRE, ELoc, RHSDRE,
                                  Type, VK_LValue, OK_Ordinary);
          ReductionOp =
              S.BuildBinOp(Stack->getCurScope(), ReductionId.getLocStart(),
                           BO_Assign, LHSDRE, ConditionalOp);
        }
        if (ReductionOp.isUsable())
          ReductionOp = S.ActOnFinishFullExpr(ReductionOp.get());
      }
      if (!ReductionOp.isUsable())
        continue;
    }

    // OpenACC [2.15.4.6, Restrictions, p.2]
    // A list item that appears in an in_reduction clause of a task construct
    // must appear in a task_reduction clause of a construct associated with a
    // taskgroup region that includes the participating task in its taskgroup
    // set. The construct associated with the innermost region that meets this
    // condition must specify the same reduction-identifier as the in_reduction
    // clause.
    if (ClauseKind == ACCC_in_reduction) {
      SourceRange ParentSR;
      BinaryOperatorKind ParentBOK;
      const Expr *ParentReductionOp;
      Expr *ParentBOKTD, *ParentReductionOpTD;
      DSAStackTy::DSAVarData ParentBOKDSA =
          Stack->getTopMostTaskgroupReductionData(D, ParentSR, ParentBOK,
                                                  ParentBOKTD);
      DSAStackTy::DSAVarData ParentReductionOpDSA =
          Stack->getTopMostTaskgroupReductionData(
              D, ParentSR, ParentReductionOp, ParentReductionOpTD);
      bool IsParentBOK = ParentBOKDSA.DKind != ACCD_unknown;
      bool IsParentReductionOp = ParentReductionOpDSA.DKind != ACCD_unknown;
      if (!IsParentBOK && !IsParentReductionOp) {
        S.Diag(ELoc, diag::err_acc_in_reduction_not_task_reduction);
        continue;
      }
      if ((DeclareReductionRef.isUnset() && IsParentReductionOp) ||
          (DeclareReductionRef.isUsable() && IsParentBOK) || BOK != ParentBOK ||
          IsParentReductionOp) {
        bool EmitError = true;
        if (IsParentReductionOp && DeclareReductionRef.isUsable()) {
          llvm::FoldingSetNodeID RedId, ParentRedId;
          ParentReductionOp->Profile(ParentRedId, Context, /*Canonical=*/true);
          DeclareReductionRef.get()->Profile(RedId, Context,
                                             /*Canonical=*/true);
          EmitError = RedId != ParentRedId;
        }
        if (EmitError) {
          S.Diag(ReductionId.getLocStart(),
                 diag::err_acc_reduction_identifier_mismatch)
              << ReductionIdRange << RefExpr->getSourceRange();
          S.Diag(ParentSR.getBegin(),
                 diag::note_acc_previous_reduction_identifier)
              << ParentSR
              << (IsParentBOK ? ParentBOKDSA.RefExpr
                              : ParentReductionOpDSA.RefExpr)
                     ->getSourceRange();
          continue;
        }
      }
      TaskgroupDescriptor = IsParentBOK ? ParentBOKTD : ParentReductionOpTD;
      assert(TaskgroupDescriptor && "Taskgroup descriptor must be defined.");
    }

    DeclRefExpr *Ref = nullptr;
    Expr *VarsExpr = RefExpr->IgnoreParens();
    if (!VD && !S.CurContext->isDependentContext()) {
      if (ASE || OASE) {
        TransformExprToCaptures RebuildToCapture(S, D);
        VarsExpr =
            RebuildToCapture.TransformExpr(RefExpr->IgnoreParens()).get();
        Ref = RebuildToCapture.getCapturedExpr();
      } else {
        VarsExpr = Ref = buildCapture(S, D, SimpleRefExpr, /*WithInit=*/false);
      }
      if (!S.IsOpenACCCapturedDecl(D)) {
        RD.ExprCaptures.emplace_back(Ref->getDecl());
        if (Ref->getDecl()->hasAttr<ACCCaptureNoInitAttr>()) {
          ExprResult RefRes = S.DefaultLvalueConversion(Ref);
          if (!RefRes.isUsable())
            continue;
          ExprResult PostUpdateRes =
              S.BuildBinOp(Stack->getCurScope(), ELoc, BO_Assign, SimpleRefExpr,
                           RefRes.get());
          if (!PostUpdateRes.isUsable())
            continue;
          if (isOpenACCTaskingDirective(Stack->getCurrentDirective()) ||
              Stack->getCurrentDirective() == ACCD_taskgroup) {
            S.Diag(RefExpr->getExprLoc(),
                   diag::err_acc_reduction_non_addressable_expression)
                << RefExpr->getSourceRange();
            continue;
          }
          RD.ExprPostUpdates.emplace_back(
              S.IgnoredValueConversions(PostUpdateRes.get()).get());
        }
      }
    }
    // All reduction items are still marked as reduction (to do not increase
    // code base size).
    Stack->addDSA(D, RefExpr->IgnoreParens(), ACCC_reduction, Ref);
    if (CurrDir == ACCD_taskgroup) {
      if (DeclareReductionRef.isUsable())
        Stack->addTaskgroupReductionData(D, ReductionIdRange,
                                         DeclareReductionRef.get());
      else
        Stack->addTaskgroupReductionData(D, ReductionIdRange, BOK);
    }
    RD.push(VarsExpr, PrivateDRE, LHSDRE, RHSDRE, ReductionOp.get(),
            TaskgroupDescriptor);
  }
  return RD.Vars.empty();
}

ACCClause *Sema::ActOnOpenACCReductionClause(
    ArrayRef<Expr *> VarList, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation ColonLoc, SourceLocation EndLoc,
    CXXScopeSpec &ReductionIdScopeSpec, const DeclarationNameInfo &ReductionId,
    ArrayRef<Expr *> UnresolvedReductions) {
  ReductionData RD(VarList.size());

  if (ActOnACCReductionKindClause(*this, DSAStack, ACCC_reduction, VarList,
                                  StartLoc, LParenLoc, ColonLoc, EndLoc,
                                  ReductionIdScopeSpec, ReductionId,
                                  UnresolvedReductions, RD))
    return nullptr;

  return ACCReductionClause::Create(
      Context, StartLoc, LParenLoc, ColonLoc, EndLoc, RD.Vars,
      ReductionIdScopeSpec.getWithLocInContext(Context), ReductionId,
      RD.Privates, RD.LHSs, RD.RHSs, RD.ReductionOps,
      buildPreInits(Context, RD.ExprCaptures),
      buildPostUpdate(*this, RD.ExprPostUpdates));
}

ACCClause *Sema::ActOnOpenACCTaskReductionClause(
    ArrayRef<Expr *> VarList, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation ColonLoc, SourceLocation EndLoc,
    CXXScopeSpec &ReductionIdScopeSpec, const DeclarationNameInfo &ReductionId,
    ArrayRef<Expr *> UnresolvedReductions) {
  ReductionData RD(VarList.size());

  if (ActOnACCReductionKindClause(*this, DSAStack, ACCC_task_reduction,
                                  VarList, StartLoc, LParenLoc, ColonLoc,
                                  EndLoc, ReductionIdScopeSpec, ReductionId,
                                  UnresolvedReductions, RD))
    return nullptr;

  return ACCTaskReductionClause::Create(
      Context, StartLoc, LParenLoc, ColonLoc, EndLoc, RD.Vars,
      ReductionIdScopeSpec.getWithLocInContext(Context), ReductionId,
      RD.Privates, RD.LHSs, RD.RHSs, RD.ReductionOps,
      buildPreInits(Context, RD.ExprCaptures),
      buildPostUpdate(*this, RD.ExprPostUpdates));
}

ACCClause *Sema::ActOnOpenACCInReductionClause(
    ArrayRef<Expr *> VarList, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation ColonLoc, SourceLocation EndLoc,
    CXXScopeSpec &ReductionIdScopeSpec, const DeclarationNameInfo &ReductionId,
    ArrayRef<Expr *> UnresolvedReductions) {
  ReductionData RD(VarList.size());

  if (ActOnACCReductionKindClause(*this, DSAStack, ACCC_in_reduction, VarList,
                                  StartLoc, LParenLoc, ColonLoc, EndLoc,
                                  ReductionIdScopeSpec, ReductionId,
                                  UnresolvedReductions, RD))
    return nullptr;

  return ACCInReductionClause::Create(
      Context, StartLoc, LParenLoc, ColonLoc, EndLoc, RD.Vars,
      ReductionIdScopeSpec.getWithLocInContext(Context), ReductionId,
      RD.Privates, RD.LHSs, RD.RHSs, RD.ReductionOps, RD.TaskgroupDescriptors,
      buildPreInits(Context, RD.ExprCaptures),
      buildPostUpdate(*this, RD.ExprPostUpdates));
}

bool Sema::CheckOpenACCLinearModifier(OpenACCLinearClauseKind LinKind,
                                     SourceLocation LinLoc) {
  if ((!LangOpts.CPlusPlus && LinKind != ACCC_LINEAR_val) ||
      LinKind == ACCC_LINEAR_unknown) {
    Diag(LinLoc, diag::err_acc_wrong_linear_modifier) << LangOpts.CPlusPlus;
    return true;
  }
  return false;
}

bool Sema::CheckOpenACCLinearDecl(ValueDecl *D, SourceLocation ELoc,
                                 OpenACCLinearClauseKind LinKind,
                                 QualType Type) {
  auto *VD = dyn_cast_or_null<VarDecl>(D);
  // A variable must not have an incomplete type or a reference type.
  if (RequireCompleteType(ELoc, Type, diag::err_acc_linear_incomplete_type))
    return true;
  if ((LinKind == ACCC_LINEAR_uval || LinKind == ACCC_LINEAR_ref) &&
      !Type->isReferenceType()) {
    Diag(ELoc, diag::err_acc_wrong_linear_modifier_non_reference)
        << Type << getOpenACCSimpleClauseTypeName(ACCC_linear, LinKind);
    return true;
  }
  Type = Type.getNonReferenceType();

  // A list item must not be const-qualified.
  if (Type.isConstant(Context)) {
    Diag(ELoc, diag::err_acc_const_variable)
        << getOpenACCClauseName(ACCC_linear);
    if (D) {
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
    }
    return true;
  }

  // A list item must be of integral or pointer type.
  Type = Type.getUnqualifiedType().getCanonicalType();
  const auto *Ty = Type.getTypePtrOrNull();
  if (!Ty || (!Ty->isDependentType() && !Ty->isIntegralType(Context) &&
              !Ty->isPointerType())) {
    Diag(ELoc, diag::err_acc_linear_expected_int_or_ptr) << Type;
    if (D) {
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
    }
    return true;
  }
  return false;
}

ACCClause *Sema::ActOnOpenACCLinearClause(
    ArrayRef<Expr *> VarList, Expr *Step, SourceLocation StartLoc,
    SourceLocation LParenLoc, OpenACCLinearClauseKind LinKind,
    SourceLocation LinLoc, SourceLocation ColonLoc, SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> Privates;
  SmallVector<Expr *, 8> Inits;
  SmallVector<Decl *, 4> ExprCaptures;
  SmallVector<Expr *, 4> ExprPostUpdates;
  if (CheckOpenACCLinearModifier(LinKind, LinLoc))
    LinKind = ACCC_LINEAR_val;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC linear clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange,
                              /*AllowArraySection=*/false);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      Privates.push_back(nullptr);
      Inits.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.14.3.7, linear clause]
    //  A list-item cannot appear in more than one linear clause.
    //  A list-item that appears in a linear clause cannot appear in any
    //  other data-sharing attribute clause.
    DSAStackTy::DSAVarData DVar = DSAStack->getTopDSA(D, false);
    if (DVar.RefExpr) {
      Diag(ELoc, diag::err_acc_wrong_dsa) << getOpenACCClauseName(DVar.CKind)
                                          << getOpenACCClauseName(ACCC_linear);
      ReportOriginalDSA(*this, DSAStack, D, DVar);
      continue;
    }

    if (CheckOpenACCLinearDecl(D, ELoc, LinKind, Type))
      continue;
    Type = Type.getNonReferenceType().getUnqualifiedType().getCanonicalType();

    // Build private copy of original var.
    auto *Private = buildVarDecl(*this, ELoc, Type, D->getName(),
                                 D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *PrivateRef = buildDeclRefExpr(*this, Private, Type, ELoc);
    // Build var to save initial value.
    VarDecl *Init = buildVarDecl(*this, ELoc, Type, ".linear.start");
    Expr *InitExpr;
    DeclRefExpr *Ref = nullptr;
    if (!VD && !CurContext->isDependentContext()) {
      Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/false);
      if (!IsOpenACCCapturedDecl(D)) {
        ExprCaptures.push_back(Ref->getDecl());
        if (Ref->getDecl()->hasAttr<ACCCaptureNoInitAttr>()) {
          ExprResult RefRes = DefaultLvalueConversion(Ref);
          if (!RefRes.isUsable())
            continue;
          ExprResult PostUpdateRes =
              BuildBinOp(DSAStack->getCurScope(), ELoc, BO_Assign,
                         SimpleRefExpr, RefRes.get());
          if (!PostUpdateRes.isUsable())
            continue;
          ExprPostUpdates.push_back(
              IgnoredValueConversions(PostUpdateRes.get()).get());
        }
      }
    }
    if (LinKind == ACCC_LINEAR_uval)
      InitExpr = VD ? VD->getInit() : SimpleRefExpr;
    else
      InitExpr = VD ? SimpleRefExpr : Ref;
    AddInitializerToDecl(Init, DefaultLvalueConversion(InitExpr).get(),
                         /*DirectInit=*/false);
    auto InitRef = buildDeclRefExpr(*this, Init, Type, ELoc);

    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_linear, Ref);
    Vars.push_back((VD || CurContext->isDependentContext())
                       ? RefExpr->IgnoreParens()
                       : Ref);
    Privates.push_back(PrivateRef);
    Inits.push_back(InitRef);
  }

  if (Vars.empty())
    return nullptr;

  Expr *StepExpr = Step;
  Expr *CalcStepExpr = nullptr;
  if (Step && !Step->isValueDependent() && !Step->isTypeDependent() &&
      !Step->isInstantiationDependent() &&
      !Step->containsUnexpandedParameterPack()) {
    SourceLocation StepLoc = Step->getLocStart();
    ExprResult Val = PerformOpenACCImplicitIntegerConversion(StepLoc, Step);
    if (Val.isInvalid())
      return nullptr;
    StepExpr = Val.get();

    // Build var to save the step value.
    VarDecl *SaveVar =
        buildVarDecl(*this, StepLoc, StepExpr->getType(), ".linear.step");
    ExprResult SaveRef =
        buildDeclRefExpr(*this, SaveVar, StepExpr->getType(), StepLoc);
    ExprResult CalcStep =
        BuildBinOp(CurScope, StepLoc, BO_Assign, SaveRef.get(), StepExpr);
    CalcStep = ActOnFinishFullExpr(CalcStep.get());

    // Warn about zero linear step (it would be probably better specified as
    // making corresponding variables 'const').
    llvm::APSInt Result;
    bool IsConstant = StepExpr->isIntegerConstantExpr(Result, Context);
    if (IsConstant && !Result.isNegative() && !Result.isStrictlyPositive())
      Diag(StepLoc, diag::warn_acc_linear_step_zero) << Vars[0]
                                                     << (Vars.size() > 1);
    if (!IsConstant && CalcStep.isUsable()) {
      // Calculate the step beforehand instead of doing this on each iteration.
      // (This is not used if the number of iterations may be kfold-ed).
      CalcStepExpr = CalcStep.get();
    }
  }

  return ACCLinearClause::Create(Context, StartLoc, LParenLoc, LinKind, LinLoc,
                                 ColonLoc, EndLoc, Vars, Privates, Inits,
                                 StepExpr, CalcStepExpr,
                                 buildPreInits(Context, ExprCaptures),
                                 buildPostUpdate(*this, ExprPostUpdates));
}

static bool FinishOpenACCLinearClause(ACCLinearClause &Clause, DeclRefExpr *IV,
                                     Expr *NumIterations, Sema &SemaRef,
                                     Scope *S, DSAStackTy *Stack) {
  // Walk the vars and build update/final expressions for the CodeGen.
  SmallVector<Expr *, 8> Updates;
  SmallVector<Expr *, 8> Finals;
  Expr *Step = Clause.getStep();
  Expr *CalcStep = Clause.getCalcStep();
  // OpenACC [2.14.3.7, linear clause]
  // If linear-step is not specified it is assumed to be 1.
  if (Step == nullptr)
    Step = SemaRef.ActOnIntegerConstant(SourceLocation(), 1).get();
  else if (CalcStep) {
    Step = cast<BinaryOperator>(CalcStep)->getLHS();
  }
  bool HasErrors = false;
  auto CurInit = Clause.inits().begin();
  auto CurPrivate = Clause.privates().begin();
  auto LinKind = Clause.getModifier();
  for (auto &RefExpr : Clause.varlists()) {
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(SemaRef, SimpleRefExpr, ELoc, ERange,
                              /*AllowArraySection=*/false);
    ValueDecl *D = Res.first;
    if (Res.second || !D) {
      Updates.push_back(nullptr);
      Finals.push_back(nullptr);
      HasErrors = true;
      continue;
    }
    auto &&Info = Stack->isLoopControlVariable(D);
    // OpenACC [2.15.11, distribute simd Construct]
    // A list item may not appear in a linear clause, unless it is the loop
    // iteration variable.
    if (isOpenACCDistributeDirective(Stack->getCurrentDirective()) &&
        isOpenACCSimdDirective(Stack->getCurrentDirective()) && !Info.first) {
      SemaRef.Diag(ELoc,
                   diag::err_acc_linear_distribute_var_non_loop_iteration);
      Updates.push_back(nullptr);
      Finals.push_back(nullptr);
      HasErrors = true;
      continue;
    }
    Expr *InitExpr = *CurInit;

    // Build privatized reference to the current linear var.
    auto *DE = cast<DeclRefExpr>(SimpleRefExpr);
    Expr *CapturedRef;
    if (LinKind == ACCC_LINEAR_uval)
      CapturedRef = cast<VarDecl>(DE->getDecl())->getInit();
    else
      CapturedRef =
          buildDeclRefExpr(SemaRef, cast<VarDecl>(DE->getDecl()),
                           DE->getType().getUnqualifiedType(), DE->getExprLoc(),
                           /*RefersToCapture=*/true);

    // Build update: Var = InitExpr + IV * Step
    ExprResult Update;
    if (!Info.first) {
      Update =
          BuildCounterUpdate(SemaRef, S, RefExpr->getExprLoc(), *CurPrivate,
                             InitExpr, IV, Step, /* Subtract */ false);
    } else
      Update = *CurPrivate;
    Update = SemaRef.ActOnFinishFullExpr(Update.get(), DE->getLocStart(),
                                         /*DiscardedValue=*/true);

    // Build final: Var = InitExpr + NumIterations * Step
    ExprResult Final;
    if (!Info.first) {
      Final = BuildCounterUpdate(SemaRef, S, RefExpr->getExprLoc(), CapturedRef,
                                 InitExpr, NumIterations, Step,
                                 /* Subtract */ false);
    } else
      Final = *CurPrivate;
    Final = SemaRef.ActOnFinishFullExpr(Final.get(), DE->getLocStart(),
                                        /*DiscardedValue=*/true);

    if (!Update.isUsable() || !Final.isUsable()) {
      Updates.push_back(nullptr);
      Finals.push_back(nullptr);
      HasErrors = true;
    } else {
      Updates.push_back(Update.get());
      Finals.push_back(Final.get());
    }
    ++CurInit;
    ++CurPrivate;
  }
  Clause.setUpdates(Updates);
  Clause.setFinals(Finals);
  return HasErrors;
}

ACCClause *Sema::ActOnOpenACCAlignedClause(
    ArrayRef<Expr *> VarList, Expr *Alignment, SourceLocation StartLoc,
    SourceLocation LParenLoc, SourceLocation ColonLoc, SourceLocation EndLoc) {

  SmallVector<Expr *, 8> Vars;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC linear clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange,
                              /*AllowArraySection=*/false);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType QType = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC  [2.8.1, simd construct, Restrictions]
    // The type of list items appearing in the aligned clause must be
    // array, pointer, reference to array, or reference to pointer.
    QType = QType.getNonReferenceType().getUnqualifiedType().getCanonicalType();
    const Type *Ty = QType.getTypePtrOrNull();
    if (!Ty || (!Ty->isArrayType() && !Ty->isPointerType())) {
      Diag(ELoc, diag::err_acc_aligned_expected_array_or_ptr)
          << QType << getLangOpts().CPlusPlus << ERange;
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
      continue;
    }

    // OpenACC  [2.8.1, simd construct, Restrictions]
    // A list-item cannot appear in more than one aligned clause.
    if (Expr *PrevRef = DSAStack->addUniqueAligned(D, SimpleRefExpr)) {
      Diag(ELoc, diag::err_acc_aligned_twice) << 0 << ERange;
      Diag(PrevRef->getExprLoc(), diag::note_acc_explicit_dsa)
          << getOpenACCClauseName(ACCC_aligned);
      continue;
    }

    DeclRefExpr *Ref = nullptr;
    if (!VD && IsOpenACCCapturedDecl(D))
      Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/true);
    Vars.push_back(DefaultFunctionArrayConversion(
                       (VD || !Ref) ? RefExpr->IgnoreParens() : Ref)
                       .get());
  }

  // OpenACC [2.8.1, simd construct, Description]
  // The parameter of the aligned clause, alignment, must be a constant
  // positive integer expression.
  // If no optional parameter is specified, implementation-defined default
  // alignments for SIMD instructions on the target platforms are assumed.
  if (Alignment != nullptr) {
    ExprResult AlignResult =
        VerifyPositiveIntegerConstantInClause(Alignment, ACCC_aligned);
    if (AlignResult.isInvalid())
      return nullptr;
    Alignment = AlignResult.get();
  }
  if (Vars.empty())
    return nullptr;

  return ACCAlignedClause::Create(Context, StartLoc, LParenLoc, ColonLoc,
                                  EndLoc, Vars, Alignment);
}

ACCClause *Sema::ActOnOpenACCCopyinClause(ArrayRef<Expr *> VarList,
                                         SourceLocation StartLoc,
                                         SourceLocation LParenLoc,
                                         SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> SrcExprs;
  SmallVector<Expr *, 8> DstExprs;
  SmallVector<Expr *, 8> AssignmentOps;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC copyin clause.");
    if (isa<DependentScopeDeclRefExpr>(RefExpr)) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      SrcExprs.push_back(nullptr);
      DstExprs.push_back(nullptr);
      AssignmentOps.push_back(nullptr);
      continue;
    }

    SourceLocation ELoc = RefExpr->getExprLoc();
    // OpenACC [2.1, C/C++]
    //  A list item is a variable name.
    // OpenACC  [2.14.4.1, Restrictions, p.1]
    //  A list item that appears in a copyin clause must be threadprivate.
    DeclRefExpr *DE = dyn_cast<DeclRefExpr>(RefExpr);
    if (!DE || !isa<VarDecl>(DE->getDecl())) {
      Diag(ELoc, diag::err_acc_expected_var_name_member_expr)
          << 0 << RefExpr->getSourceRange();
      continue;
    }

    Decl *D = DE->getDecl();
    VarDecl *VD = cast<VarDecl>(D);

    QualType Type = VD->getType();
    if (Type->isDependentType() || Type->isInstantiationDependentType()) {
      // It will be analyzed later.
      Vars.push_back(DE);
      SrcExprs.push_back(nullptr);
      DstExprs.push_back(nullptr);
      AssignmentOps.push_back(nullptr);
      continue;
    }

    // OpenACC [2.14.4.1, Restrictions, C/C++, p.1]
    //  A list item that appears in a copyin clause must be threadprivate.
    if (!DSAStack->isThreadPrivate(VD)) {
      Diag(ELoc, diag::err_acc_required_access)
          << getOpenACCClauseName(ACCC_copyin)
          << getOpenACCDirectiveName(ACCD_threadprivate);
      continue;
    }

    // OpenACC [2.14.4.1, Restrictions, C/C++, p.2]
    //  A variable of class type (or array thereof) that appears in a
    //  copyin clause requires an accessible, unambiguous copy assignment
    //  operator for the class type.
    auto ElemType = Context.getBaseElementType(Type).getNonReferenceType();
    auto *SrcVD =
        buildVarDecl(*this, DE->getLocStart(), ElemType.getUnqualifiedType(),
                     ".copyin.src", VD->hasAttrs() ? &VD->getAttrs() : nullptr);
    auto *PseudoSrcExpr = buildDeclRefExpr(
        *this, SrcVD, ElemType.getUnqualifiedType(), DE->getExprLoc());
    auto *DstVD =
        buildVarDecl(*this, DE->getLocStart(), ElemType, ".copyin.dst",
                     VD->hasAttrs() ? &VD->getAttrs() : nullptr);
    auto *PseudoDstExpr =
        buildDeclRefExpr(*this, DstVD, ElemType, DE->getExprLoc());
    // For arrays generate assignment operation for single element and replace
    // it by the original array element in CodeGen.
    auto AssignmentOp = BuildBinOp(/*S=*/nullptr, DE->getExprLoc(), BO_Assign,
                                   PseudoDstExpr, PseudoSrcExpr);
    if (AssignmentOp.isInvalid())
      continue;
    AssignmentOp = ActOnFinishFullExpr(AssignmentOp.get(), DE->getExprLoc(),
                                       /*DiscardedValue=*/true);
    if (AssignmentOp.isInvalid())
      continue;

    DSAStack->addDSA(VD, DE, ACCC_copyin);
    Vars.push_back(DE);
    SrcExprs.push_back(PseudoSrcExpr);
    DstExprs.push_back(PseudoDstExpr);
    AssignmentOps.push_back(AssignmentOp.get());
  }

  if (Vars.empty())
    return nullptr;

  return ACCCopyinClause::Create(Context, StartLoc, LParenLoc, EndLoc, Vars,
                                 SrcExprs, DstExprs, AssignmentOps);
}

ACCClause *Sema::ActOnOpenACCCopyprivateClause(ArrayRef<Expr *> VarList,
                                              SourceLocation StartLoc,
                                              SourceLocation LParenLoc,
                                              SourceLocation EndLoc) {
  SmallVector<Expr *, 8> Vars;
  SmallVector<Expr *, 8> SrcExprs;
  SmallVector<Expr *, 8> DstExprs;
  SmallVector<Expr *, 8> AssignmentOps;
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC linear clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange,
                              /*AllowArraySection=*/false);
    if (Res.second) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      SrcExprs.push_back(nullptr);
      DstExprs.push_back(nullptr);
      AssignmentOps.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    auto *VD = dyn_cast<VarDecl>(D);

    // OpenACC [2.14.4.2, Restrictions, p.2]
    //  A list item that appears in a copyprivate clause may not appear in a
    //  private or firstprivate clause on the single construct.
    if (!VD || !DSAStack->isThreadPrivate(VD)) {
      auto DVar = DSAStack->getTopDSA(D, false);
      if (DVar.CKind != ACCC_unknown && DVar.CKind != ACCC_copyprivate &&
          DVar.RefExpr) {
        Diag(ELoc, diag::err_acc_wrong_dsa)
            << getOpenACCClauseName(DVar.CKind)
            << getOpenACCClauseName(ACCC_copyprivate);
        ReportOriginalDSA(*this, DSAStack, D, DVar);
        continue;
      }

      // OpenACC [2.11.4.2, Restrictions, p.1]
      //  All list items that appear in a copyprivate clause must be either
      //  threadprivate or private in the enclosing context.
      if (DVar.CKind == ACCC_unknown) {
        DVar = DSAStack->getImplicitDSA(D, false);
        if (DVar.CKind == ACCC_shared) {
          Diag(ELoc, diag::err_acc_required_access)
              << getOpenACCClauseName(ACCC_copyprivate)
              << "threadprivate or private in the enclosing context";
          ReportOriginalDSA(*this, DSAStack, D, DVar);
          continue;
        }
      }
    }

    // Variably modified types are not supported.
    if (!Type->isAnyPointerType() && Type->isVariablyModifiedType()) {
      Diag(ELoc, diag::err_acc_variably_modified_type_not_supported)
          << getOpenACCClauseName(ACCC_copyprivate) << Type
          << getOpenACCDirectiveName(DSAStack->getCurrentDirective());
      bool IsDecl =
          !VD ||
          VD->isThisDeclarationADefinition(Context) == VarDecl::DeclarationOnly;
      Diag(D->getLocation(),
           IsDecl ? diag::note_previous_decl : diag::note_defined_here)
          << D;
      continue;
    }

    // OpenACC [2.14.4.1, Restrictions, C/C++, p.2]
    //  A variable of class type (or array thereof) that appears in a
    //  copyin clause requires an accessible, unambiguous copy assignment
    //  operator for the class type.
    Type = Context.getBaseElementType(Type.getNonReferenceType())
               .getUnqualifiedType();
    auto *SrcVD =
        buildVarDecl(*this, RefExpr->getLocStart(), Type, ".copyprivate.src",
                     D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *PseudoSrcExpr = buildDeclRefExpr(*this, SrcVD, Type, ELoc);
    auto *DstVD =
        buildVarDecl(*this, RefExpr->getLocStart(), Type, ".copyprivate.dst",
                     D->hasAttrs() ? &D->getAttrs() : nullptr);
    auto *PseudoDstExpr = buildDeclRefExpr(*this, DstVD, Type, ELoc);
    auto AssignmentOp = BuildBinOp(DSAStack->getCurScope(), ELoc, BO_Assign,
                                   PseudoDstExpr, PseudoSrcExpr);
    if (AssignmentOp.isInvalid())
      continue;
    AssignmentOp = ActOnFinishFullExpr(AssignmentOp.get(), ELoc,
                                       /*DiscardedValue=*/true);
    if (AssignmentOp.isInvalid())
      continue;

    // No need to mark vars as copyprivate, they are already threadprivate or
    // implicitly private.
    assert(VD || IsOpenACCCapturedDecl(D));
    Vars.push_back(
        VD ? RefExpr->IgnoreParens()
           : buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/false));
    SrcExprs.push_back(PseudoSrcExpr);
    DstExprs.push_back(PseudoDstExpr);
    AssignmentOps.push_back(AssignmentOp.get());
  }

  if (Vars.empty())
    return nullptr;

  return ACCCopyprivateClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                                      Vars, SrcExprs, DstExprs, AssignmentOps);
}

ACCClause *Sema::ActOnOpenACCFlushClause(ArrayRef<Expr *> VarList,
                                        SourceLocation StartLoc,
                                        SourceLocation LParenLoc,
                                        SourceLocation EndLoc) {
  if (VarList.empty())
    return nullptr;

  return ACCFlushClause::Create(Context, StartLoc, LParenLoc, EndLoc, VarList);
}

ACCClause *
Sema::ActOnOpenACCDependClause(OpenACCDependClauseKind DepKind,
                              SourceLocation DepLoc, SourceLocation ColonLoc,
                              ArrayRef<Expr *> VarList, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc) {
  if (DSAStack->getCurrentDirective() == ACCD_ordered &&
      DepKind != ACCC_DEPEND_source && DepKind != ACCC_DEPEND_sink) {
    Diag(DepLoc, diag::err_acc_unexpected_clause_value)
        << "'source' or 'sink'" << getOpenACCClauseName(ACCC_depend);
    return nullptr;
  }
  if (DSAStack->getCurrentDirective() != ACCD_ordered &&
      (DepKind == ACCC_DEPEND_unknown || DepKind == ACCC_DEPEND_source ||
       DepKind == ACCC_DEPEND_sink)) {
    unsigned Except[] = {ACCC_DEPEND_source, ACCC_DEPEND_sink};
    Diag(DepLoc, diag::err_acc_unexpected_clause_value)
        << getListOfPossibleValues(ACCC_depend, /*First=*/0,
                                   /*Last=*/ACCC_DEPEND_unknown, Except)
        << getOpenACCClauseName(ACCC_depend);
    return nullptr;
  }
  SmallVector<Expr *, 8> Vars;
  DSAStackTy::OperatorOffsetTy OpsOffs;
  llvm::APSInt DepCounter(/*BitWidth=*/32);
  llvm::APSInt TotalDepCount(/*BitWidth=*/32);
  if (DepKind == ACCC_DEPEND_sink) {
    if (auto *OrderedCountExpr = DSAStack->getParentOrderedRegionParam()) {
      TotalDepCount = OrderedCountExpr->EvaluateKnownConstInt(Context);
      TotalDepCount.setIsUnsigned(/*Val=*/true);
    }
  }
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC shared clause.");
    if (isa<DependentScopeDeclRefExpr>(RefExpr)) {
      // It will be analyzed later.
      Vars.push_back(RefExpr);
      continue;
    }

    SourceLocation ELoc = RefExpr->getExprLoc();
    auto *SimpleExpr = RefExpr->IgnoreParenCasts();
    if (DepKind == ACCC_DEPEND_sink) {
      if (DSAStack->getParentOrderedRegionParam() &&
          DepCounter >= TotalDepCount) {
        Diag(ELoc, diag::err_acc_depend_sink_unexpected_expr);
        continue;
      }
      ++DepCounter;
      // OpenACC  [2.13.9, Summary]
      // depend(dependence-type : vec), where dependence-type is:
      // 'sink' and where vec is the iteration vector, which has the form:
      //  x1 [+- d1], x2 [+- d2 ], . . . , xn [+- dn]
      // where n is the value specified by the ordered clause in the loop
      // directive, xi denotes the loop iteration variable of the i-th nested
      // loop associated with the loop directive, and di is a constant
      // non-negative integer.
      if (CurContext->isDependentContext()) {
        // It will be analyzed later.
        Vars.push_back(RefExpr);
        continue;
      }
      SimpleExpr = SimpleExpr->IgnoreImplicit();
      OverloadedOperatorKind OOK = OO_None;
      SourceLocation OOLoc;
      Expr *LHS = SimpleExpr;
      Expr *RHS = nullptr;
      if (auto *BO = dyn_cast<BinaryOperator>(SimpleExpr)) {
        OOK = BinaryOperator::getOverloadedOperator(BO->getOpcode());
        OOLoc = BO->getOperatorLoc();
        LHS = BO->getLHS()->IgnoreParenImpCasts();
        RHS = BO->getRHS()->IgnoreParenImpCasts();
      } else if (auto *OCE = dyn_cast<CXXOperatorCallExpr>(SimpleExpr)) {
        OOK = OCE->getOperator();
        OOLoc = OCE->getOperatorLoc();
        LHS = OCE->getArg(/*Arg=*/0)->IgnoreParenImpCasts();
        RHS = OCE->getArg(/*Arg=*/1)->IgnoreParenImpCasts();
      } else if (auto *MCE = dyn_cast<CXXMemberCallExpr>(SimpleExpr)) {
        OOK = MCE->getMethodDecl()
                  ->getNameInfo()
                  .getName()
                  .getCXXOverloadedOperator();
        OOLoc = MCE->getCallee()->getExprLoc();
        LHS = MCE->getImplicitObjectArgument()->IgnoreParenImpCasts();
        RHS = MCE->getArg(/*Arg=*/0)->IgnoreParenImpCasts();
      }
      SourceLocation ELoc;
      SourceRange ERange;
      auto Res = getPrivateItem(*this, LHS, ELoc, ERange,
                                /*AllowArraySection=*/false);
      if (Res.second) {
        // It will be analyzed later.
        Vars.push_back(RefExpr);
      }
      ValueDecl *D = Res.first;
      if (!D)
        continue;

      if (OOK != OO_Plus && OOK != OO_Minus && (RHS || OOK != OO_None)) {
        Diag(OOLoc, diag::err_acc_depend_sink_expected_plus_minus);
        continue;
      }
      if (RHS) {
        ExprResult RHSRes = VerifyPositiveIntegerConstantInClause(
            RHS, ACCC_depend, /*StrictlyPositive=*/false);
        if (RHSRes.isInvalid())
          continue;
      }
      if (!CurContext->isDependentContext() &&
          DSAStack->getParentOrderedRegionParam() &&
          DepCounter != DSAStack->isParentLoopControlVariable(D).first) {
        ValueDecl *VD =
            DSAStack->getParentLoopControlVariable(DepCounter.getZExtValue());
        if (VD) {
          Diag(ELoc, diag::err_acc_depend_sink_expected_loop_iteration)
              << 1 << VD;
        } else {
          Diag(ELoc, diag::err_acc_depend_sink_expected_loop_iteration) << 0;
        }
        continue;
      }
      OpsOffs.push_back({RHS, OOK});
    } else {
      auto *ASE = dyn_cast<ArraySubscriptExpr>(SimpleExpr);
      if (!RefExpr->IgnoreParenImpCasts()->isLValue() ||
          (ASE &&
           !ASE->getBase()->getType().getNonReferenceType()->isPointerType() &&
           !ASE->getBase()->getType().getNonReferenceType()->isArrayType())) {
        Diag(ELoc, diag::err_acc_expected_addressable_lvalue_or_array_item)
            << RefExpr->getSourceRange();
        continue;
      }
      bool Suppress = getDiagnostics().getSuppressAllDiagnostics();
      getDiagnostics().setSuppressAllDiagnostics(/*Val=*/true);
      ExprResult Res =
          CreateBuiltinUnaryOp(ELoc, UO_AddrOf, RefExpr->IgnoreParenImpCasts());
      getDiagnostics().setSuppressAllDiagnostics(Suppress);
      if (!Res.isUsable() && !isa<ACCArraySectionExpr>(SimpleExpr)) {
        Diag(ELoc, diag::err_acc_expected_addressable_lvalue_or_array_item)
            << RefExpr->getSourceRange();
        continue;
      }
    }
    Vars.push_back(RefExpr->IgnoreParenImpCasts());
  }

  if (!CurContext->isDependentContext() && DepKind == ACCC_DEPEND_sink &&
      TotalDepCount > VarList.size() &&
      DSAStack->getParentOrderedRegionParam() &&
      DSAStack->getParentLoopControlVariable(VarList.size() + 1)) {
    Diag(EndLoc, diag::err_acc_depend_sink_expected_loop_iteration)
        << 1 << DSAStack->getParentLoopControlVariable(VarList.size() + 1);
  }
  if (DepKind != ACCC_DEPEND_source && DepKind != ACCC_DEPEND_sink &&
      Vars.empty())
    return nullptr;

  auto *C = ACCDependClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                                    DepKind, DepLoc, ColonLoc, Vars);
  if ((DepKind == ACCC_DEPEND_sink || DepKind == ACCC_DEPEND_source) &&
      DSAStack->isParentOrderedRegion())
    DSAStack->addDoacrossDependClause(C, OpsOffs);
  return C;
}

ACCClause *Sema::ActOnOpenACCDeviceClause(Expr *Device, SourceLocation StartLoc,
                                         SourceLocation LParenLoc,
                                         SourceLocation EndLoc) {
  Expr *ValExpr = Device;
  Stmt *HelperValStmt = nullptr;

  // OpenACC [2.9.1, Restrictions]
  // The device expression must evaluate to a non-negative integer value.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_device,
                                 /*StrictlyPositive=*/false))
    return nullptr;

  OpenACCDirectiveKind DKind = DSAStack->getCurrentDirective();
  OpenACCDirectiveKind CaptureRegion =
      getOpenACCCaptureRegionForClause(DKind, ACCC_device);
  if (CaptureRegion != ACCD_unknown && !CurContext->isDependentContext()) {
    ValExpr = MakeFullExpr(ValExpr).get();
    llvm::MapVector<Expr *, DeclRefExpr *> Captures;
    ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
    HelperValStmt = buildPreInits(Context, Captures);
  }

  return new (Context) ACCDeviceClause(ValExpr, HelperValStmt, CaptureRegion,
                                       StartLoc, LParenLoc, EndLoc);
}

static bool CheckTypeMappable(SourceLocation SL, SourceRange SR, Sema &SemaRef,
                              DSAStackTy *Stack, QualType QTy) {
  NamedDecl *ND;
  if (QTy->isIncompleteType(&ND)) {
    SemaRef.Diag(SL, diag::err_incomplete_type) << QTy << SR;
    return false;
  }
  return true;
}

/// \brief Return true if it can be proven that the provided array expression
/// (array section or array subscript) does NOT specify the whole size of the
/// array whose base type is \a BaseQTy.
static bool CheckArrayExpressionDoesNotReferToWholeSize(Sema &SemaRef,
                                                        const Expr *E,
                                                        QualType BaseQTy) {
  auto *OASE = dyn_cast<ACCArraySectionExpr>(E);

  // If this is an array subscript, it refers to the whole size if the size of
  // the dimension is constant and equals 1. Also, an array section assumes the
  // format of an array subscript if no colon is used.
  if (isa<ArraySubscriptExpr>(E) || (OASE && OASE->getColonLoc().isInvalid())) {
    if (auto *ATy = dyn_cast<ConstantArrayType>(BaseQTy.getTypePtr()))
      return ATy->getSize().getSExtValue() != 1;
    // Size can't be evaluated statically.
    return false;
  }

  assert(OASE && "Expecting array section if not an array subscript.");
  auto *LowerBound = OASE->getLowerBound();
  auto *Length = OASE->getLength();

  // If there is a lower bound that does not evaluates to zero, we are not
  // covering the whole dimension.
  if (LowerBound) {
    llvm::APSInt ConstLowerBound;
    if (!LowerBound->EvaluateAsInt(ConstLowerBound, SemaRef.getASTContext()))
      return false; // Can't get the integer value as a constant.
    if (ConstLowerBound.getSExtValue())
      return true;
  }

  // If we don't have a length we covering the whole dimension.
  if (!Length)
    return false;

  // If the base is a pointer, we don't have a way to get the size of the
  // pointee.
  if (BaseQTy->isPointerType())
    return false;

  // We can only check if the length is the same as the size of the dimension
  // if we have a constant array.
  auto *CATy = dyn_cast<ConstantArrayType>(BaseQTy.getTypePtr());
  if (!CATy)
    return false;

  llvm::APSInt ConstLength;
  if (!Length->EvaluateAsInt(ConstLength, SemaRef.getASTContext()))
    return false; // Can't get the integer value as a constant.

  return CATy->getSize().getSExtValue() != ConstLength.getSExtValue();
}

// Return true if it can be proven that the provided array expression (array
// section or array subscript) does NOT specify a single element of the array
// whose base type is \a BaseQTy.
static bool CheckArrayExpressionDoesNotReferToUnitySize(Sema &SemaRef,
                                                        const Expr *E,
                                                        QualType BaseQTy) {
  auto *OASE = dyn_cast<ACCArraySectionExpr>(E);

  // An array subscript always refer to a single element. Also, an array section
  // assumes the format of an array subscript if no colon is used.
  if (isa<ArraySubscriptExpr>(E) || (OASE && OASE->getColonLoc().isInvalid()))
    return false;

  assert(OASE && "Expecting array section if not an array subscript.");
  auto *Length = OASE->getLength();

  // If we don't have a length we have to check if the array has unitary size
  // for this dimension. Also, we should always expect a length if the base type
  // is pointer.
  if (!Length) {
    if (auto *ATy = dyn_cast<ConstantArrayType>(BaseQTy.getTypePtr()))
      return ATy->getSize().getSExtValue() != 1;
    // We cannot assume anything.
    return false;
  }

  // Check if the length evaluates to 1.
  llvm::APSInt ConstLength;
  if (!Length->EvaluateAsInt(ConstLength, SemaRef.getASTContext()))
    return false; // Can't get the integer value as a constant.

  return ConstLength.getSExtValue() != 1;
}

// Return the expression of the base of the mappable expression or null if it
// cannot be determined and do all the necessary checks to see if the expression
// is valid as a standalone mappable expression. In the process, record all the
// components of the expression.
static Expr *CheckMapClauseExpressionBase(
    Sema &SemaRef, Expr *E,
    ACCClauseMappableExprCommon::MappableExprComponentList &CurComponents,
    OpenACCClauseKind CKind, bool NoDiagnose) {
  SourceLocation ELoc = E->getExprLoc();
  SourceRange ERange = E->getSourceRange();

  // The base of elements of list in a map clause have to be either:
  //  - a reference to variable or field.
  //  - a member expression.
  //  - an array expression.
  //
  // E.g. if we have the expression 'r.S.Arr[:12]', we want to retrieve the
  // reference to 'r'.
  //
  // If we have:
  //
  // struct SS {
  //   Bla S;
  //   foo() {
  //     #pragma acc target map (S.Arr[:12]);
  //   }
  // }
  //
  // We want to retrieve the member expression 'this->S';

  Expr *RelevantExpr = nullptr;

  // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.2]
  //  If a list item is an array section, it must specify contiguous storage.
  //
  // For this restriction it is sufficient that we make sure only references
  // to variables or fields and array expressions, and that no array sections
  // exist except in the rightmost expression (unless they cover the whole
  // dimension of the array). E.g. these would be invalid:
  //
  //   r.ArrS[3:5].Arr[6:7]
  //
  //   r.ArrS[3:5].x
  //
  // but these would be valid:
  //   r.ArrS[3].Arr[6:7]
  //
  //   r.ArrS[3].x

  bool AllowUnitySizeArraySection = true;
  bool AllowWholeSizeArraySection = true;

  while (!RelevantExpr) {
    E = E->IgnoreParenImpCasts();

    if (auto *CurE = dyn_cast<DeclRefExpr>(E)) {
      if (!isa<VarDecl>(CurE->getDecl()))
        return nullptr;

      RelevantExpr = CurE;

      // If we got a reference to a declaration, we should not expect any array
      // section before that.
      AllowUnitySizeArraySection = false;
      AllowWholeSizeArraySection = false;

      // Record the component.
      CurComponents.emplace_back(CurE, CurE->getDecl());
    } else if (auto *CurE = dyn_cast<MemberExpr>(E)) {
      auto *BaseE = CurE->getBase()->IgnoreParenImpCasts();

      if (isa<CXXThisExpr>(BaseE))
        // We found a base expression: this->Val.
        RelevantExpr = CurE;
      else
        E = BaseE;

      if (!isa<FieldDecl>(CurE->getMemberDecl())) {
        if (!NoDiagnose) {
          SemaRef.Diag(ELoc, diag::err_acc_expected_access_to_data_field)
              << CurE->getSourceRange();
          return nullptr;
        }
        if (RelevantExpr)
          return nullptr;
        continue;
      }

      auto *FD = cast<FieldDecl>(CurE->getMemberDecl());

      // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C/C++, p.3]
      //  A bit-field cannot appear in a map clause.
      //
      if (FD->isBitField()) {
        if (!NoDiagnose) {
          SemaRef.Diag(ELoc, diag::err_acc_bit_fields_forbidden_in_clause)
              << CurE->getSourceRange() << getOpenACCClauseName(CKind);
          return nullptr;
        }
        if (RelevantExpr)
          return nullptr;
        continue;
      }

      // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C++, p.1]
      //  If the type of a list item is a reference to a type T then the type
      //  will be considered to be T for all purposes of this clause.
      QualType CurType = BaseE->getType().getNonReferenceType();

      // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C/C++, p.2]
      //  A list item cannot be a variable that is a member of a structure with
      //  a union type.
      //
      if (auto *RT = CurType->getAs<RecordType>()) {
        if (RT->isUnionType()) {
          if (!NoDiagnose) {
            SemaRef.Diag(ELoc, diag::err_acc_union_type_not_allowed)
                << CurE->getSourceRange();
            return nullptr;
          }
          continue;
        }
      }

      // If we got a member expression, we should not expect any array section
      // before that:
      //
      // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.7]
      //  If a list item is an element of a structure, only the rightmost symbol
      //  of the variable reference can be an array section.
      //
      AllowUnitySizeArraySection = false;
      AllowWholeSizeArraySection = false;

      // Record the component.
      CurComponents.emplace_back(CurE, FD);
    } else if (auto *CurE = dyn_cast<ArraySubscriptExpr>(E)) {
      E = CurE->getBase()->IgnoreParenImpCasts();

      if (!E->getType()->isAnyPointerType() && !E->getType()->isArrayType()) {
        if (!NoDiagnose) {
          SemaRef.Diag(ELoc, diag::err_acc_expected_base_var_name)
              << 0 << CurE->getSourceRange();
          return nullptr;
        }
        continue;
      }

      // If we got an array subscript that express the whole dimension we
      // can have any array expressions before. If it only expressing part of
      // the dimension, we can only have unitary-size array expressions.
      if (CheckArrayExpressionDoesNotReferToWholeSize(SemaRef, CurE,
                                                      E->getType()))
        AllowWholeSizeArraySection = false;

      // Record the component - we don't have any declaration associated.
      CurComponents.emplace_back(CurE, nullptr);
    } else if (auto *CurE = dyn_cast<ACCArraySectionExpr>(E)) {
      assert(!NoDiagnose && "Array sections cannot be implicitly mapped.");
      E = CurE->getBase()->IgnoreParenImpCasts();

      QualType CurType =
          ACCArraySectionExpr::getBaseOriginalType(E).getCanonicalType();

      // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C++, p.1]
      //  If the type of a list item is a reference to a type T then the type
      //  will be considered to be T for all purposes of this clause.
      if (CurType->isReferenceType())
        CurType = CurType->getPointeeType();

      bool IsPointer = CurType->isAnyPointerType();

      if (!IsPointer && !CurType->isArrayType()) {
        SemaRef.Diag(ELoc, diag::err_acc_expected_base_var_name)
            << 0 << CurE->getSourceRange();
        return nullptr;
      }

      bool NotWhole =
          CheckArrayExpressionDoesNotReferToWholeSize(SemaRef, CurE, CurType);
      bool NotUnity =
          CheckArrayExpressionDoesNotReferToUnitySize(SemaRef, CurE, CurType);

      if (AllowWholeSizeArraySection) {
        // Any array section is currently allowed. Allowing a whole size array
        // section implies allowing a unity array section as well.
        //
        // If this array section refers to the whole dimension we can still
        // accept other array sections before this one, except if the base is a
        // pointer. Otherwise, only unitary sections are accepted.
        if (NotWhole || IsPointer)
          AllowWholeSizeArraySection = false;
      } else if (AllowUnitySizeArraySection && NotUnity) {
        // A unity or whole array section is not allowed and that is not
        // compatible with the properties of the current array section.
        SemaRef.Diag(
            ELoc, diag::err_acc_array_section_does_not_specify_contiguous_storage)
            << CurE->getSourceRange();
        return nullptr;
      }

      // Record the component - we don't have any declaration associated.
      CurComponents.emplace_back(CurE, nullptr);
    } else {
      if (!NoDiagnose) {
        // If nothing else worked, this is not a valid map clause expression.
        SemaRef.Diag(
            ELoc, diag::err_acc_expected_named_var_member_or_array_expression)
            << ERange;
      }
      return nullptr;
    }
  }

  return RelevantExpr;
}

// Return true if expression E associated with value VD has conflicts with other
// map information.
static bool CheckMapConflicts(
    Sema &SemaRef, DSAStackTy *DSAS, ValueDecl *VD, Expr *E,
    bool CurrentRegionOnly,
    ACCClauseMappableExprCommon::MappableExprComponentListRef CurComponents,
    OpenACCClauseKind CKind) {
  assert(VD && E);
  SourceLocation ELoc = E->getExprLoc();
  SourceRange ERange = E->getSourceRange();

  // In order to easily check the conflicts we need to match each component of
  // the expression under test with the components of the expressions that are
  // already in the stack.

  assert(!CurComponents.empty() && "Map clause expression with no components!");
  assert(CurComponents.back().getAssociatedDeclaration() == VD &&
         "Map clause expression with unexpected base!");

  // Variables to help detecting enclosing problems in data environment nests.
  bool IsEnclosedByDataEnvironmentExpr = false;
  const Expr *EnclosingExpr = nullptr;

  bool FoundError = DSAS->checkMappableExprComponentListsForDecl(
      VD, CurrentRegionOnly,
      [&](ACCClauseMappableExprCommon::MappableExprComponentListRef
              StackComponents,
          OpenACCClauseKind) -> bool {

        assert(!StackComponents.empty() &&
               "Map clause expression with no components!");
        assert(StackComponents.back().getAssociatedDeclaration() == VD &&
               "Map clause expression with unexpected base!");

        // The whole expression in the stack.
        auto *RE = StackComponents.front().getAssociatedExpression();

        // Expressions must start from the same base. Here we detect at which
        // point both expressions diverge from each other and see if we can
        // detect if the memory referred to both expressions is contiguous and
        // do not overlap.
        auto CI = CurComponents.rbegin();
        auto CE = CurComponents.rend();
        auto SI = StackComponents.rbegin();
        auto SE = StackComponents.rend();
        for (; CI != CE && SI != SE; ++CI, ++SI) {

          // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.3]
          //  At most one list item can be an array item derived from a given
          //  variable in map clauses of the same construct.
          if (CurrentRegionOnly &&
              (isa<ArraySubscriptExpr>(CI->getAssociatedExpression()) ||
               isa<ACCArraySectionExpr>(CI->getAssociatedExpression())) &&
              (isa<ArraySubscriptExpr>(SI->getAssociatedExpression()) ||
               isa<ACCArraySectionExpr>(SI->getAssociatedExpression()))) {
            SemaRef.Diag(CI->getAssociatedExpression()->getExprLoc(),
                         diag::err_acc_multiple_array_items_in_map_clause)
                << CI->getAssociatedExpression()->getSourceRange();
            SemaRef.Diag(SI->getAssociatedExpression()->getExprLoc(),
                         diag::note_used_here)
                << SI->getAssociatedExpression()->getSourceRange();
            return true;
          }

          // Do both expressions have the same kind?
          if (CI->getAssociatedExpression()->getStmtClass() !=
              SI->getAssociatedExpression()->getStmtClass())
            break;

          // Are we dealing with different variables/fields?
          if (CI->getAssociatedDeclaration() != SI->getAssociatedDeclaration())
            break;
        }
        // Check if the extra components of the expressions in the enclosing
        // data environment are redundant for the current base declaration.
        // If they are, the maps completely overlap, which is legal.
        for (; SI != SE; ++SI) {
          QualType Type;
          if (auto *ASE =
                  dyn_cast<ArraySubscriptExpr>(SI->getAssociatedExpression())) {
            Type = ASE->getBase()->IgnoreParenImpCasts()->getType();
          } else if (auto *OASE = dyn_cast<ACCArraySectionExpr>(
                         SI->getAssociatedExpression())) {
            auto *E = OASE->getBase()->IgnoreParenImpCasts();
            Type =
                ACCArraySectionExpr::getBaseOriginalType(E).getCanonicalType();
          }
          if (Type.isNull() || Type->isAnyPointerType() ||
              CheckArrayExpressionDoesNotReferToWholeSize(
                  SemaRef, SI->getAssociatedExpression(), Type))
            break;
        }

        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.4]
        //  List items of map clauses in the same construct must not share
        //  original storage.
        //
        // If the expressions are exactly the same or one is a subset of the
        // other, it means they are sharing storage.
        if (CI == CE && SI == SE) {
          if (CurrentRegionOnly) {
            if (CKind == ACCC_map)
              SemaRef.Diag(ELoc, diag::err_acc_map_shared_storage) << ERange;
            else {
              assert(CKind == ACCC_to || CKind == ACCC_from);
              SemaRef.Diag(ELoc, diag::err_acc_once_referenced_in_target_update)
                  << ERange;
            }
            SemaRef.Diag(RE->getExprLoc(), diag::note_used_here)
                << RE->getSourceRange();
            return true;
          } else {
            // If we find the same expression in the enclosing data environment,
            // that is legal.
            IsEnclosedByDataEnvironmentExpr = true;
            return false;
          }
        }

        QualType DerivedType =
            std::prev(CI)->getAssociatedDeclaration()->getType();
        SourceLocation DerivedLoc =
            std::prev(CI)->getAssociatedExpression()->getExprLoc();

        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C++, p.1]
        //  If the type of a list item is a reference to a type T then the type
        //  will be considered to be T for all purposes of this clause.
        DerivedType = DerivedType.getNonReferenceType();

        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C/C++, p.1]
        //  A variable for which the type is pointer and an array section
        //  derived from that variable must not appear as list items of map
        //  clauses of the same construct.
        //
        // Also, cover one of the cases in:
        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.5]
        //  If any part of the original storage of a list item has corresponding
        //  storage in the device data environment, all of the original storage
        //  must have corresponding storage in the device data environment.
        //
        if (DerivedType->isAnyPointerType()) {
          if (CI == CE || SI == SE) {
            SemaRef.Diag(
                DerivedLoc,
                diag::err_acc_pointer_mapped_along_with_derived_section)
                << DerivedLoc;
          } else {
            assert(CI != CE && SI != SE);
            SemaRef.Diag(DerivedLoc, diag::err_acc_same_pointer_derreferenced)
                << DerivedLoc;
          }
          SemaRef.Diag(RE->getExprLoc(), diag::note_used_here)
              << RE->getSourceRange();
          return true;
        }

        // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.4]
        //  List items of map clauses in the same construct must not share
        //  original storage.
        //
        // An expression is a subset of the other.
        if (CurrentRegionOnly && (CI == CE || SI == SE)) {
          if (CKind == ACCC_map)
            SemaRef.Diag(ELoc, diag::err_acc_map_shared_storage) << ERange;
          else {
            assert(CKind == ACCC_to || CKind == ACCC_from);
            SemaRef.Diag(ELoc, diag::err_acc_once_referenced_in_target_update)
                << ERange;
          }
          SemaRef.Diag(RE->getExprLoc(), diag::note_used_here)
              << RE->getSourceRange();
          return true;
        }

        // The current expression uses the same base as other expression in the
        // data environment but does not contain it completely.
        if (!CurrentRegionOnly && SI != SE)
          EnclosingExpr = RE;

        // The current expression is a subset of the expression in the data
        // environment.
        IsEnclosedByDataEnvironmentExpr |=
            (!CurrentRegionOnly && CI != CE && SI == SE);

        return false;
      });

  if (CurrentRegionOnly)
    return FoundError;

  // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.5]
  //  If any part of the original storage of a list item has corresponding
  //  storage in the device data environment, all of the original storage must
  //  have corresponding storage in the device data environment.
  // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.6]
  //  If a list item is an element of a structure, and a different element of
  //  the structure has a corresponding list item in the device data environment
  //  prior to a task encountering the construct associated with the map clause,
  //  then the list item must also have a corresponding list item in the device
  //  data environment prior to the task encountering the construct.
  //
  if (EnclosingExpr && !IsEnclosedByDataEnvironmentExpr) {
    SemaRef.Diag(ELoc,
                 diag::err_acc_original_storage_is_shared_and_does_not_contain)
        << ERange;
    SemaRef.Diag(EnclosingExpr->getExprLoc(), diag::note_used_here)
        << EnclosingExpr->getSourceRange();
    return true;
  }

  return FoundError;
}

namespace {
// Utility struct that gathers all the related lists associated with a mappable
// expression.
struct MappableVarListInfo final {
  // The list of expressions.
  ArrayRef<Expr *> VarList;
  // The list of processed expressions.
  SmallVector<Expr *, 16> ProcessedVarList;
  // The mappble components for each expression.
  ACCClauseMappableExprCommon::MappableExprComponentLists VarComponents;
  // The base declaration of the variable.
  SmallVector<ValueDecl *, 16> VarBaseDeclarations;

  MappableVarListInfo(ArrayRef<Expr *> VarList) : VarList(VarList) {
    // We have a list of components and base declarations for each entry in the
    // variable list.
    VarComponents.reserve(VarList.size());
    VarBaseDeclarations.reserve(VarList.size());
  }
};
}

// Check the validity of the provided variable list for the provided clause kind
// \a CKind. In the check process the valid expressions, and mappable expression
// components and variables are extracted and used to fill \a Vars,
// \a ClauseComponents, and \a ClauseBaseDeclarations. \a MapType and
// \a IsMapTypeImplicit are expected to be valid if the clause kind is 'map'.
static void
checkMappableExpressionList(Sema &SemaRef, DSAStackTy *DSAS,
                            OpenACCClauseKind CKind, MappableVarListInfo &MVLI,
                            SourceLocation StartLoc,
                            OpenACCMapClauseKind MapType = ACCC_MAP_unknown,
                            bool IsMapTypeImplicit = false) {
  // We only expect mappable expressions in 'to', 'from', and 'map' clauses.
  assert((CKind == ACCC_map || CKind == ACCC_to || CKind == ACCC_from) &&
         "Unexpected clause kind with mappable expressions!");

  // Keep track of the mappable components and base declarations in this clause.
  // Each entry in the list is going to have a list of components associated. We
  // record each set of the components so that we can build the clause later on.
  // In the end we should have the same amount of declarations and component
  // lists.

  for (auto &RE : MVLI.VarList) {
    assert(RE && "Null expr in acc to/from/map clause");
    SourceLocation ELoc = RE->getExprLoc();

    auto *VE = RE->IgnoreParenLValueCasts();

    if (VE->isValueDependent() || VE->isTypeDependent() ||
        VE->isInstantiationDependent() ||
        VE->containsUnexpandedParameterPack()) {
      // We can only analyze this information once the missing information is
      // resolved.
      MVLI.ProcessedVarList.push_back(RE);
      continue;
    }

    auto *SimpleExpr = RE->IgnoreParenCasts();

    if (!RE->IgnoreParenImpCasts()->isLValue()) {
      SemaRef.Diag(ELoc,
                   diag::err_acc_expected_named_var_member_or_array_expression)
          << RE->getSourceRange();
      continue;
    }

    ACCClauseMappableExprCommon::MappableExprComponentList CurComponents;
    ValueDecl *CurDeclaration = nullptr;

    // Obtain the array or member expression bases if required. Also, fill the
    // components array with all the components identified in the process.
    auto *BE = CheckMapClauseExpressionBase(SemaRef, SimpleExpr, CurComponents,
                                            CKind, /*NoDiagnose=*/false);
    if (!BE)
      continue;

    assert(!CurComponents.empty() &&
           "Invalid mappable expression information.");

    // For the following checks, we rely on the base declaration which is
    // expected to be associated with the last component. The declaration is
    // expected to be a variable or a field (if 'this' is being mapped).
    CurDeclaration = CurComponents.back().getAssociatedDeclaration();
    assert(CurDeclaration && "Null decl on map clause.");
    assert(
        CurDeclaration->isCanonicalDecl() &&
        "Expecting components to have associated only canonical declarations.");

    auto *VD = dyn_cast<VarDecl>(CurDeclaration);
    auto *FD = dyn_cast<FieldDecl>(CurDeclaration);

    assert((VD || FD) && "Only variables or fields are expected here!");
    (void)FD;

    // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.10]
    // threadprivate variables cannot appear in a map clause.
    // OpenACC 4.5 [2.10.5, target update Construct]
    // threadprivate variables cannot appear in a from clause.
    if (VD && DSAS->isThreadPrivate(VD)) {
      auto DVar = DSAS->getTopDSA(VD, false);
      SemaRef.Diag(ELoc, diag::err_acc_threadprivate_in_clause)
          << getOpenACCClauseName(CKind);
      ReportOriginalDSA(SemaRef, DSAS, VD, DVar);
      continue;
    }

    // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.9]
    //  A list item cannot appear in both a map clause and a data-sharing
    //  attribute clause on the same construct.

    // Check conflicts with other map clause expressions. We check the conflicts
    // with the current construct separately from the enclosing data
    // environment, because the restrictions are different. We only have to
    // check conflicts across regions for the map clauses.
    if (CheckMapConflicts(SemaRef, DSAS, CurDeclaration, SimpleExpr,
                          /*CurrentRegionOnly=*/true, CurComponents, CKind))
      break;
    if (CKind == ACCC_map &&
        CheckMapConflicts(SemaRef, DSAS, CurDeclaration, SimpleExpr,
                          /*CurrentRegionOnly=*/false, CurComponents, CKind))
      break;

    // OpenACC 4.5 [2.10.5, target update Construct]
    // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, C++, p.1]
    //  If the type of a list item is a reference to a type T then the type will
    //  be considered to be T for all purposes of this clause.
    QualType Type = CurDeclaration->getType().getNonReferenceType();

    // OpenACC 4.5 [2.10.5, target update Construct, Restrictions, p.4]
    // A list item in a to or from clause must have a mappable type.
    // OpenACC 4.5 [2.15.5.1, map Clause, Restrictions, p.9]
    //  A list item must have a mappable type.
    if (!CheckTypeMappable(VE->getExprLoc(), VE->getSourceRange(), SemaRef,
                           DSAS, Type))
      continue;

    if (CKind == ACCC_map) {
      // target enter data
      // OpenACC [2.10.2, Restrictions, p. 99]
      // A map-type must be specified in all map clauses and must be either
      // to or alloc.
      OpenACCDirectiveKind DKind = DSAS->getCurrentDirective();
      if (DKind == ACCD_target_enter_data &&
          !(MapType == ACCC_MAP_to || MapType == ACCC_MAP_alloc)) {
        SemaRef.Diag(StartLoc, diag::err_acc_invalid_map_type_for_directive)
            << (IsMapTypeImplicit ? 1 : 0)
            << getOpenACCSimpleClauseTypeName(ACCC_map, MapType)
            << getOpenACCDirectiveName(DKind);
        continue;
      }

      // target exit_data
      // OpenACC [2.10.3, Restrictions, p. 102]
      // A map-type must be specified in all map clauses and must be either
      // from, release, or delete.
      if (DKind == ACCD_target_exit_data &&
          !(MapType == ACCC_MAP_from || MapType == ACCC_MAP_release ||
            MapType == ACCC_MAP_delete)) {
        SemaRef.Diag(StartLoc, diag::err_acc_invalid_map_type_for_directive)
            << (IsMapTypeImplicit ? 1 : 0)
            << getOpenACCSimpleClauseTypeName(ACCC_map, MapType)
            << getOpenACCDirectiveName(DKind);
        continue;
      }

      // OpenACC 4.5 [2.15.5.1, Restrictions, p.3]
      // A list item cannot appear in both a map clause and a data-sharing
      // attribute clause on the same construct
      if ((DKind == ACCD_target || DKind == ACCD_target_teams ||
           DKind == ACCD_target_teams_distribute ||
           DKind == ACCD_target_teams_distribute_parallel_for ||
           DKind == ACCD_target_teams_distribute_parallel_for_simd ||
           DKind == ACCD_target_teams_distribute_simd) && VD) {
        auto DVar = DSAS->getTopDSA(VD, false);
        if (isOpenACCPrivate(DVar.CKind)) {
          SemaRef.Diag(ELoc, diag::err_acc_variable_in_given_clause_and_dsa)
              << getOpenACCClauseName(DVar.CKind)
              << getOpenACCClauseName(ACCC_map)
              << getOpenACCDirectiveName(DSAS->getCurrentDirective());
          ReportOriginalDSA(SemaRef, DSAS, CurDeclaration, DVar);
          continue;
        }
      }
    }

    // Save the current expression.
    MVLI.ProcessedVarList.push_back(RE);

    // Store the components in the stack so that they can be used to check
    // against other clauses later on.
    DSAS->addMappableExpressionComponents(CurDeclaration, CurComponents,
                                          /*WhereFoundClauseKind=*/ACCC_map);

    // Save the components and declaration to create the clause. For purposes of
    // the clause creation, any component list that has has base 'this' uses
    // null as base declaration.
    MVLI.VarComponents.resize(MVLI.VarComponents.size() + 1);
    MVLI.VarComponents.back().append(CurComponents.begin(),
                                     CurComponents.end());
    MVLI.VarBaseDeclarations.push_back(isa<MemberExpr>(BE) ? nullptr
                                                           : CurDeclaration);
  }
}

ACCClause *
Sema::ActOnOpenACCMapClause(OpenACCMapClauseKind MapTypeModifier,
                           OpenACCMapClauseKind MapType, bool IsMapTypeImplicit,
                           SourceLocation MapLoc, SourceLocation ColonLoc,
                           ArrayRef<Expr *> VarList, SourceLocation StartLoc,
                           SourceLocation LParenLoc, SourceLocation EndLoc) {
  MappableVarListInfo MVLI(VarList);
  checkMappableExpressionList(*this, DSAStack, ACCC_map, MVLI, StartLoc,
                              MapType, IsMapTypeImplicit);

  // We need to produce a map clause even if we don't have variables so that
  // other diagnostics related with non-existing map clauses are accurate.
  return ACCMapClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                              MVLI.ProcessedVarList, MVLI.VarBaseDeclarations,
                              MVLI.VarComponents, MapTypeModifier, MapType,
                              IsMapTypeImplicit, MapLoc);
}

QualType Sema::ActOnOpenACCDeclareReductionType(SourceLocation TyLoc,
                                               TypeResult ParsedType) {
  assert(ParsedType.isUsable());

  QualType ReductionType = GetTypeFromParser(ParsedType.get());
  if (ReductionType.isNull())
    return QualType();

  // [OpenACC 4.0], 2.15 declare reduction Directive, Restrictions, C\C++
  // A type name in a declare reduction directive cannot be a function type, an
  // array type, a reference type, or a type qualified with const, volatile or
  // restrict.
  if (ReductionType.hasQualifiers()) {
    Diag(TyLoc, diag::err_acc_reduction_wrong_type) << 0;
    return QualType();
  }

  if (ReductionType->isFunctionType()) {
    Diag(TyLoc, diag::err_acc_reduction_wrong_type) << 1;
    return QualType();
  }
  if (ReductionType->isReferenceType()) {
    Diag(TyLoc, diag::err_acc_reduction_wrong_type) << 2;
    return QualType();
  }
  if (ReductionType->isArrayType()) {
    Diag(TyLoc, diag::err_acc_reduction_wrong_type) << 3;
    return QualType();
  }
  return ReductionType;
}

Sema::DeclGroupPtrTy Sema::ActOnOpenACCDeclareReductionDirectiveStart(
    Scope *S, DeclContext *DC, DeclarationName Name,
    ArrayRef<std::pair<QualType, SourceLocation>> ReductionTypes,
    AccessSpecifier AS, Decl *PrevDeclInScope) {
  SmallVector<Decl *, 8> Decls;
  Decls.reserve(ReductionTypes.size());

  LookupResult Lookup(*this, Name, SourceLocation(), LookupACCReductionName,
                      forRedeclarationInCurContext());
  // [OpenACC 4.0], 2.15 declare reduction Directive, Restrictions
  // A reduction-identifier may not be re-declared in the current scope for the
  // same type or for a type that is compatible according to the base language
  // rules.
  llvm::DenseMap<QualType, SourceLocation> PreviousRedeclTypes;
  ACCDeclareReductionDecl *PrevDRD = nullptr;
  bool InCompoundScope = true;
  if (S != nullptr) {
    // Find previous declaration with the same name not referenced in other
    // declarations.
    FunctionScopeInfo *ParentFn = getEnclosingFunction();
    InCompoundScope =
        (ParentFn != nullptr) && !ParentFn->CompoundScopes.empty();
    LookupName(Lookup, S);
    FilterLookupForScope(Lookup, DC, S, /*ConsiderLinkage=*/false,
                         /*AllowInlineNamespace=*/false);
    llvm::DenseMap<ACCDeclareReductionDecl *, bool> UsedAsPrevious;
    auto Filter = Lookup.makeFilter();
    while (Filter.hasNext()) {
      auto *PrevDecl = cast<ACCDeclareReductionDecl>(Filter.next());
      if (InCompoundScope) {
        auto I = UsedAsPrevious.find(PrevDecl);
        if (I == UsedAsPrevious.end())
          UsedAsPrevious[PrevDecl] = false;
        if (auto *D = PrevDecl->getPrevDeclInScope())
          UsedAsPrevious[D] = true;
      }
      PreviousRedeclTypes[PrevDecl->getType().getCanonicalType()] =
          PrevDecl->getLocation();
    }
    Filter.done();
    if (InCompoundScope) {
      for (auto &PrevData : UsedAsPrevious) {
        if (!PrevData.second) {
          PrevDRD = PrevData.first;
          break;
        }
      }
    }
  } else if (PrevDeclInScope != nullptr) {
    auto *PrevDRDInScope = PrevDRD =
        cast<ACCDeclareReductionDecl>(PrevDeclInScope);
    do {
      PreviousRedeclTypes[PrevDRDInScope->getType().getCanonicalType()] =
          PrevDRDInScope->getLocation();
      PrevDRDInScope = PrevDRDInScope->getPrevDeclInScope();
    } while (PrevDRDInScope != nullptr);
  }
  for (auto &TyData : ReductionTypes) {
    auto I = PreviousRedeclTypes.find(TyData.first.getCanonicalType());
    bool Invalid = false;
    if (I != PreviousRedeclTypes.end()) {
      Diag(TyData.second, diag::err_acc_declare_reduction_redefinition)
          << TyData.first;
      Diag(I->second, diag::note_previous_definition);
      Invalid = true;
    }
    PreviousRedeclTypes[TyData.first.getCanonicalType()] = TyData.second;
    auto *DRD = ACCDeclareReductionDecl::Create(Context, DC, TyData.second,
                                                Name, TyData.first, PrevDRD);
    DC->addDecl(DRD);
    DRD->setAccess(AS);
    Decls.push_back(DRD);
    if (Invalid)
      DRD->setInvalidDecl();
    else
      PrevDRD = DRD;
  }

  return DeclGroupPtrTy::make(
      DeclGroupRef::Create(Context, Decls.begin(), Decls.size()));
}

void Sema::ActOnOpenACCDeclareReductionCombinerStart(Scope *S, Decl *D) {
  auto *DRD = cast<ACCDeclareReductionDecl>(D);

  // Enter new function scope.
  PushFunctionScope();
  getCurFunction()->setHasBranchProtectedScope();
  getCurFunction()->setHasACCDeclareReductionCombiner();

  if (S != nullptr)
    PushDeclContext(S, DRD);
  else
    CurContext = DRD;

  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);

  QualType ReductionType = DRD->getType();
  // Create 'T* omp_parm;T omp_in;'. All references to 'omp_in' will
  // be replaced by '*omp_parm' during codegen. This required because 'omp_in'
  // uses semantics of argument handles by value, but it should be passed by
  // reference. C lang does not support references, so pass all parameters as
  // pointers.
  // Create 'T omp_in;' variable.
  auto *OmpInParm =
      buildVarDecl(*this, D->getLocation(), ReductionType, "omp_in");
  // Create 'T* omp_parm;T omp_out;'. All references to 'omp_out' will
  // be replaced by '*omp_parm' during codegen. This required because 'omp_out'
  // uses semantics of argument handles by value, but it should be passed by
  // reference. C lang does not support references, so pass all parameters as
  // pointers.
  // Create 'T omp_out;' variable.
  auto *OmpOutParm =
      buildVarDecl(*this, D->getLocation(), ReductionType, "omp_out");
  if (S != nullptr) {
    PushOnScopeChains(OmpInParm, S);
    PushOnScopeChains(OmpOutParm, S);
  } else {
    DRD->addDecl(OmpInParm);
    DRD->addDecl(OmpOutParm);
  }
}

void Sema::ActOnOpenACCDeclareReductionCombinerEnd(Decl *D, Expr *Combiner) {
  auto *DRD = cast<ACCDeclareReductionDecl>(D);
  DiscardCleanupsInEvaluationContext();
  PopExpressionEvaluationContext();

  PopDeclContext();
  PopFunctionScopeInfo();

  if (Combiner != nullptr)
    DRD->setCombiner(Combiner);
  else
    DRD->setInvalidDecl();
}

VarDecl *Sema::ActOnOpenACCDeclareReductionInitializerStart(Scope *S, Decl *D) {
  auto *DRD = cast<ACCDeclareReductionDecl>(D);

  // Enter new function scope.
  PushFunctionScope();
  getCurFunction()->setHasBranchProtectedScope();

  if (S != nullptr)
    PushDeclContext(S, DRD);
  else
    CurContext = DRD;

  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);

  QualType ReductionType = DRD->getType();
  // Create 'T* omp_parm;T omp_priv;'. All references to 'omp_priv' will
  // be replaced by '*omp_parm' during codegen. This required because 'omp_priv'
  // uses semantics of argument handles by value, but it should be passed by
  // reference. C lang does not support references, so pass all parameters as
  // pointers.
  // Create 'T omp_priv;' variable.
  auto *OmpPrivParm =
      buildVarDecl(*this, D->getLocation(), ReductionType, "omp_priv");
  // Create 'T* omp_parm;T omp_orig;'. All references to 'omp_orig' will
  // be replaced by '*omp_parm' during codegen. This required because 'omp_orig'
  // uses semantics of argument handles by value, but it should be passed by
  // reference. C lang does not support references, so pass all parameters as
  // pointers.
  // Create 'T omp_orig;' variable.
  auto *OmpOrigParm =
      buildVarDecl(*this, D->getLocation(), ReductionType, "omp_orig");
  if (S != nullptr) {
    PushOnScopeChains(OmpPrivParm, S);
    PushOnScopeChains(OmpOrigParm, S);
  } else {
    DRD->addDecl(OmpPrivParm);
    DRD->addDecl(OmpOrigParm);
  }
  return OmpPrivParm;
}

void Sema::ActOnOpenACCDeclareReductionInitializerEnd(Decl *D, Expr *Initializer,
                                                     VarDecl *OmpPrivParm) {
  auto *DRD = cast<ACCDeclareReductionDecl>(D);
  DiscardCleanupsInEvaluationContext();
  PopExpressionEvaluationContext();

  PopDeclContext();
  PopFunctionScopeInfo();

  if (Initializer != nullptr) {
    DRD->setInitializer(Initializer, ACCDeclareReductionDecl::CallInit);
  } else if (OmpPrivParm->hasInit()) {
    DRD->setInitializer(OmpPrivParm->getInit(),
                        OmpPrivParm->isDirectInit()
                            ? ACCDeclareReductionDecl::DirectInit
                            : ACCDeclareReductionDecl::CopyInit);
  } else {
    DRD->setInvalidDecl();
  }
}

Sema::DeclGroupPtrTy Sema::ActOnOpenACCDeclareReductionDirectiveEnd(
    Scope *S, DeclGroupPtrTy DeclReductions, bool IsValid) {
  for (auto *D : DeclReductions.get()) {
    if (IsValid) {
      auto *DRD = cast<ACCDeclareReductionDecl>(D);
      if (S != nullptr)
        PushOnScopeChains(DRD, S, /*AddToContext=*/false);
    } else
      D->setInvalidDecl();
  }
  return DeclReductions;
}

ACCClause *Sema::ActOnOpenACCNumTeamsClause(Expr *NumTeams,
                                           SourceLocation StartLoc,
                                           SourceLocation LParenLoc,
                                           SourceLocation EndLoc) {
  Expr *ValExpr = NumTeams;
  Stmt *HelperValStmt = nullptr;

  // OpenACC [teams Constrcut, Restrictions]
  // The num_teams expression must evaluate to a positive integer value.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_num_teams,
                                 /*StrictlyPositive=*/true))
    return nullptr;

  OpenACCDirectiveKind DKind = DSAStack->getCurrentDirective();
  OpenACCDirectiveKind CaptureRegion =
      getOpenACCCaptureRegionForClause(DKind, ACCC_num_teams);
  if (CaptureRegion != ACCD_unknown && !CurContext->isDependentContext()) {
    ValExpr = MakeFullExpr(ValExpr).get();
    llvm::MapVector<Expr *, DeclRefExpr *> Captures;
    ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
    HelperValStmt = buildPreInits(Context, Captures);
  }

  return new (Context) ACCNumTeamsClause(ValExpr, HelperValStmt, CaptureRegion,
                                         StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCThreadLimitClause(Expr *ThreadLimit,
                                              SourceLocation StartLoc,
                                              SourceLocation LParenLoc,
                                              SourceLocation EndLoc) {
  Expr *ValExpr = ThreadLimit;
  Stmt *HelperValStmt = nullptr;

  // OpenACC [teams Constrcut, Restrictions]
  // The thread_limit expression must evaluate to a positive integer value.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_thread_limit,
                                 /*StrictlyPositive=*/true))
    return nullptr;

  OpenACCDirectiveKind DKind = DSAStack->getCurrentDirective();
  OpenACCDirectiveKind CaptureRegion =
      getOpenACCCaptureRegionForClause(DKind, ACCC_thread_limit);
  if (CaptureRegion != ACCD_unknown && !CurContext->isDependentContext()) {
    ValExpr = MakeFullExpr(ValExpr).get();
    llvm::MapVector<Expr *, DeclRefExpr *> Captures;
    ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
    HelperValStmt = buildPreInits(Context, Captures);
  }

  return new (Context) ACCThreadLimitClause(
      ValExpr, HelperValStmt, CaptureRegion, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCPriorityClause(Expr *Priority,
                                           SourceLocation StartLoc,
                                           SourceLocation LParenLoc,
                                           SourceLocation EndLoc) {
  Expr *ValExpr = Priority;

  // OpenACC [2.9.1, task Constrcut]
  // The priority-value is a non-negative numerical scalar expression.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_priority,
                                 /*StrictlyPositive=*/false))
    return nullptr;

  return new (Context) ACCPriorityClause(ValExpr, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCGrainsizeClause(Expr *Grainsize,
                                            SourceLocation StartLoc,
                                            SourceLocation LParenLoc,
                                            SourceLocation EndLoc) {
  Expr *ValExpr = Grainsize;

  // OpenACC [2.9.2, taskloop Constrcut]
  // The parameter of the grainsize clause must be a positive integer
  // expression.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_grainsize,
                                 /*StrictlyPositive=*/true))
    return nullptr;

  return new (Context) ACCGrainsizeClause(ValExpr, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCNumTasksClause(Expr *NumTasks,
                                           SourceLocation StartLoc,
                                           SourceLocation LParenLoc,
                                           SourceLocation EndLoc) {
  Expr *ValExpr = NumTasks;

  // OpenACC [2.9.2, taskloop Constrcut]
  // The parameter of the num_tasks clause must be a positive integer
  // expression.
  if (!IsNonNegativeIntegerValue(ValExpr, *this, ACCC_num_tasks,
                                 /*StrictlyPositive=*/true))
    return nullptr;

  return new (Context) ACCNumTasksClause(ValExpr, StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCHintClause(Expr *Hint, SourceLocation StartLoc,
                                       SourceLocation LParenLoc,
                                       SourceLocation EndLoc) {
  // OpenACC [2.13.2, critical construct, Description]
  // ... where hint-expression is an integer constant expression that evaluates
  // to a valid lock hint.
  ExprResult HintExpr = VerifyPositiveIntegerConstantInClause(Hint, ACCC_hint);
  if (HintExpr.isInvalid())
    return nullptr;
  return new (Context)
      ACCHintClause(HintExpr.get(), StartLoc, LParenLoc, EndLoc);
}

ACCClause *Sema::ActOnOpenACCDistScheduleClause(
    OpenACCDistScheduleClauseKind Kind, Expr *ChunkSize, SourceLocation StartLoc,
    SourceLocation LParenLoc, SourceLocation KindLoc, SourceLocation CommaLoc,
    SourceLocation EndLoc) {
  if (Kind == ACCC_DIST_SCHEDULE_unknown) {
    std::string Values;
    Values += "'";
    Values += getOpenACCSimpleClauseTypeName(ACCC_dist_schedule, 0);
    Values += "'";
    Diag(KindLoc, diag::err_acc_unexpected_clause_value)
        << Values << getOpenACCClauseName(ACCC_dist_schedule);
    return nullptr;
  }
  Expr *ValExpr = ChunkSize;
  Stmt *HelperValStmt = nullptr;
  if (ChunkSize) {
    if (!ChunkSize->isValueDependent() && !ChunkSize->isTypeDependent() &&
        !ChunkSize->isInstantiationDependent() &&
        !ChunkSize->containsUnexpandedParameterPack()) {
      SourceLocation ChunkSizeLoc = ChunkSize->getLocStart();
      ExprResult Val =
          PerformOpenACCImplicitIntegerConversion(ChunkSizeLoc, ChunkSize);
      if (Val.isInvalid())
        return nullptr;

      ValExpr = Val.get();

      // OpenACC [2.7.1, Restrictions]
      //  chunk_size must be a loop invariant integer expression with a positive
      //  value.
      llvm::APSInt Result;
      if (ValExpr->isIntegerConstantExpr(Result, Context)) {
        if (Result.isSigned() && !Result.isStrictlyPositive()) {
          Diag(ChunkSizeLoc, diag::err_acc_negative_expression_in_clause)
              << "dist_schedule" << ChunkSize->getSourceRange();
          return nullptr;
        }
      } else if (getOpenACCCaptureRegionForClause(
                     DSAStack->getCurrentDirective(), ACCC_dist_schedule) !=
                     ACCD_unknown &&
                 !CurContext->isDependentContext()) {
        ValExpr = MakeFullExpr(ValExpr).get();
        llvm::MapVector<Expr *, DeclRefExpr *> Captures;
        ValExpr = tryBuildCapture(*this, ValExpr, Captures).get();
        HelperValStmt = buildPreInits(Context, Captures);
      }
    }
  }

  return new (Context)
      ACCDistScheduleClause(StartLoc, LParenLoc, KindLoc, CommaLoc, EndLoc,
                            Kind, ValExpr, HelperValStmt);
}

ACCClause *Sema::ActOnOpenACCDefaultmapClause(
    OpenACCDefaultmapClauseModifier M, OpenACCDefaultmapClauseKind Kind,
    SourceLocation StartLoc, SourceLocation LParenLoc, SourceLocation MLoc,
    SourceLocation KindLoc, SourceLocation EndLoc) {
  // OpenACC 4.5 only supports 'defaultmap(tofrom: scalar)'
  if (M != ACCC_DEFAULTMAP_MODIFIER_tofrom || Kind != ACCC_DEFAULTMAP_scalar) {
    std::string Value;
    SourceLocation Loc;
    Value += "'";
    if (M != ACCC_DEFAULTMAP_MODIFIER_tofrom) {
      Value += getOpenACCSimpleClauseTypeName(ACCC_defaultmap,
                                             ACCC_DEFAULTMAP_MODIFIER_tofrom);
      Loc = MLoc;
    } else {
      Value += getOpenACCSimpleClauseTypeName(ACCC_defaultmap,
                                             ACCC_DEFAULTMAP_scalar);
      Loc = KindLoc;
    }
    Value += "'";
    Diag(Loc, diag::err_acc_unexpected_clause_value)
        << Value << getOpenACCClauseName(ACCC_defaultmap);
    return nullptr;
  }
  DSAStack->setDefaultDMAToFromScalar(StartLoc);

  return new (Context)
      ACCDefaultmapClause(StartLoc, LParenLoc, MLoc, KindLoc, EndLoc, Kind, M);
}

bool Sema::ActOnStartOpenACCDeclareTargetDirective(SourceLocation Loc) {
  DeclContext *CurLexicalContext = getCurLexicalContext();
  if (!CurLexicalContext->isFileContext() &&
      !CurLexicalContext->isExternCContext() &&
      !CurLexicalContext->isExternCXXContext() &&
      !isa<CXXRecordDecl>(CurLexicalContext) &&
      !isa<ClassTemplateDecl>(CurLexicalContext) &&
      !isa<ClassTemplatePartialSpecializationDecl>(CurLexicalContext) &&
      !isa<ClassTemplateSpecializationDecl>(CurLexicalContext)) {
    Diag(Loc, diag::err_acc_region_not_file_context);
    return false;
  }
  if (IsInOpenACCDeclareTargetContext) {
    Diag(Loc, diag::err_acc_enclosed_declare_target);
    return false;
  }

  IsInOpenACCDeclareTargetContext = true;
  return true;
}

void Sema::ActOnFinishOpenACCDeclareTargetDirective() {
  assert(IsInOpenACCDeclareTargetContext &&
         "Unexpected ActOnFinishOpenACCDeclareTargetDirective");

  IsInOpenACCDeclareTargetContext = false;
}

void Sema::ActOnOpenACCDeclareTargetName(Scope *CurScope,
                                        CXXScopeSpec &ScopeSpec,
                                        const DeclarationNameInfo &Id,
                                        ACCDeclareTargetDeclAttr::MapTypeTy MT,
                                        NamedDeclSetType &SameDirectiveDecls) {
  LookupResult Lookup(*this, Id, LookupOrdinaryName);
  LookupParsedName(Lookup, CurScope, &ScopeSpec, true);

  if (Lookup.isAmbiguous())
    return;
  Lookup.suppressDiagnostics();

  if (!Lookup.isSingleResult()) {
    if (TypoCorrection Corrected =
            CorrectTypo(Id, LookupOrdinaryName, CurScope, nullptr,
                        llvm::make_unique<VarOrFuncDeclFilterCCC>(*this),
                        CTK_ErrorRecovery)) {
      diagnoseTypo(Corrected, PDiag(diag::err_undeclared_var_use_suggest)
                                  << Id.getName());
      checkDeclIsAllowedInOpenACCTarget(nullptr, Corrected.getCorrectionDecl());
      return;
    }

    Diag(Id.getLoc(), diag::err_undeclared_var_use) << Id.getName();
    return;
  }

  NamedDecl *ND = Lookup.getAsSingle<NamedDecl>();
  if (isa<VarDecl>(ND) || isa<FunctionDecl>(ND)) {
    if (!SameDirectiveDecls.insert(cast<NamedDecl>(ND->getCanonicalDecl())))
      Diag(Id.getLoc(), diag::err_acc_declare_target_multiple) << Id.getName();

    if (!ND->hasAttr<ACCDeclareTargetDeclAttr>()) {
      Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(Context, MT);
      ND->addAttr(A);
      if (ASTMutationListener *ML = Context.getASTMutationListener())
        ML->DeclarationMarkedOpenACCDeclareTarget(ND, A);
      checkDeclIsAllowedInOpenACCTarget(nullptr, ND, Id.getLoc());
    } else if (ND->getAttr<ACCDeclareTargetDeclAttr>()->getMapType() != MT) {
      Diag(Id.getLoc(), diag::err_acc_declare_target_to_and_link)
          << Id.getName();
    }
  } else
    Diag(Id.getLoc(), diag::err_acc_invalid_target_decl) << Id.getName();
}

static void checkDeclInTargetContext(SourceLocation SL, SourceRange SR,
                                     Sema &SemaRef, Decl *D) {
  if (!D)
    return;
  const Decl *LD = nullptr;
  if (isa<TagDecl>(D)) {
    LD = cast<TagDecl>(D)->getDefinition();
  } else if (isa<VarDecl>(D)) {
    LD = cast<VarDecl>(D)->getDefinition();

    // If this is an implicit variable that is legal and we do not need to do
    // anything.
    if (cast<VarDecl>(D)->isImplicit()) {
      Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(
          SemaRef.Context, ACCDeclareTargetDeclAttr::MT_To);
      D->addAttr(A);
      if (ASTMutationListener *ML = SemaRef.Context.getASTMutationListener())
        ML->DeclarationMarkedOpenACCDeclareTarget(D, A);
      return;
    }
  } else if (auto *F = dyn_cast<FunctionDecl>(D)) {
    const FunctionDecl *FD = nullptr;
    if (cast<FunctionDecl>(D)->hasBody(FD)) {
      LD = FD;
      // If the definition is associated with the current declaration in the
      // target region (it can be e.g. a lambda) that is legal and we do not
      // need to do anything else.
      if (LD == D) {
        Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(
            SemaRef.Context, ACCDeclareTargetDeclAttr::MT_To);
        D->addAttr(A);
        if (ASTMutationListener *ML = SemaRef.Context.getASTMutationListener())
          ML->DeclarationMarkedOpenACCDeclareTarget(D, A);
        return;
      }
    } else if (F->isFunctionTemplateSpecialization() &&
               F->getTemplateSpecializationKind() ==
                   TSK_ImplicitInstantiation) {
      // Check if the function is implicitly instantiated from the template
      // defined in the declare target region.
      const FunctionTemplateDecl *FTD = F->getPrimaryTemplate();
      if (FTD && FTD->hasAttr<ACCDeclareTargetDeclAttr>())
        return;
    }
  }
  if (!LD)
    LD = D;
  if (LD && !LD->hasAttr<ACCDeclareTargetDeclAttr>() &&
      (isa<VarDecl>(LD) || isa<FunctionDecl>(LD))) {
    // Outlined declaration is not declared target.
    if (LD->isOutOfLine()) {
      SemaRef.Diag(LD->getLocation(), diag::warn_acc_not_in_target_context);
      SemaRef.Diag(SL, diag::note_used_here) << SR;
    } else {
      const DeclContext *DC = LD->getDeclContext();
      while (DC) {
        if (isa<FunctionDecl>(DC) &&
            cast<FunctionDecl>(DC)->hasAttr<ACCDeclareTargetDeclAttr>())
          break;
        DC = DC->getParent();
      }
      if (DC)
        return;

      // Is not declared in target context.
      SemaRef.Diag(LD->getLocation(), diag::warn_acc_not_in_target_context);
      SemaRef.Diag(SL, diag::note_used_here) << SR;
    }
    // Mark decl as declared target to prevent further diagnostic.
    Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(
        SemaRef.Context, ACCDeclareTargetDeclAttr::MT_To);
    D->addAttr(A);
    if (ASTMutationListener *ML = SemaRef.Context.getASTMutationListener())
      ML->DeclarationMarkedOpenACCDeclareTarget(D, A);
  }
}

static bool checkValueDeclInTarget(SourceLocation SL, SourceRange SR,
                                   Sema &SemaRef, DSAStackTy *Stack,
                                   ValueDecl *VD) {
  if (VD->hasAttr<ACCDeclareTargetDeclAttr>())
    return true;
  if (!CheckTypeMappable(SL, SR, SemaRef, Stack, VD->getType()))
    return false;
  return true;
}

void Sema::checkDeclIsAllowedInOpenACCTarget(Expr *E, Decl *D,
                                            SourceLocation IdLoc) {
  if (!D || D->isInvalidDecl())
    return;
  SourceRange SR = E ? E->getSourceRange() : D->getSourceRange();
  SourceLocation SL = E ? E->getLocStart() : D->getLocation();
  // 2.10.6: threadprivate variable cannot appear in a declare target directive.
  if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
    if (DSAStack->isThreadPrivate(VD)) {
      Diag(SL, diag::err_acc_threadprivate_in_target);
      ReportOriginalDSA(*this, DSAStack, VD, DSAStack->getTopDSA(VD, false));
      return;
    }
  }
  if (ValueDecl *VD = dyn_cast<ValueDecl>(D)) {
    // Problem if any with var declared with incomplete type will be reported
    // as normal, so no need to check it here.
    if ((E || !VD->getType()->isIncompleteType()) &&
        !checkValueDeclInTarget(SL, SR, *this, DSAStack, VD)) {
      // Mark decl as declared target to prevent further diagnostic.
      if (isa<VarDecl>(VD) || isa<FunctionDecl>(VD) ||
          isa<FunctionTemplateDecl>(VD)) {
        Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(
            Context, ACCDeclareTargetDeclAttr::MT_To);
        VD->addAttr(A);
        if (ASTMutationListener *ML = Context.getASTMutationListener())
          ML->DeclarationMarkedOpenACCDeclareTarget(VD, A);
      }
      return;
    }
  }
  if (FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
    if (FD->hasAttr<ACCDeclareTargetDeclAttr>() &&
        (FD->getAttr<ACCDeclareTargetDeclAttr>()->getMapType() ==
         ACCDeclareTargetDeclAttr::MT_Link)) {
      assert(IdLoc.isValid() && "Source location is expected");
      Diag(IdLoc, diag::err_acc_function_in_link_clause);
      Diag(FD->getLocation(), diag::note_defined_here) << FD;
      return;
    }
  }
  if (auto *FTD = dyn_cast<FunctionTemplateDecl>(D)) {
    if (FTD->hasAttr<ACCDeclareTargetDeclAttr>() &&
        (FTD->getAttr<ACCDeclareTargetDeclAttr>()->getMapType() ==
         ACCDeclareTargetDeclAttr::MT_Link)) {
      assert(IdLoc.isValid() && "Source location is expected");
      Diag(IdLoc, diag::err_acc_function_in_link_clause);
      Diag(FTD->getLocation(), diag::note_defined_here) << FTD;
      return;
    }
  }
  if (!E) {
    // Checking declaration inside declare target region.
    if (!D->hasAttr<ACCDeclareTargetDeclAttr>() &&
        (isa<VarDecl>(D) || isa<FunctionDecl>(D) ||
         isa<FunctionTemplateDecl>(D))) {
      Attr *A = ACCDeclareTargetDeclAttr::CreateImplicit(
          Context, ACCDeclareTargetDeclAttr::MT_To);
      D->addAttr(A);
      if (ASTMutationListener *ML = Context.getASTMutationListener())
        ML->DeclarationMarkedOpenACCDeclareTarget(D, A);
    }
    return;
  }
  checkDeclInTargetContext(E->getExprLoc(), E->getSourceRange(), *this, D);
}

ACCClause *Sema::ActOnOpenACCToClause(ArrayRef<Expr *> VarList,
                                     SourceLocation StartLoc,
                                     SourceLocation LParenLoc,
                                     SourceLocation EndLoc) {
  MappableVarListInfo MVLI(VarList);
  checkMappableExpressionList(*this, DSAStack, ACCC_to, MVLI, StartLoc);
  if (MVLI.ProcessedVarList.empty())
    return nullptr;

  return ACCToClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                             MVLI.ProcessedVarList, MVLI.VarBaseDeclarations,
                             MVLI.VarComponents);
}

ACCClause *Sema::ActOnOpenACCFromClause(ArrayRef<Expr *> VarList,
                                       SourceLocation StartLoc,
                                       SourceLocation LParenLoc,
                                       SourceLocation EndLoc) {
  MappableVarListInfo MVLI(VarList);
  checkMappableExpressionList(*this, DSAStack, ACCC_from, MVLI, StartLoc);
  if (MVLI.ProcessedVarList.empty())
    return nullptr;

  return ACCFromClause::Create(Context, StartLoc, LParenLoc, EndLoc,
                               MVLI.ProcessedVarList, MVLI.VarBaseDeclarations,
                               MVLI.VarComponents);
}

ACCClause *Sema::ActOnOpenACCUseDevicePtrClause(ArrayRef<Expr *> VarList,
                                               SourceLocation StartLoc,
                                               SourceLocation LParenLoc,
                                               SourceLocation EndLoc) {
  MappableVarListInfo MVLI(VarList);
  SmallVector<Expr *, 8> PrivateCopies;
  SmallVector<Expr *, 8> Inits;

  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC use_device_ptr clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      MVLI.ProcessedVarList.push_back(RefExpr);
      PrivateCopies.push_back(nullptr);
      Inits.push_back(nullptr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    Type = Type.getNonReferenceType().getUnqualifiedType();

    auto *VD = dyn_cast<VarDecl>(D);

    // Item should be a pointer or reference to pointer.
    if (!Type->isPointerType()) {
      Diag(ELoc, diag::err_acc_usedeviceptr_not_a_pointer)
          << 0 << RefExpr->getSourceRange();
      continue;
    }

    // Build the private variable and the expression that refers to it.
    auto VDPrivate = buildVarDecl(*this, ELoc, Type, D->getName(),
                                  D->hasAttrs() ? &D->getAttrs() : nullptr);
    if (VDPrivate->isInvalidDecl())
      continue;

    CurContext->addDecl(VDPrivate);
    auto VDPrivateRefExpr = buildDeclRefExpr(
        *this, VDPrivate, RefExpr->getType().getUnqualifiedType(), ELoc);

    // Add temporary variable to initialize the private copy of the pointer.
    auto *VDInit =
        buildVarDecl(*this, RefExpr->getExprLoc(), Type, ".devptr.temp");
    auto *VDInitRefExpr = buildDeclRefExpr(*this, VDInit, RefExpr->getType(),
                                           RefExpr->getExprLoc());
    AddInitializerToDecl(VDPrivate,
                         DefaultLvalueConversion(VDInitRefExpr).get(),
                         /*DirectInit=*/false);

    // If required, build a capture to implement the privatization initialized
    // with the current list item value.
    DeclRefExpr *Ref = nullptr;
    if (!VD)
      Ref = buildCapture(*this, D, SimpleRefExpr, /*WithInit=*/true);
    MVLI.ProcessedVarList.push_back(VD ? RefExpr->IgnoreParens() : Ref);
    PrivateCopies.push_back(VDPrivateRefExpr);
    Inits.push_back(VDInitRefExpr);

    // We need to add a data sharing attribute for this variable to make sure it
    // is correctly captured. A variable that shows up in a use_device_ptr has
    // similar properties of a first private variable.
    DSAStack->addDSA(D, RefExpr->IgnoreParens(), ACCC_firstprivate, Ref);

    // Create a mappable component for the list item. List items in this clause
    // only need a component.
    MVLI.VarBaseDeclarations.push_back(D);
    MVLI.VarComponents.resize(MVLI.VarComponents.size() + 1);
    MVLI.VarComponents.back().push_back(
        ACCClauseMappableExprCommon::MappableComponent(SimpleRefExpr, D));
  }

  if (MVLI.ProcessedVarList.empty())
    return nullptr;

  return ACCUseDevicePtrClause::Create(
      Context, StartLoc, LParenLoc, EndLoc, MVLI.ProcessedVarList,
      PrivateCopies, Inits, MVLI.VarBaseDeclarations, MVLI.VarComponents);
}

ACCClause *Sema::ActOnOpenACCIsDevicePtrClause(ArrayRef<Expr *> VarList,
                                              SourceLocation StartLoc,
                                              SourceLocation LParenLoc,
                                              SourceLocation EndLoc) {
  MappableVarListInfo MVLI(VarList);
  for (auto &RefExpr : VarList) {
    assert(RefExpr && "NULL expr in OpenACC is_device_ptr clause.");
    SourceLocation ELoc;
    SourceRange ERange;
    Expr *SimpleRefExpr = RefExpr;
    auto Res = getPrivateItem(*this, SimpleRefExpr, ELoc, ERange);
    if (Res.second) {
      // It will be analyzed later.
      MVLI.ProcessedVarList.push_back(RefExpr);
    }
    ValueDecl *D = Res.first;
    if (!D)
      continue;

    QualType Type = D->getType();
    // item should be a pointer or array or reference to pointer or array
    if (!Type.getNonReferenceType()->isPointerType() &&
        !Type.getNonReferenceType()->isArrayType()) {
      Diag(ELoc, diag::err_acc_argument_type_isdeviceptr)
          << 0 << RefExpr->getSourceRange();
      continue;
    }

    // Check if the declaration in the clause does not show up in any data
    // sharing attribute.
    auto DVar = DSAStack->getTopDSA(D, false);
    if (isOpenACCPrivate(DVar.CKind)) {
      Diag(ELoc, diag::err_acc_variable_in_given_clause_and_dsa)
          << getOpenACCClauseName(DVar.CKind)
          << getOpenACCClauseName(ACCC_is_device_ptr)
          << getOpenACCDirectiveName(DSAStack->getCurrentDirective());
      ReportOriginalDSA(*this, DSAStack, D, DVar);
      continue;
    }

    Expr *ConflictExpr;
    if (DSAStack->checkMappableExprComponentListsForDecl(
            D, /*CurrentRegionOnly=*/true,
            [&ConflictExpr](
                ACCClauseMappableExprCommon::MappableExprComponentListRef R,
                OpenACCClauseKind) -> bool {
              ConflictExpr = R.front().getAssociatedExpression();
              return true;
            })) {
      Diag(ELoc, diag::err_acc_map_shared_storage) << RefExpr->getSourceRange();
      Diag(ConflictExpr->getExprLoc(), diag::note_used_here)
          << ConflictExpr->getSourceRange();
      continue;
    }

    // Store the components in the stack so that they can be used to check
    // against other clauses later on.
    ACCClauseMappableExprCommon::MappableComponent MC(SimpleRefExpr, D);
    DSAStack->addMappableExpressionComponents(
        D, MC, /*WhereFoundClauseKind=*/ACCC_is_device_ptr);

    // Record the expression we've just processed.
    MVLI.ProcessedVarList.push_back(SimpleRefExpr);

    // Create a mappable component for the list item. List items in this clause
    // only need a component. We use a null declaration to signal fields in
    // 'this'.
    assert((isa<DeclRefExpr>(SimpleRefExpr) ||
            isa<CXXThisExpr>(cast<MemberExpr>(SimpleRefExpr)->getBase())) &&
           "Unexpected device pointer expression!");
    MVLI.VarBaseDeclarations.push_back(
        isa<DeclRefExpr>(SimpleRefExpr) ? D : nullptr);
    MVLI.VarComponents.resize(MVLI.VarComponents.size() + 1);
    MVLI.VarComponents.back().push_back(MC);
  }

  if (MVLI.ProcessedVarList.empty())
    return nullptr;

  return ACCIsDevicePtrClause::Create(
      Context, StartLoc, LParenLoc, EndLoc, MVLI.ProcessedVarList,
      MVLI.VarBaseDeclarations, MVLI.VarComponents);
}
