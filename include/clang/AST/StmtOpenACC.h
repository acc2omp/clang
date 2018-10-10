//===- StmtOpenACC.h - Classes for OpenACC directives  ------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file defines OpenACC AST classes for executable directives and
/// clauses.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_STMTOPENACC_H
#define LLVM_CLANG_AST_STMTOPENACC_H

#include "clang/AST/Expr.h"
#include "clang/AST/OpenACCClause.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/OpenACCKinds.h"
#include "clang/Basic/SourceLocation.h"

namespace clang {

//===----------------------------------------------------------------------===//
// AST classes for directives.
//===----------------------------------------------------------------------===//

/// \brief This is a basic class for representing single OpenACC executable
/// directive.
///
class ACCExecutableDirective : public Stmt {
  friend class ASTStmtReader;
  /// \brief Kind of the directive.
  OpenACCDirectiveKind Kind;
  /// \brief Starting location of the directive (directive keyword).
  SourceLocation StartLoc;
  /// \brief Ending location of the directive.
  SourceLocation EndLoc;
  /// \brief Numbers of clauses.
  const unsigned NumClauses;
  /// \brief Number of child expressions/stmts.
  const unsigned NumChildren;
  /// \brief Offset from this to the start of clauses.
  /// There are NumClauses pointers to clauses, they are followed by
  /// NumChildren pointers to child stmts/exprs (if the directive type
  /// requires an associated stmt, then it has to be the first of them).
  const unsigned ClausesOffset;

  /// \brief Get the clauses storage.
  MutableArrayRef<ACCClause *> getClauses() {
    ACCClause **ClauseStorage = reinterpret_cast<ACCClause **>(
        reinterpret_cast<char *>(this) + ClausesOffset);
    return MutableArrayRef<ACCClause *>(ClauseStorage, NumClauses);
  }

protected:
  /// \brief Build instance of directive of class \a K.
  ///
  /// \param SC Statement class.
  /// \param K Kind of OpenACC directive.
  /// \param StartLoc Starting location of the directive (directive keyword).
  /// \param EndLoc Ending location of the directive.
  ///
  template <typename T>
  ACCExecutableDirective(const T *, StmtClass SC, OpenACCDirectiveKind K,
                         SourceLocation StartLoc, SourceLocation EndLoc,
                         unsigned NumClauses, unsigned NumChildren)
      : Stmt(SC), Kind(K), StartLoc(std::move(StartLoc)),
        EndLoc(std::move(EndLoc)), NumClauses(NumClauses),
        NumChildren(NumChildren),
        ClausesOffset(llvm::alignTo(sizeof(T), alignof(ACCClause *))) {}

  /// \brief Sets the list of variables for this clause.
  ///
  /// \param Clauses The list of clauses for the directive.
  ///
  void setClauses(ArrayRef<ACCClause *> Clauses);

  /// \brief Set the associated statement for the directive.
  ///
  /// /param S Associated statement.
  ///
  void setAssociatedStmt(Stmt *S) {
    assert(hasAssociatedStmt() && "no associated statement.");
    *child_begin() = S;
  }

public:
  /// \brief Iterates over a filtered subrange of clauses applied to a
  /// directive.
  ///
  /// This iterator visits only clauses of type SpecificClause.
  template <typename SpecificClause>
  class specific_clause_iterator
      : public llvm::iterator_adaptor_base<
            specific_clause_iterator<SpecificClause>,
            ArrayRef<ACCClause *>::const_iterator, std::forward_iterator_tag,
            const SpecificClause *, ptrdiff_t, const SpecificClause *,
            const SpecificClause *> {
    ArrayRef<ACCClause *>::const_iterator End;

    void SkipToNextClause() {
      while (this->I != End && !isa<SpecificClause>(*this->I))
        ++this->I;
    }

  public:
    explicit specific_clause_iterator(ArrayRef<ACCClause *> Clauses)
        : specific_clause_iterator::iterator_adaptor_base(Clauses.begin()),
          End(Clauses.end()) {
      SkipToNextClause();
    }

    const SpecificClause *operator*() const {
      return cast<SpecificClause>(*this->I);
    }
    const SpecificClause *operator->() const { return **this; }

    specific_clause_iterator &operator++() {
      ++this->I;
      SkipToNextClause();
      return *this;
    }
  };

  template <typename SpecificClause>
  static llvm::iterator_range<specific_clause_iterator<SpecificClause>>
  getClausesOfKind(ArrayRef<ACCClause *> Clauses) {
    return {specific_clause_iterator<SpecificClause>(Clauses),
            specific_clause_iterator<SpecificClause>(
                llvm::makeArrayRef(Clauses.end(), 0))};
  }

  template <typename SpecificClause>
  llvm::iterator_range<specific_clause_iterator<SpecificClause>>
  getClausesOfKind() const {
    return getClausesOfKind<SpecificClause>(clauses());
  }

  /// Gets a single clause of the specified kind associated with the
  /// current directive iff there is only one clause of this kind (and assertion
  /// is fired if there is more than one clause is associated with the
  /// directive). Returns nullptr if no clause of this kind is associated with
  /// the directive.
  template <typename SpecificClause>
  const SpecificClause *getSingleClause() const {
    auto Clauses = getClausesOfKind<SpecificClause>();

    if (Clauses.begin() != Clauses.end()) {
      assert(std::next(Clauses.begin()) == Clauses.end() &&
             "There are at least 2 clauses of the specified kind");
      return *Clauses.begin();
    }
    return nullptr;
  }

  /// Returns true if the current directive has one or more clauses of a
  /// specific kind.
  template <typename SpecificClause>
  bool hasClausesOfKind() const {
    auto Clauses = getClausesOfKind<SpecificClause>();
    return Clauses.begin() != Clauses.end();
  }

  /// \brief Returns starting location of directive kind.
  SourceLocation getLocStart() const { return StartLoc; }
  /// \brief Returns ending location of directive.
  SourceLocation getLocEnd() const { return EndLoc; }

  /// \brief Set starting location of directive kind.
  ///
  /// \param Loc New starting location of directive.
  ///
  void setLocStart(SourceLocation Loc) { StartLoc = Loc; }
  /// \brief Set ending location of directive.
  ///
  /// \param Loc New ending location of directive.
  ///
  void setLocEnd(SourceLocation Loc) { EndLoc = Loc; }

  /// \brief Get number of clauses.
  unsigned getNumClauses() const { return NumClauses; }

  /// \brief Returns specified clause.
  ///
  /// \param i Number of clause.
  ///
  ACCClause *getClause(unsigned i) const { return clauses()[i]; }

  /// \brief Returns true if directive has associated statement.
  bool hasAssociatedStmt() const { return NumChildren > 0; }

  /// \brief Returns statement associated with the directive.
  const Stmt *getAssociatedStmt() const {
    assert(hasAssociatedStmt() && "no associated statement.");
    return *child_begin();
  }
  Stmt *getAssociatedStmt() {
    assert(hasAssociatedStmt() && "no associated statement.");
    return *child_begin();
  }

  /// \brief Returns the captured statement associated with the
  /// component region within the (combined) directive.
  //
  // \param RegionKind Component region kind.
  const CapturedStmt *getCapturedStmt(OpenACCDirectiveKind RegionKind) const {
    SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
    getOpenACCCaptureRegions(CaptureRegions, getDirectiveKind());
    assert(std::any_of(
               CaptureRegions.begin(), CaptureRegions.end(),
               [=](const OpenACCDirectiveKind K) { return K == RegionKind; }) &&
           "RegionKind not found in OpenACC CaptureRegions.");
    auto *CS = cast<CapturedStmt>(getAssociatedStmt());
    for (auto ThisCaptureRegion : CaptureRegions) {
      if (ThisCaptureRegion == RegionKind)
        return CS;
      CS = cast<CapturedStmt>(CS->getCapturedStmt());
    }
    llvm_unreachable("Incorrect RegionKind specified for directive.");
  }

  /// Get innermost captured statement for the construct.
  CapturedStmt *getInnermostCapturedStmt() {
    assert(hasAssociatedStmt() && getAssociatedStmt() &&
           "Must have associated statement.");
    SmallVector<OpenACCDirectiveKind, 4> CaptureRegions;
    getOpenACCCaptureRegions(CaptureRegions, getDirectiveKind());
    assert(!CaptureRegions.empty() &&
           "At least one captured statement must be provided.");
    auto *CS = cast<CapturedStmt>(getAssociatedStmt());
    for (unsigned Level = CaptureRegions.size(); Level > 1; --Level)
      CS = cast<CapturedStmt>(CS->getCapturedStmt());
    return CS;
  }

  const CapturedStmt *getInnermostCapturedStmt() const {
    return const_cast<ACCExecutableDirective *>(this)
        ->getInnermostCapturedStmt();
  }

  OpenACCDirectiveKind getDirectiveKind() const { return Kind; }

  static bool classof(const Stmt *S) {
     return S->getStmtClass() >= firstACCExecutableDirectiveConstant &&
           S->getStmtClass() <= lastACCExecutableDirectiveConstant;
  }

  child_range children() {
    if (!hasAssociatedStmt())
      return child_range(child_iterator(), child_iterator());
    Stmt **ChildStorage = reinterpret_cast<Stmt **>(getClauses().end());
    return child_range(ChildStorage, ChildStorage + NumChildren);
  }

  ArrayRef<ACCClause *> clauses() { return getClauses(); }

  ArrayRef<ACCClause *> clauses() const {
    return const_cast<ACCExecutableDirective *>(this)->getClauses();
  }
};

/// \brief This represents '#pragma acc parallel' directive.
///
/// \code
/// #pragma acc parallel private(a,b) reduction(+: c,d)
/// \endcode
/// In this example directive '#pragma acc parallel' has clauses 'private'
/// with the variables 'a' and 'b' and 'reduction' with operator '+' and
/// variables 'c' and 'd'.
///
class ACCParallelDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief true if the construct has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive (directive keyword).
  /// \param EndLoc Ending Location of the directive.
  ///
  ACCParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                       unsigned NumClauses)
      : ACCExecutableDirective(this, ACCParallelDirectiveClass, ACCD_parallel,
                               StartLoc, EndLoc, NumClauses, 1),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCParallelDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCParallelDirectiveClass, ACCD_parallel,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement associated with the directive.
  /// \param HasCancel true if this directive has inner cancel directive.
  ///
  static ACCParallelDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);

  /// \brief Creates an empty directive with the place for \a N clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCParallelDirective *CreateEmpty(const ASTContext &C,
                                           unsigned NumClauses, EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCParallelDirectiveClass;
  }
};

/// \brief This is a common base class for loop like directives ('acc simd', 'acc
/// loop', 'acc loop simd' etc.). It is responsible for the loop code generation.
///
class ACCLoopLikeDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Number of collapsed loops as specified by 'collapse' clause.
  unsigned CollapsedNum;

  /// \brief Offsets to the stored exprs.
  /// This enumeration contains offsets to all the pointers to children
  /// expressions stored in ACCLoopLikeDirective.
  /// The first 9 children are necessary for all the loop directives,
  /// the next 8 are specific to the worksharing ones, and the next 11 are
  /// used for combined constructs containing two pragmas associated to loops.
  /// After the fixed children, three arrays of length CollapsedNum are
  /// allocated: loop counters, their updates and final values.
  /// PrevLowerBound and PrevUpperBound are used to communicate blocking
  /// information in composite constructs which require loop blocking
  /// DistInc is used to generate the increment expression for the distribute
  /// loop when combined with a further nested loop
  /// PrevEnsureUpperBound is used as the EnsureUpperBound expression for the
  /// for loop when combined with a previous distribute loop in the same pragma
  /// (e.g. 'distribute parallel loop')
  ///
  enum {
    AssociatedStmtOffset = 0,
    IterationVariableOffset = 1,
    LastIterationOffset = 2,
    CalcLastIterationOffset = 3,
    PreConditionOffset = 4,
    CondOffset = 5,
    InitOffset = 6,
    IncOffset = 7,
    PreInitsOffset = 8,
    // The '...End' enumerators do not correspond to child expressions - they
    // specify the offset to the end (and start of the following counters/
    // updates/finals arrays).
    DefaultEnd = 9,
    // The following 8 exprs are used by worksharing and distribute loops only.
    IsLastIterVariableOffset = 9,
    LowerBoundVariableOffset = 10,
    UpperBoundVariableOffset = 11,
    StrideVariableOffset = 12,
    EnsureUpperBoundOffset = 13,
    NextLowerBoundOffset = 14,
    NextUpperBoundOffset = 15,
    NumIterationsOffset = 16,
    // Offset to the end for worksharing loop directives.
    WorksharingEnd = 17,
    PrevLowerBoundVariableOffset = 17,
    PrevUpperBoundVariableOffset = 18,
    DistIncOffset = 19,
    PrevEnsureUpperBoundOffset = 20,
    CombinedLowerBoundVariableOffset = 21,
    CombinedUpperBoundVariableOffset = 22,
    CombinedEnsureUpperBoundOffset = 23,
    CombinedInitOffset = 24,
    CombinedConditionOffset = 25,
    CombinedNextLowerBoundOffset = 26,
    CombinedNextUpperBoundOffset = 27,
    // Offset to the end (and start of the following counters/updates/finals
    // arrays) for combined distribute loop directives.
    CombinedDistributeEnd = 28,
  };

  /// \brief Get the counters storage.
  MutableArrayRef<Expr *> getCounters() {
    Expr **Storage = reinterpret_cast<Expr **>(
        &(*(std::next(child_begin(), getArraysOffset(getDirectiveKind())))));
    return MutableArrayRef<Expr *>(Storage, CollapsedNum);
  }

  /// \brief Get the private counters storage.
  MutableArrayRef<Expr *> getPrivateCounters() {
    Expr **Storage = reinterpret_cast<Expr **>(&*std::next(
        child_begin(), getArraysOffset(getDirectiveKind()) + CollapsedNum));
    return MutableArrayRef<Expr *>(Storage, CollapsedNum);
  }

  /// \brief Get the updates storage.
  MutableArrayRef<Expr *> getInits() {
    Expr **Storage = reinterpret_cast<Expr **>(
        &*std::next(child_begin(),
                    getArraysOffset(getDirectiveKind()) + 2 * CollapsedNum));
    return MutableArrayRef<Expr *>(Storage, CollapsedNum);
  }

  /// \brief Get the updates storage.
  MutableArrayRef<Expr *> getUpdates() {
    Expr **Storage = reinterpret_cast<Expr **>(
        &*std::next(child_begin(),
                    getArraysOffset(getDirectiveKind()) + 3 * CollapsedNum));
    return MutableArrayRef<Expr *>(Storage, CollapsedNum);
  }

  /// \brief Get the final counter updates storage.
  MutableArrayRef<Expr *> getFinals() {
    Expr **Storage = reinterpret_cast<Expr **>(
        &*std::next(child_begin(),
                    getArraysOffset(getDirectiveKind()) + 4 * CollapsedNum));
    return MutableArrayRef<Expr *>(Storage, CollapsedNum);
  }

protected:
  /// \brief Build instance of loop directive of class \a Kind.
  ///
  /// \param SC Statement class.
  /// \param Kind Kind of OpenACC directive.
  /// \param StartLoc Starting location of the directive (directive keyword).
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed loops from 'collapse' clause.
  /// \param NumClauses Number of clauses.
  /// \param NumSpecialChildren Number of additional directive-specific stmts.
  ///
  template <typename T>
  ACCLoopLikeDirective(const T *That, StmtClass SC, OpenACCDirectiveKind Kind,
                   SourceLocation StartLoc, SourceLocation EndLoc,
                   unsigned CollapsedNum, unsigned NumClauses,
                   unsigned NumSpecialChildren = 0)
      : ACCExecutableDirective(That, SC, Kind, StartLoc, EndLoc, NumClauses,
                               numLoopChildren(CollapsedNum, Kind) +
                                   NumSpecialChildren),
        CollapsedNum(CollapsedNum) {}

  /// \brief Offset to the start of children expression arrays.
  static unsigned getArraysOffset(OpenACCDirectiveKind Kind) {
    if (isOpenACCLoopBoundSharingDirective(Kind))
      return CombinedDistributeEnd;
    if (isOpenACCWorksharingDirective(Kind) || isOpenACCTaskLoopDirective(Kind) ||
        isOpenACCDistributeDirective(Kind))
      return WorksharingEnd;
    return DefaultEnd;
  }

  /// \brief Children number.
  static unsigned numLoopChildren(unsigned CollapsedNum,
                                  OpenACCDirectiveKind Kind) {
    return getArraysOffset(Kind) + 5 * CollapsedNum; // Counters,
                                                     // PrivateCounters, Inits,
                                                     // Updates and Finals
  }

  void setIterationVariable(Expr *IV) {
    *std::next(child_begin(), IterationVariableOffset) = IV;
  }
  void setLastIteration(Expr *LI) {
    *std::next(child_begin(), LastIterationOffset) = LI;
  }
  void setCalcLastIteration(Expr *CLI) {
    *std::next(child_begin(), CalcLastIterationOffset) = CLI;
  }
  void setPreCond(Expr *PC) {
    *std::next(child_begin(), PreConditionOffset) = PC;
  }
  void setCond(Expr *Cond) {
    *std::next(child_begin(), CondOffset) = Cond;
  }
  void setInit(Expr *Init) { *std::next(child_begin(), InitOffset) = Init; }
  void setInc(Expr *Inc) { *std::next(child_begin(), IncOffset) = Inc; }
  void setPreInits(Stmt *PreInits) {
    *std::next(child_begin(), PreInitsOffset) = PreInits;
  }
  void setIsLastIterVariable(Expr *IL) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), IsLastIterVariableOffset) = IL;
  }
  void setLowerBoundVariable(Expr *LB) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), LowerBoundVariableOffset) = LB;
  }
  void setUpperBoundVariable(Expr *UB) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), UpperBoundVariableOffset) = UB;
  }
  void setStrideVariable(Expr *ST) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), StrideVariableOffset) = ST;
  }
  void setEnsureUpperBound(Expr *EUB) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), EnsureUpperBoundOffset) = EUB;
  }
  void setNextLowerBound(Expr *NLB) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), NextLowerBoundOffset) = NLB;
  }
  void setNextUpperBound(Expr *NUB) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), NextUpperBoundOffset) = NUB;
  }
  void setNumIterations(Expr *NI) {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    *std::next(child_begin(), NumIterationsOffset) = NI;
  }
  void setPrevLowerBoundVariable(Expr *PrevLB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), PrevLowerBoundVariableOffset) = PrevLB;
  }
  void setPrevUpperBoundVariable(Expr *PrevUB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), PrevUpperBoundVariableOffset) = PrevUB;
  }
  void setDistInc(Expr *DistInc) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), DistIncOffset) = DistInc;
  }
  void setPrevEnsureUpperBound(Expr *PrevEUB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), PrevEnsureUpperBoundOffset) = PrevEUB;
  }
  void setCombinedLowerBoundVariable(Expr *CombLB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedLowerBoundVariableOffset) = CombLB;
  }
  void setCombinedUpperBoundVariable(Expr *CombUB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedUpperBoundVariableOffset) = CombUB;
  }
  void setCombinedEnsureUpperBound(Expr *CombEUB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedEnsureUpperBoundOffset) = CombEUB;
  }
  void setCombinedInit(Expr *CombInit) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedInitOffset) = CombInit;
  }
  void setCombinedCond(Expr *CombCond) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedConditionOffset) = CombCond;
  }
  void setCombinedNextLowerBound(Expr *CombNLB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedNextLowerBoundOffset) = CombNLB;
  }
  void setCombinedNextUpperBound(Expr *CombNUB) {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    *std::next(child_begin(), CombinedNextUpperBoundOffset) = CombNUB;
  }
  void setCounters(ArrayRef<Expr *> A);
  void setPrivateCounters(ArrayRef<Expr *> A);
  void setInits(ArrayRef<Expr *> A);
  void setUpdates(ArrayRef<Expr *> A);
  void setFinals(ArrayRef<Expr *> A);

public:
  /// The expressions built to support OpenACC loops in combined/composite
  /// pragmas (e.g. pragma acc distribute parallel loop)
  struct DistCombinedHelperExprs {
    /// DistributeLowerBound - used when composing 'acc distribute' with
    /// 'acc loop' in a same construct.
    Expr *LB;
    /// DistributeUpperBound - used when composing 'acc distribute' with
    /// 'acc loop' in a same construct.
    Expr *UB;
    /// DistributeEnsureUpperBound - used when composing 'acc distribute'
    ///  with 'acc loop' in a same construct, EUB depends on DistUB
    Expr *EUB;
    /// Distribute loop iteration variable init used when composing 'acc
    /// distribute'
    ///  with 'acc loop' in a same construct
    Expr *Init;
    /// Distribute Loop condition used when composing 'acc distribute'
    ///  with 'acc loop' in a same construct
    Expr *Cond;
    /// Update of LowerBound for statically sheduled acc loops for
    /// outer loop in combined constructs (e.g. 'distribute parallel loop')
    Expr *NLB;
    /// Update of UpperBound for statically sheduled acc loops for
    /// outer loop in combined constructs (e.g. 'distribute parallel loop')
    Expr *NUB;
  };

  /// \brief The expressions built for the OpenACC loop CodeGen for the
  /// whole collapsed loop nest.
  struct HelperExprs {
    /// \brief Loop iteration variable.
    Expr *IterationVarRef;
    /// \brief Loop last iteration number.
    Expr *LastIteration;
    /// \brief Loop number of iterations.
    Expr *NumIterations;
    /// \brief Calculation of last iteration.
    Expr *CalcLastIteration;
    /// \brief Loop pre-condition.
    Expr *PreCond;
    /// \brief Loop condition.
    Expr *Cond;
    /// \brief Loop iteration variable init.
    Expr *Init;
    /// \brief Loop increment.
    Expr *Inc;
    /// \brief IsLastIteration - local flag variable passed to runtime.
    Expr *IL;
    /// \brief LowerBound - local variable passed to runtime.
    Expr *LB;
    /// \brief UpperBound - local variable passed to runtime.
    Expr *UB;
    /// \brief Stride - local variable passed to runtime.
    Expr *ST;
    /// \brief EnsureUpperBound -- expression UB = min(UB, NumIterations).
    Expr *EUB;
    /// \brief Update of LowerBound for statically sheduled 'acc loop' loops.
    Expr *NLB;
    /// \brief Update of UpperBound for statically sheduled 'acc loop' loops.
    Expr *NUB;
    /// \brief PreviousLowerBound - local variable passed to runtime in the
    /// enclosing schedule or null if that does not apply.
    Expr *PrevLB;
    /// \brief PreviousUpperBound - local variable passed to runtime in the
    /// enclosing schedule or null if that does not apply.
    Expr *PrevUB;
    /// \brief DistInc - increment expression for distribute loop when found
    /// combined with a further loop level (e.g. in 'distribute parallel loop')
    /// expression IV = IV + ST
    Expr *DistInc;
    /// \brief PrevEUB - expression similar to EUB but to be used when loop
    /// scheduling uses PrevLB and PrevUB (e.g.  in 'distribute parallel loop'
    /// when ensuring that the UB is either the calculated UB by the runtime or
    /// the end of the assigned distribute chunk)
    /// expression UB = min (UB, PrevUB)
    Expr *PrevEUB;
    /// \brief Counters Loop counters.
    SmallVector<Expr *, 4> Counters;
    /// \brief PrivateCounters Loop counters.
    SmallVector<Expr *, 4> PrivateCounters;
    /// \brief Expressions for loop counters inits for CodeGen.
    SmallVector<Expr *, 4> Inits;
    /// \brief Expressions for loop counters update for CodeGen.
    SmallVector<Expr *, 4> Updates;
    /// \brief Final loop counter values for GodeGen.
    SmallVector<Expr *, 4> Finals;
    /// Init statement for all captured expressions.
    Stmt *PreInits;

    /// Expressions used when combining OpenACC loop pragmas
    DistCombinedHelperExprs DistCombinedFields;

    /// \brief Check if all the expressions are built (does not check the
    /// worksharing ones).
    bool builtAll() {
      return IterationVarRef != nullptr && LastIteration != nullptr &&
             NumIterations != nullptr && PreCond != nullptr &&
             Cond != nullptr && Init != nullptr && Inc != nullptr;
    }

    /// \brief Initialize all the fields to null.
    /// \param Size Number of elements in the counters/finals/updates arrays.
    void clear(unsigned Size) {
      IterationVarRef = nullptr;
      LastIteration = nullptr;
      CalcLastIteration = nullptr;
      PreCond = nullptr;
      Cond = nullptr;
      Init = nullptr;
      Inc = nullptr;
      IL = nullptr;
      LB = nullptr;
      UB = nullptr;
      ST = nullptr;
      EUB = nullptr;
      NLB = nullptr;
      NUB = nullptr;
      NumIterations = nullptr;
      PrevLB = nullptr;
      PrevUB = nullptr;
      DistInc = nullptr;
      PrevEUB = nullptr;
      Counters.resize(Size);
      PrivateCounters.resize(Size);
      Inits.resize(Size);
      Updates.resize(Size);
      Finals.resize(Size);
      for (unsigned i = 0; i < Size; ++i) {
        Counters[i] = nullptr;
        PrivateCounters[i] = nullptr;
        Inits[i] = nullptr;
        Updates[i] = nullptr;
        Finals[i] = nullptr;
      }
      PreInits = nullptr;
      DistCombinedFields.LB = nullptr;
      DistCombinedFields.UB = nullptr;
      DistCombinedFields.EUB = nullptr;
      DistCombinedFields.Init = nullptr;
      DistCombinedFields.Cond = nullptr;
      DistCombinedFields.NLB = nullptr;
      DistCombinedFields.NUB = nullptr;
    }
  };

  /// \brief Get number of collapsed loops.
  unsigned getCollapsedNumber() const { return CollapsedNum; }

  Expr *getIterationVariable() const {
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), IterationVariableOffset)));
  }
  Expr *getLastIteration() const {
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), LastIterationOffset)));
  }
  Expr *getCalcLastIteration() const {
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CalcLastIterationOffset)));
  }
  Expr *getPreCond() const {
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), PreConditionOffset)));
  }
  Expr *getCond() const {
    return const_cast<Expr *>(
        reinterpret_cast<const Expr *>(*std::next(child_begin(), CondOffset)));
  }
  Expr *getInit() const {
    return const_cast<Expr *>(
        reinterpret_cast<const Expr *>(*std::next(child_begin(), InitOffset)));
  }
  Expr *getInc() const {
    return const_cast<Expr *>(
        reinterpret_cast<const Expr *>(*std::next(child_begin(), IncOffset)));
  }
  const Stmt *getPreInits() const {
    return *std::next(child_begin(), PreInitsOffset);
  }
  Stmt *getPreInits() { return *std::next(child_begin(), PreInitsOffset); }
  Expr *getIsLastIterVariable() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), IsLastIterVariableOffset)));
  }
  Expr *getLowerBoundVariable() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), LowerBoundVariableOffset)));
  }
  Expr *getUpperBoundVariable() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), UpperBoundVariableOffset)));
  }
  Expr *getStrideVariable() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), StrideVariableOffset)));
  }
  Expr *getEnsureUpperBound() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), EnsureUpperBoundOffset)));
  }
  Expr *getNextLowerBound() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), NextLowerBoundOffset)));
  }
  Expr *getNextUpperBound() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), NextUpperBoundOffset)));
  }
  Expr *getNumIterations() const {
    assert((isOpenACCWorksharingDirective(getDirectiveKind()) ||
            isOpenACCTaskLoopDirective(getDirectiveKind()) ||
            isOpenACCDistributeDirective(getDirectiveKind())) &&
           "expected worksharing loop directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), NumIterationsOffset)));
  }
  Expr *getPrevLowerBoundVariable() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), PrevLowerBoundVariableOffset)));
  }
  Expr *getPrevUpperBoundVariable() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), PrevUpperBoundVariableOffset)));
  }
  Expr *getDistInc() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), DistIncOffset)));
  }
  Expr *getPrevEnsureUpperBound() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), PrevEnsureUpperBoundOffset)));
  }
  Expr *getCombinedLowerBoundVariable() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedLowerBoundVariableOffset)));
  }
  Expr *getCombinedUpperBoundVariable() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedUpperBoundVariableOffset)));
  }
  Expr *getCombinedEnsureUpperBound() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedEnsureUpperBoundOffset)));
  }
  Expr *getCombinedInit() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedInitOffset)));
  }
  Expr *getCombinedCond() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedConditionOffset)));
  }
  Expr *getCombinedNextLowerBound() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedNextLowerBoundOffset)));
  }
  Expr *getCombinedNextUpperBound() const {
    assert(isOpenACCLoopBoundSharingDirective(getDirectiveKind()) &&
           "expected loop bound sharing directive");
    return const_cast<Expr *>(reinterpret_cast<const Expr *>(
        *std::next(child_begin(), CombinedNextUpperBoundOffset)));
  }
  const Stmt *getBody() const {
    // This relies on the loop form is already checked by Sema.
    const Stmt *Body =
        getInnermostCapturedStmt()->getCapturedStmt()->IgnoreContainers();
    Body = cast<ForStmt>(Body)->getBody();
    for (unsigned Cnt = 1; Cnt < CollapsedNum; ++Cnt) {
      Body = Body->IgnoreContainers();
      Body = cast<ForStmt>(Body)->getBody();
    }
    return Body;
  }

  ArrayRef<Expr *> counters() { return getCounters(); }

  ArrayRef<Expr *> counters() const {
    return const_cast<ACCLoopLikeDirective *>(this)->getCounters();
  }

  ArrayRef<Expr *> private_counters() { return getPrivateCounters(); }

  ArrayRef<Expr *> private_counters() const {
    return const_cast<ACCLoopLikeDirective *>(this)->getPrivateCounters();
  }

  ArrayRef<Expr *> inits() { return getInits(); }

  ArrayRef<Expr *> inits() const {
    return const_cast<ACCLoopLikeDirective *>(this)->getInits();
  }

  ArrayRef<Expr *> updates() { return getUpdates(); }

  ArrayRef<Expr *> updates() const {
    return const_cast<ACCLoopLikeDirective *>(this)->getUpdates();
  }

  ArrayRef<Expr *> finals() { return getFinals(); }

  ArrayRef<Expr *> finals() const {
    return const_cast<ACCLoopLikeDirective *>(this)->getFinals();
  }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCVectorDirectiveClass ||
           T->getStmtClass() == ACCLoopDirectiveClass ||
           T->getStmtClass() == ACCLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCParallelLoopDirectiveClass ||
           T->getStmtClass() == ACCParallelLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCTaskLoopDirectiveClass ||
           T->getStmtClass() == ACCTaskLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCDistributeDirectiveClass ||
           T->getStmtClass() == ACCTargetParallelLoopDirectiveClass ||
           T->getStmtClass() == ACCDistributeParallelLoopDirectiveClass ||
           T->getStmtClass() == ACCDistributeParallelLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCDistributeVectorDirectiveClass ||
           T->getStmtClass() == ACCTargetParallelLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCTargetVectorDirectiveClass ||
           T->getStmtClass() == ACCTeamsDistributeDirectiveClass ||
           T->getStmtClass() == ACCTeamsDistributeVectorDirectiveClass ||
           T->getStmtClass() ==
               ACCTeamsDistributeParallelLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCTeamsDistributeParallelLoopDirectiveClass ||
           T->getStmtClass() ==
               ACCTargetTeamsDistributeParallelLoopDirectiveClass ||
           T->getStmtClass() ==
               ACCTargetTeamsDistributeParallelLoopVectorDirectiveClass ||
           T->getStmtClass() == ACCTargetTeamsDistributeDirectiveClass ||
           T->getStmtClass() == ACCTargetTeamsDistributeVectorDirectiveClass;
  }
};

/// \brief This represents '#pragma acc simd' directive.
///
/// \code
/// #pragma acc simd private(a,b) linear(i,j:s) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc simd' has clauses 'private'
/// with the variables 'a' and 'b', 'linear' with variables 'i', 'j' and
/// linear step 's', 'reduction' with operator '+' and variables 'c' and 'd'.
///
class ACCVectorDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                   unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCVectorDirectiveClass, ACCD_vector, StartLoc,
                         EndLoc, CollapsedNum, NumClauses) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCVectorDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCVectorDirectiveClass, ACCD_vector,
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCVectorDirective *Create(const ASTContext &C, SourceLocation StartLoc,
                                  SourceLocation EndLoc, unsigned CollapsedNum,
                                  ArrayRef<ACCClause *> Clauses,
                                  Stmt *AssociatedStmt,
                                  const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCVectorDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                       unsigned CollapsedNum, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCVectorDirectiveClass;
  }
};

/// \brief This represents '#pragma acc loop' directive.
///
/// \code
/// #pragma acc loopprivate(a,b) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc loop' has clauses 'private' with the
/// variables 'a' and 'b' and 'reduction' with operator '+' and variables 'c'
/// and 'd'.
///
class ACCLoopDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// \brief true if current directive has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                  unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCLoopDirectiveClass, ACCD_loop, StartLoc, EndLoc,
                         CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCLoopDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCLoopDirectiveClass, ACCD_loop, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if current directive has inner cancel directive.
  ///
  static ACCLoopDirective *Create(const ASTContext &C, SourceLocation StartLoc,
                                 SourceLocation EndLoc, unsigned CollapsedNum,
                                 ArrayRef<ACCClause *> Clauses,
                                 Stmt *AssociatedStmt, const HelperExprs &Exprs,
                                 bool HasCancel);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCLoopDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                      unsigned CollapsedNum, EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCLoopDirectiveClass;
  }
};

/// \brief This represents '#pragma acc loop simd' directive.
///
/// \code
/// #pragma acc loop simd private(a,b) linear(i,j:s) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc loop simd' has clauses 'private'
/// with the variables 'a' and 'b', 'linear' with variables 'i', 'j' and
/// linear step 's', 'reduction' with operator '+' and variables 'c' and 'd'.
///
class ACCLoopVectorDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCLoopVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                      unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCLoopVectorDirectiveClass, ACCD_loop_vector,
                         StartLoc, EndLoc, CollapsedNum, NumClauses) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCLoopVectorDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCLoopVectorDirectiveClass, ACCD_loop_vector,
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCLoopVectorDirective *CreateEmpty(const ASTContext &C,
                                          unsigned NumClauses,
                                          unsigned CollapsedNum, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCLoopVectorDirectiveClass;
  }
};

/// \brief This represents '#pragma acc sections' directive.
///
/// \code
/// #pragma acc sections private(a,b) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc sections' has clauses 'private' with
/// the variables 'a' and 'b' and 'reduction' with operator '+' and variables
/// 'c' and 'd'.
///
class ACCSectionsDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;

  /// \brief true if current directive has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                       unsigned NumClauses)
      : ACCExecutableDirective(this, ACCSectionsDirectiveClass, ACCD_sections,
                               StartLoc, EndLoc, NumClauses, 1),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCSectionsDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCSectionsDirectiveClass, ACCD_sections,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param HasCancel true if current directive has inner directive.
  ///
  static ACCSectionsDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCSectionsDirective *CreateEmpty(const ASTContext &C,
                                           unsigned NumClauses, EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCSectionsDirectiveClass;
  }
};

/// \brief This represents '#pragma acc section' directive.
///
/// \code
/// #pragma acc section
/// \endcode
///
class ACCSectionDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;

  /// \brief true if current directive has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCSectionDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCSectionDirectiveClass, ACCD_section,
                               StartLoc, EndLoc, 0, 1),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCSectionDirective()
      : ACCExecutableDirective(this, ACCSectionDirectiveClass, ACCD_section,
                               SourceLocation(), SourceLocation(), 0, 1),
        HasCancel(false) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param HasCancel true if current directive has inner directive.
  ///
  static ACCSectionDirective *Create(const ASTContext &C,
                                     SourceLocation StartLoc,
                                     SourceLocation EndLoc,
                                     Stmt *AssociatedStmt, bool HasCancel);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCSectionDirective *CreateEmpty(const ASTContext &C, EmptyShell);

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCSectionDirectiveClass;
  }
};

/// \brief This represents '#pragma acc single' directive.
///
/// \code
/// #pragma acc single private(a,b) copyprivate(c,d)
/// \endcode
/// In this example directive '#pragma acc single' has clauses 'private' with
/// the variables 'a' and 'b' and 'copyprivate' with variables 'c' and 'd'.
///
class ACCSingleDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCSingleDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                     unsigned NumClauses)
      : ACCExecutableDirective(this, ACCSingleDirectiveClass, ACCD_single,
                               StartLoc, EndLoc, NumClauses, 1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCSingleDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCSingleDirectiveClass, ACCD_single,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCSingleDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCSingleDirective *CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCSingleDirectiveClass;
  }
};

/// \brief This represents '#pragma acc master' directive.
///
/// \code
/// #pragma acc master
/// \endcode
///
class ACCMasterDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCMasterDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCMasterDirectiveClass, ACCD_master,
                               StartLoc, EndLoc, 0, 1) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCMasterDirective()
      : ACCExecutableDirective(this, ACCMasterDirectiveClass, ACCD_master,
                               SourceLocation(), SourceLocation(), 0, 1) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCMasterDirective *Create(const ASTContext &C,
                                    SourceLocation StartLoc,
                                    SourceLocation EndLoc,
                                    Stmt *AssociatedStmt);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCMasterDirective *CreateEmpty(const ASTContext &C, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCMasterDirectiveClass;
  }
};

/// \brief This represents '#pragma acc critical' directive.
///
/// \code
/// #pragma acc critical
/// \endcode
///
class ACCCriticalDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Name of the directive.
  DeclarationNameInfo DirName;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param Name Name of the directive.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCCriticalDirective(const DeclarationNameInfo &Name, SourceLocation StartLoc,
                       SourceLocation EndLoc, unsigned NumClauses)
      : ACCExecutableDirective(this, ACCCriticalDirectiveClass, ACCD_critical,
                               StartLoc, EndLoc, NumClauses, 1),
        DirName(Name) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCCriticalDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCCriticalDirectiveClass, ACCD_critical,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1),
        DirName() {}

  /// \brief Set name of the directive.
  ///
  /// \param Name Name of the directive.
  ///
  void setDirectiveName(const DeclarationNameInfo &Name) { DirName = Name; }

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param Name Name of the directive.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCCriticalDirective *
  Create(const ASTContext &C, const DeclarationNameInfo &Name,
         SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCCriticalDirective *CreateEmpty(const ASTContext &C,
                                           unsigned NumClauses, EmptyShell);

  /// \brief Return name of the directive.
  ///
  DeclarationNameInfo getDirectiveName() const { return DirName; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCCriticalDirectiveClass;
  }
};

// LUIS
/// \brief This represents '#pragma acc parallel loop' directive.
///
/// \code
/// #pragma acc parallel loop private(a,b) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc parallel loop' has clauses 'private'
/// with the variables 'a' and 'b' and 'reduction' with operator '+' and
/// variables 'c' and 'd'.
///
class ACCParallelLoopDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// \brief true if current region has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCParallelLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                          unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCParallelLoopDirectiveClass, ACCD_parallel_loop,
                         StartLoc, EndLoc, CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCParallelLoopDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCParallelLoopDirectiveClass, ACCD_parallel_loop,
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if current directive has inner cancel directive.
  ///
  static ACCParallelLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs, bool HasCancel);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCParallelLoopDirective *CreateEmpty(const ASTContext &C,
                                              unsigned NumClauses,
                                              unsigned CollapsedNum,
                                              EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCParallelLoopDirectiveClass;
  }
};

/// \brief This represents '#pragma acc parallel loop simd' directive.
///
/// \code
/// #pragma acc parallel loop simd private(a,b) linear(i,j:s) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc parallel loop simd' has clauses
/// 'private' with the variables 'a' and 'b', 'linear' with variables 'i', 'j'
/// and linear step 's', 'reduction' with operator '+' and variables 'c' and
/// 'd'.
///
class ACCParallelLoopVectorDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCParallelLoopVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                              unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCParallelLoopVectorDirectiveClass,
                         ACCD_parallel_loop_vector, StartLoc, EndLoc, CollapsedNum,
                         NumClauses) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCParallelLoopVectorDirective(unsigned CollapsedNum,
                                       unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCParallelLoopVectorDirectiveClass,
                         ACCD_parallel_loop_vector, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCParallelLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCParallelLoopVectorDirective *CreateEmpty(const ASTContext &C,
                                                  unsigned NumClauses,
                                                  unsigned CollapsedNum,
                                                  EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCParallelLoopVectorDirectiveClass;
  }
};

/// \brief This represents '#pragma acc parallel sections' directive.
///
/// \code
/// #pragma acc parallel sections private(a,b) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc parallel sections' has clauses
/// 'private' with the variables 'a' and 'b' and 'reduction' with operator '+'
/// and variables 'c' and 'd'.
///
class ACCParallelSectionsDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;

  /// \brief true if current directive has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCParallelSectionsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                               unsigned NumClauses)
      : ACCExecutableDirective(this, ACCParallelSectionsDirectiveClass,
                               ACCD_parallel_sections, StartLoc, EndLoc,
                               NumClauses, 1),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCParallelSectionsDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCParallelSectionsDirectiveClass,
                               ACCD_parallel_sections, SourceLocation(),
                               SourceLocation(), NumClauses, 1),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param HasCancel true if current directive has inner cancel directive.
  ///
  static ACCParallelSectionsDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCParallelSectionsDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCParallelSectionsDirectiveClass;
  }
};

/// \brief This represents '#pragma acc task' directive.
///
/// \code
/// #pragma acc task private(a,b) final(d)
/// \endcode
/// In this example directive '#pragma acc task' has clauses 'private' with the
/// variables 'a' and 'b' and 'final' with condition 'd'.
///
class ACCTaskDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief true if this directive has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTaskDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                   unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTaskDirectiveClass, ACCD_task, StartLoc,
                               EndLoc, NumClauses, 1),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTaskDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTaskDirectiveClass, ACCD_task,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param HasCancel true, if current directive has inner cancel directive.
  ///
  static ACCTaskDirective *Create(const ASTContext &C, SourceLocation StartLoc,
                                  SourceLocation EndLoc,
                                  ArrayRef<ACCClause *> Clauses,
                                  Stmt *AssociatedStmt, bool HasCancel);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTaskDirective *CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                       EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskDirectiveClass;
  }
};

/// \brief This represents '#pragma acc taskyield' directive.
///
/// \code
/// #pragma acc taskyield
/// \endcode
///
class ACCTaskyieldDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCTaskyieldDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCTaskyieldDirectiveClass, ACCD_taskyield,
                               StartLoc, EndLoc, 0, 0) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCTaskyieldDirective()
      : ACCExecutableDirective(this, ACCTaskyieldDirectiveClass, ACCD_taskyield,
                               SourceLocation(), SourceLocation(), 0, 0) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  ///
  static ACCTaskyieldDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCTaskyieldDirective *CreateEmpty(const ASTContext &C, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskyieldDirectiveClass;
  }
};

/// \brief This represents '#pragma acc barrier' directive.
///
/// \code
/// #pragma acc barrier
/// \endcode
///
class ACCBarrierDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCBarrierDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCBarrierDirectiveClass, ACCD_barrier,
                               StartLoc, EndLoc, 0, 0) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCBarrierDirective()
      : ACCExecutableDirective(this, ACCBarrierDirectiveClass, ACCD_barrier,
                               SourceLocation(), SourceLocation(), 0, 0) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  ///
  static ACCBarrierDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCBarrierDirective *CreateEmpty(const ASTContext &C, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCBarrierDirectiveClass;
  }
};

/// \brief This represents '#pragma acc taskwait' directive.
///
/// \code
/// #pragma acc taskwait
/// \endcode
///
class ACCTaskwaitDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCTaskwaitDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCTaskwaitDirectiveClass, ACCD_taskwait,
                               StartLoc, EndLoc, 0, 0) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCTaskwaitDirective()
      : ACCExecutableDirective(this, ACCTaskwaitDirectiveClass, ACCD_taskwait,
                               SourceLocation(), SourceLocation(), 0, 0) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  ///
  static ACCTaskwaitDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCTaskwaitDirective *CreateEmpty(const ASTContext &C, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskwaitDirectiveClass;
  }
};

/// This represents '#pragma acc taskgroup' directive.
///
/// \code
/// #pragma acc taskgroup
/// \endcode
///
class ACCTaskgroupDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTaskgroupDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                        unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTaskgroupDirectiveClass, ACCD_taskgroup,
                               StartLoc, EndLoc, NumClauses, 2) {}

  /// Build an empty directive.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTaskgroupDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTaskgroupDirectiveClass, ACCD_taskgroup,
                               SourceLocation(), SourceLocation(), NumClauses,
                               2) {}

  /// Sets the task_reduction return variable.
  void setReductionRef(Expr *RR) {
    *std::next(child_begin(), 1) = RR;
  }

public:
  /// Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param ReductionRef Reference to the task_reduction return variable.
  ///
  static ACCTaskgroupDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
         Expr *ReductionRef);

  /// Creates an empty directive.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTaskgroupDirective *CreateEmpty(const ASTContext &C,
                                            unsigned NumClauses, EmptyShell);


  /// Returns reference to the task_reduction return variable.
  const Expr *getReductionRef() const {
    return static_cast<const Expr *>(*std::next(child_begin(), 1));
  }
  Expr *getReductionRef() {
    return static_cast<Expr *>(*std::next(child_begin(), 1));
  }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskgroupDirectiveClass;
  }
};

/// \brief This represents '#pragma acc flush' directive.
///
/// \code
/// #pragma acc flush(a,b)
/// \endcode
/// In this example directive '#pragma acc flush' has 2 arguments- variables 'a'
/// and 'b'.
/// 'acc flush' directive does not have clauses but have an optional list of
/// variables to flush. This list of variables is stored within some fake clause
/// FlushClause.
class ACCFlushDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCFlushDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                    unsigned NumClauses)
      : ACCExecutableDirective(this, ACCFlushDirectiveClass, ACCD_flush,
                               StartLoc, EndLoc, NumClauses, 0) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCFlushDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCFlushDirectiveClass, ACCD_flush,
                               SourceLocation(), SourceLocation(), NumClauses,
                               0) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses (only single ACCFlushClause clause is
  /// allowed).
  ///
  static ACCFlushDirective *Create(const ASTContext &C, SourceLocation StartLoc,
                                   SourceLocation EndLoc,
                                   ArrayRef<ACCClause *> Clauses);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCFlushDirective *CreateEmpty(const ASTContext &C,
                                        unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCFlushDirectiveClass;
  }
};

/// \brief This represents '#pragma acc ordered' directive.
///
/// \code
/// #pragma acc ordered
/// \endcode
///
class ACCOrderedDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCOrderedDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                      unsigned NumClauses)
      : ACCExecutableDirective(this, ACCOrderedDirectiveClass, ACCD_ordered,
                               StartLoc, EndLoc, NumClauses, 1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCOrderedDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCOrderedDirectiveClass, ACCD_ordered,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1) {}

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCOrderedDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCOrderedDirective *CreateEmpty(const ASTContext &C,
                                          unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCOrderedDirectiveClass;
  }
};

/// \brief This represents '#pragma acc atomic' directive.
///
/// \code
/// #pragma acc atomic capture
/// \endcode
/// In this example directive '#pragma acc atomic' has clause 'capture'.
///
class ACCAtomicDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Used for 'atomic update' or 'atomic capture' constructs. They may
  /// have atomic expressions of forms
  /// \code
  /// x = x binop expr;
  /// x = expr binop x;
  /// \endcode
  /// This field is true for the first form of the expression and false for the
  /// second. Required for correct codegen of non-associative operations (like
  /// << or >>).
  bool IsXLHSInRHSPart;
  /// \brief Used for 'atomic update' or 'atomic capture' constructs. They may
  /// have atomic expressions of forms
  /// \code
  /// v = x; <update x>;
  /// <update x>; v = x;
  /// \endcode
  /// This field is true for the first(postfix) form of the expression and false
  /// otherwise.
  bool IsPostfixUpdate;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCAtomicDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                     unsigned NumClauses)
      : ACCExecutableDirective(this, ACCAtomicDirectiveClass, ACCD_atomic,
                               StartLoc, EndLoc, NumClauses, 5),
        IsXLHSInRHSPart(false), IsPostfixUpdate(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCAtomicDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCAtomicDirectiveClass, ACCD_atomic,
                               SourceLocation(), SourceLocation(), NumClauses,
                               5),
        IsXLHSInRHSPart(false), IsPostfixUpdate(false) {}

  /// \brief Set 'x' part of the associated expression/statement.
  void setX(Expr *X) { *std::next(child_begin()) = X; }
  /// \brief Set helper expression of the form
  /// 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' or
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  void setUpdateExpr(Expr *UE) { *std::next(child_begin(), 2) = UE; }
  /// \brief Set 'v' part of the associated expression/statement.
  void setV(Expr *V) { *std::next(child_begin(), 3) = V; }
  /// \brief Set 'expr' part of the associated expression/statement.
  void setExpr(Expr *E) { *std::next(child_begin(), 4) = E; }

public:
  /// \brief Creates directive with a list of \a Clauses and 'x', 'v' and 'expr'
  /// parts of the atomic construct (see Section 2.12.6, atomic Construct, for
  /// detailed description of 'x', 'v' and 'expr').
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param X 'x' part of the associated expression/statement.
  /// \param V 'v' part of the associated expression/statement.
  /// \param E 'expr' part of the associated expression/statement.
  /// \param UE Helper expression of the form
  /// 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' or
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  /// \param IsXLHSInRHSPart true if \a UE has the first form and false if the
  /// second.
  /// \param IsPostfixUpdate true if original value of 'x' must be stored in
  /// 'v', not an updated one.
  static ACCAtomicDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, Expr *X, Expr *V,
         Expr *E, Expr *UE, bool IsXLHSInRHSPart, bool IsPostfixUpdate);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCAtomicDirective *CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses, EmptyShell);

  /// \brief Get 'x' part of the associated expression/statement.
  Expr *getX() { return cast_or_null<Expr>(*std::next(child_begin())); }
  const Expr *getX() const {
    return cast_or_null<Expr>(*std::next(child_begin()));
  }
  /// \brief Get helper expression of the form
  /// 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' or
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  Expr *getUpdateExpr() {
    return cast_or_null<Expr>(*std::next(child_begin(), 2));
  }
  const Expr *getUpdateExpr() const {
    return cast_or_null<Expr>(*std::next(child_begin(), 2));
  }
  /// \brief Return true if helper update expression has form
  /// 'OpaqueValueExpr(x) binop OpaqueValueExpr(expr)' and false if it has form
  /// 'OpaqueValueExpr(expr) binop OpaqueValueExpr(x)'.
  bool isXLHSInRHSPart() const { return IsXLHSInRHSPart; }
  /// \brief Return true if 'v' expression must be updated to original value of
  /// 'x', false if 'v' must be updated to the new value of 'x'.
  bool isPostfixUpdate() const { return IsPostfixUpdate; }
  /// \brief Get 'v' part of the associated expression/statement.
  Expr *getV() { return cast_or_null<Expr>(*std::next(child_begin(), 3)); }
  const Expr *getV() const {
    return cast_or_null<Expr>(*std::next(child_begin(), 3));
  }
  /// \brief Get 'expr' part of the associated expression/statement.
  Expr *getExpr() { return cast_or_null<Expr>(*std::next(child_begin(), 4)); }
  const Expr *getExpr() const {
    return cast_or_null<Expr>(*std::next(child_begin(), 4));
  }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCAtomicDirectiveClass;
  }
};

/// \brief This represents '#pragma acc target' directive.
///
/// \code
/// #pragma acc target if(a)
/// \endcode
/// In this example directive '#pragma acc target' has clause 'if' with
/// condition 'a'.
///
class ACCTargetDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                     unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetDirectiveClass, ACCD_target,
                               StartLoc, EndLoc, NumClauses, 1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetDirectiveClass, ACCD_target,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCTargetDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetDirective *CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetDirectiveClass;
  }
};
// acc2mp MYHEADER
/// \brief This represents '#pragma acc data' directive.
///
/// \code
/// #pragma acc data device(0) if(a) map(b[:])
/// \endcode
/// In this example directive '#pragma acc data' has clauses 'device'
/// with the value '0', 'if' with condition 'a' and 'map' with array
/// section 'b[:]'.
///
class ACCDataDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param NumClauses The number of clauses.
  ///
  ACCDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                         unsigned NumClauses)
      : ACCExecutableDirective(this, ACCDataDirectiveClass, 
                               ACCD_data, StartLoc, EndLoc, NumClauses,
                               1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCDataDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCDataDirectiveClass, 
                               ACCD_data, SourceLocation(),
                               SourceLocation(), NumClauses, 1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCDataDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a N clauses.
  ///
  /// \param C AST context.
  /// \param N The number of clauses.
  ///
  static ACCDataDirective *CreateEmpty(const ASTContext &C, unsigned N,
                                             EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCDataDirectiveClass;
  }
};

/// \brief This represents '#pragma acc enter data' directive.
///
/// \code
/// #pragma acc enter data device(0) if(a) map(b[:])
/// \endcode
/// In this example directive '#pragma acc enter data' has clauses
/// 'device' with the value '0', 'if' with condition 'a' and 'map' with array
/// section 'b[:]'.
///
class ACCEnterDataDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param NumClauses The number of clauses.
  ///
  ACCEnterDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                              unsigned NumClauses)
      : ACCExecutableDirective(this, ACCEnterDataDirectiveClass,
                               ACCD_enter_data, StartLoc, EndLoc,
                               NumClauses, /*NumChildren=*/1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCEnterDataDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCEnterDataDirectiveClass,
                               ACCD_enter_data, SourceLocation(),
                               SourceLocation(), NumClauses,
                               /*NumChildren=*/1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCEnterDataDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a N clauses.
  ///
  /// \param C AST context.
  /// \param N The number of clauses.
  ///
  static ACCEnterDataDirective *CreateEmpty(const ASTContext &C,
                                                  unsigned N, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCEnterDataDirectiveClass;
  }
};

/// \brief This represents '#pragma acc exit data' directive.
///
/// \code
/// #pragma acc exit data device(0) if(a) map(b[:])
/// \endcode
/// In this example directive '#pragma acc exit data' has clauses
/// 'device' with the value '0', 'if' with condition 'a' and 'map' with array
/// section 'b[:]'.
///
class ACCExitDataDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param NumClauses The number of clauses.
  ///
  ACCExitDataDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                             unsigned NumClauses)
      : ACCExecutableDirective(this, ACCExitDataDirectiveClass,
                               ACCD_exit_data, StartLoc, EndLoc,
                               NumClauses, /*NumChildren=*/1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCExitDataDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCExitDataDirectiveClass,
                               ACCD_exit_data, SourceLocation(),
                               SourceLocation(), NumClauses,
                               /*NumChildren=*/1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCExitDataDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a N clauses.
  ///
  /// \param C AST context.
  /// \param N The number of clauses.
  ///
  static ACCExitDataDirective *CreateEmpty(const ASTContext &C,
                                                 unsigned N, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCExitDataDirectiveClass;
  }
};
// acc2mp MYHEADER

/// \brief This represents '#pragma acc target parallel' directive.
///
/// \code
/// #pragma acc target parallel if(a)
/// \endcode
/// In this example directive '#pragma acc target parallel' has clause 'if' with
/// condition 'a'.
///
class ACCTargetParallelDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetParallelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                             unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetParallelDirectiveClass,
                               ACCD_target_parallel, StartLoc, EndLoc,
                               NumClauses, /*NumChildren=*/1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetParallelDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetParallelDirectiveClass,
                               ACCD_target_parallel, SourceLocation(),
                               SourceLocation(), NumClauses,
                               /*NumChildren=*/1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCTargetParallelDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetParallelDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetParallelDirectiveClass;
  }
};

/// \brief This represents '#pragma acc target parallel loop' directive.
///
/// \code
/// #pragma acc target parallel loop private(a,b) reduction(+:c,d)
/// \endcode
/// In this example directive '#pragma acc target parallel loop' has clauses
/// 'private' with the variables 'a' and 'b' and 'reduction' with operator '+'
/// and variables 'c' and 'd'.
///
class ACCTargetParallelLoopDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// \brief true if current region has inner cancel directive.
  bool HasCancel;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetParallelLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                                unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetParallelLoopDirectiveClass,
                         ACCD_target_parallel_loop, StartLoc, EndLoc,
                         CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetParallelLoopDirective(unsigned CollapsedNum,
                                         unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetParallelLoopDirectiveClass,
                         ACCD_target_parallel_loop, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// \brief Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if current directive has inner cancel directive.
  ///
  static ACCTargetParallelLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs, bool HasCancel);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetParallelLoopDirective *CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    unsigned CollapsedNum,
                                                    EmptyShell);

  /// \brief Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetParallelLoopDirectiveClass;
  }
};

/// \brief This represents '#pragma acc teams' directive.
///
/// \code
/// #pragma acc teams if(a)
/// \endcode
/// In this example directive '#pragma acc teams' has clause 'if' with
/// condition 'a'.
///
class ACCTeamsDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                    unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTeamsDirectiveClass, ACCD_teams,
                               StartLoc, EndLoc, NumClauses, 1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTeamsDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTeamsDirectiveClass, ACCD_teams,
                               SourceLocation(), SourceLocation(), NumClauses,
                               1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCTeamsDirective *Create(const ASTContext &C, SourceLocation StartLoc,
                                   SourceLocation EndLoc,
                                   ArrayRef<ACCClause *> Clauses,
                                   Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTeamsDirective *CreateEmpty(const ASTContext &C,
                                        unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTeamsDirectiveClass;
  }
};

/// \brief This represents '#pragma acc cancellation point' directive.
///
/// \code
/// #pragma acc cancellation point for
/// \endcode
///
/// In this example a cancellation point is created for innermost 'for' region.
class ACCCancellationPointDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  OpenACCDirectiveKind CancelRegion;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  ///
  ACCCancellationPointDirective(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCExecutableDirective(this, ACCCancellationPointDirectiveClass,
                               ACCD_cancellation_point, StartLoc, EndLoc, 0, 0),
        CancelRegion(ACCD_unknown) {}

  /// \brief Build an empty directive.
  ///
  explicit ACCCancellationPointDirective()
      : ACCExecutableDirective(this, ACCCancellationPointDirectiveClass,
                               ACCD_cancellation_point, SourceLocation(),
                               SourceLocation(), 0, 0),
        CancelRegion(ACCD_unknown) {}

  /// \brief Set cancel region for current cancellation point.
  /// \param CR Cancellation region.
  void setCancelRegion(OpenACCDirectiveKind CR) { CancelRegion = CR; }

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  ///
  static ACCCancellationPointDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         OpenACCDirectiveKind CancelRegion);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  ///
  static ACCCancellationPointDirective *CreateEmpty(const ASTContext &C,
                                                    EmptyShell);

  /// \brief Get cancellation region for the current cancellation point.
  OpenACCDirectiveKind getCancelRegion() const { return CancelRegion; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCCancellationPointDirectiveClass;
  }
};

/// \brief This represents '#pragma acc cancel' directive.
///
/// \code
/// #pragma acc cancel for
/// \endcode
///
/// In this example a cancel is created for innermost 'for' region.
class ACCCancelDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  OpenACCDirectiveKind CancelRegion;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCCancelDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                     unsigned NumClauses)
      : ACCExecutableDirective(this, ACCCancelDirectiveClass, ACCD_cancel,
                               StartLoc, EndLoc, NumClauses, 0),
        CancelRegion(ACCD_unknown) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  explicit ACCCancelDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCCancelDirectiveClass, ACCD_cancel,
                               SourceLocation(), SourceLocation(), NumClauses,
                               0),
        CancelRegion(ACCD_unknown) {}

  /// \brief Set cancel region for current cancellation point.
  /// \param CR Cancellation region.
  void setCancelRegion(OpenACCDirectiveKind CR) { CancelRegion = CR; }

public:
  /// \brief Creates directive.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  ///
  static ACCCancelDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, OpenACCDirectiveKind CancelRegion);

  /// \brief Creates an empty directive.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCCancelDirective *CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses, EmptyShell);

  /// \brief Get cancellation region for the current cancellation point.
  OpenACCDirectiveKind getCancelRegion() const { return CancelRegion; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCCancelDirectiveClass;
  }
};

/// \brief This represents '#pragma acc taskloop' directive.
///
/// \code
/// #pragma acc taskloop private(a,b) grainsize(val) num_tasks(num)
/// \endcode
/// In this example directive '#pragma acc taskloop' has clauses 'private'
/// with the variables 'a' and 'b', 'grainsize' with expression 'val' and
/// 'num_tasks' with expression 'num'.
///
class ACCTaskLoopDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTaskLoopDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                       unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTaskLoopDirectiveClass, ACCD_taskloop,
                         StartLoc, EndLoc, CollapsedNum, NumClauses) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTaskLoopDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTaskLoopDirectiveClass, ACCD_taskloop,
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTaskLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTaskLoopDirective *CreateEmpty(const ASTContext &C,
                                           unsigned NumClauses,
                                           unsigned CollapsedNum, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskLoopDirectiveClass;
  }
};

/// \brief This represents '#pragma acc taskloop simd' directive.
///
/// \code
/// #pragma acc taskloop simd private(a,b) grainsize(val) num_tasks(num)
/// \endcode
/// In this example directive '#pragma acc taskloop simd' has clauses 'private'
/// with the variables 'a' and 'b', 'grainsize' with expression 'val' and
/// 'num_tasks' with expression 'num'.
///
class ACCTaskLoopVectorDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTaskLoopVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                           unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTaskLoopVectorDirectiveClass,
                         ACCD_taskloop_vector, StartLoc, EndLoc, CollapsedNum,
                         NumClauses) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTaskLoopVectorDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTaskLoopVectorDirectiveClass,
                         ACCD_taskloop_vector, SourceLocation(), SourceLocation(),
                         CollapsedNum, NumClauses) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTaskLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTaskLoopVectorDirective *CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTaskLoopVectorDirectiveClass;
  }
};

/// \brief This represents '#pragma acc distribute' directive.
///
/// \code
/// #pragma acc distribute private(a,b)
/// \endcode
/// In this example directive '#pragma acc distribute' has clauses 'private'
/// with the variables 'a' and 'b'
///
class ACCDistributeDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                         unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeDirectiveClass, ACCD_distribute,
                         StartLoc, EndLoc, CollapsedNum, NumClauses)
        {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCDistributeDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeDirectiveClass, ACCD_distribute,
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses)
        {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCDistributeDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCDistributeDirective *CreateEmpty(const ASTContext &C,
                                             unsigned NumClauses,
                                             unsigned CollapsedNum, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCDistributeDirectiveClass;
  }
};

/// \brief This represents '#pragma acc target update' directive.
///
/// \code
/// #pragma acc target update to(a) from(b) device(1)
/// \endcode
/// In this example directive '#pragma acc target update' has clause 'to' with
/// argument 'a', clause 'from' with argument 'b' and clause 'device' with
/// argument '1'.
///
class ACCTargetUpdateDirective : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param NumClauses The number of clauses.
  ///
  ACCTargetUpdateDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                           unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetUpdateDirectiveClass,
                               ACCD_target_update, StartLoc, EndLoc, NumClauses,
                               1) {}

  /// \brief Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetUpdateDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetUpdateDirectiveClass,
                               ACCD_target_update, SourceLocation(),
                               SourceLocation(), NumClauses, 1) {}

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCTargetUpdateDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt);

  /// \brief Creates an empty directive with the place for \a NumClauses
  /// clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses The number of clauses.
  ///
  static ACCTargetUpdateDirective *CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetUpdateDirectiveClass;
  }
};

/// \brief This represents '#pragma acc distribute parallel for' composite
///  directive.
///
/// \code
/// #pragma acc distribute parallel loop private(a,b)
/// \endcode
/// In this example directive '#pragma acc distribute parallel loop' has clause
/// 'private' with the variables 'a' and 'b'
///
class ACCDistributeParallelLoopDirective : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// true if the construct has inner cancel directive.
  bool HasCancel = false;

  /// \brief Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCDistributeParallelLoopDirective(SourceLocation StartLoc,
                                    SourceLocation EndLoc,
                                    unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeParallelLoopDirectiveClass,
                         ACCD_distribute_parallel_loop, StartLoc, EndLoc,
                         CollapsedNum, NumClauses), HasCancel(false) {}

  /// \brief Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCDistributeParallelLoopDirective(unsigned CollapsedNum,
                                             unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeParallelLoopDirectiveClass,
                         ACCD_distribute_parallel_loop, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// \brief Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if this directive has inner cancel directive.
  ///
  static ACCDistributeParallelLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs, bool HasCancel);

  /// \brief Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCDistributeParallelLoopDirective *CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        unsigned CollapsedNum,
                                                        EmptyShell);

  /// Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCDistributeParallelLoopDirectiveClass;
  }
};

/// This represents '#pragma acc distribute parallel loop simd' composite
/// directive.
///
/// \code
/// #pragma acc distribute parallel loop simd private(x)
/// \endcode
/// In this example directive '#pragma acc distribute parallel loop simd' has
/// clause 'private' with the variables 'x'
///
class ACCDistributeParallelLoopVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCDistributeParallelLoopVectorDirective(SourceLocation StartLoc,
                                        SourceLocation EndLoc,
                                        unsigned CollapsedNum,
                                        unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeParallelLoopVectorDirectiveClass,
                         ACCD_distribute_parallel_loop_vector, StartLoc, 
                         EndLoc, CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCDistributeParallelLoopVectorDirective(unsigned CollapsedNum,
                                                 unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeParallelLoopVectorDirectiveClass,
                         ACCD_distribute_parallel_loop_vector, 
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCDistributeParallelLoopVectorDirective *Create(
      const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
      unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
      Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCDistributeParallelLoopVectorDirective *CreateEmpty(
      const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
      EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCDistributeParallelLoopVectorDirectiveClass;
  }
};

/// This represents '#pragma acc distribute simd' composite directive.
///
/// \code
/// #pragma acc distribute simd private(x)
/// \endcode
/// In this example directive '#pragma acc distribute simd' has clause
/// 'private' with the variables 'x'
///
class ACCDistributeVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCDistributeVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                             unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeVectorDirectiveClass,
                         ACCD_distribute_vector, StartLoc, EndLoc, CollapsedNum,
                         NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCDistributeVectorDirective(unsigned CollapsedNum, 
                                      unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCDistributeVectorDirectiveClass,
                         ACCD_distribute_vector, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCDistributeVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCDistributeVectorDirective *CreateEmpty(const ASTContext &C,
                                                 unsigned NumClauses,
                                                 unsigned CollapsedNum,
                                                 EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCDistributeVectorDirectiveClass;
  }
};

/// This represents '#pragma acc target parallel loop simd' directive.
///
/// \code
/// #pragma acc target parallel loop simd private(a) map(b) safelen(c)
/// \endcode
/// In this example directive '#pragma acc target parallel loop simd' has clauses
/// 'private' with the variable 'a', 'map' with the variable 'b' and 'safelen'
/// with the variable 'c'.
///
class ACCTargetParallelLoopVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetParallelLoopVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                                unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetParallelLoopVectorDirectiveClass,
                         ACCD_target_parallel_loop_vector, StartLoc, EndLoc,
                         CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetParallelLoopVectorDirective(unsigned CollapsedNum,
                                             unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetParallelLoopVectorDirectiveClass,
                         ACCD_target_parallel_loop_vector, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTargetParallelLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetParallelLoopVectorDirective *CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        unsigned CollapsedNum,
                                                        EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetParallelLoopVectorDirectiveClass;
  }
};

/// This represents '#pragma acc target simd' directive.
///
/// \code
/// #pragma acc target simd private(a) map(b) safelen(c)
/// \endcode
/// In this example directive '#pragma acc target simd' has clauses 'private'
/// with the variable 'a', 'map' with the variable 'b' and 'safelen' with
/// the variable 'c'.
///
class ACCTargetVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetVectorDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                         unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetVectorDirectiveClass,
                         ACCD_target_vector, StartLoc, EndLoc, CollapsedNum,
                         NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetVectorDirective(unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetVectorDirectiveClass, ACCD_target_vector, 
                         SourceLocation(),SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTargetVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetVectorDirective *CreateEmpty(const ASTContext &C,
                                             unsigned NumClauses,
                                             unsigned CollapsedNum,
                                             EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetVectorDirectiveClass;
  }
};

/// This represents '#pragma acc teams distribute' directive.
///
/// \code
/// #pragma acc teams distribute private(a,b)
/// \endcode
/// In this example directive '#pragma acc teams distribute' has clauses
/// 'private' with the variables 'a' and 'b'
///
class ACCTeamsDistributeDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTeamsDistributeDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                              unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeDirectiveClass, 
                         ACCD_teams_distribute, StartLoc, EndLoc, 
                         CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTeamsDistributeDirective(unsigned CollapsedNum,
                                       unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeDirectiveClass,
                         ACCD_teams_distribute, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTeamsDistributeDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTeamsDistributeDirective *CreateEmpty(const ASTContext &C,
                                                  unsigned NumClauses,
                                                  unsigned CollapsedNum,
                                                  EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTeamsDistributeDirectiveClass;
  }
};

/// This represents '#pragma acc teams distribute simd'
/// combined directive.
///
/// \code
/// #pragma acc teams distribute simd private(a,b)
/// \endcode
/// In this example directive '#pragma acc teams distribute simd'
/// has clause 'private' with the variables 'a' and 'b'
///
class ACCTeamsDistributeVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTeamsDistributeVectorDirective(SourceLocation StartLoc,
                                  SourceLocation EndLoc, unsigned CollapsedNum,
                                  unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeVectorDirectiveClass,
                         ACCD_teams_distribute_vector, StartLoc, EndLoc,
                         CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTeamsDistributeVectorDirective(unsigned CollapsedNum,
                                           unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeVectorDirectiveClass,
                         ACCD_teams_distribute_vector, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTeamsDistributeVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place
  /// for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTeamsDistributeVectorDirective *CreateEmpty(const ASTContext &C,
                                                      unsigned NumClauses,
                                                      unsigned CollapsedNum,
                                                      EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTeamsDistributeVectorDirectiveClass;
  }
};

/// This represents '#pragma acc teams distribute parallel loop simd' composite
/// directive.
///
/// \code
/// #pragma acc teams distribute parallel loop simd private(x)
/// \endcode
/// In this example directive '#pragma acc teams distribute parallel loop simd'
/// has clause 'private' with the variables 'x'
///
class ACCTeamsDistributeParallelLoopVectorDirective final
    : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTeamsDistributeParallelLoopVectorDirective(SourceLocation StartLoc,
                                             SourceLocation EndLoc,
                                             unsigned CollapsedNum,
                                             unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeParallelLoopVectorDirectiveClass,
                         ACCD_teams_distribute_parallel_loop_vector, StartLoc, 
                         EndLoc, CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTeamsDistributeParallelLoopVectorDirective(unsigned CollapsedNum,
                                                      unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeParallelLoopVectorDirectiveClass,
                         ACCD_teams_distribute_parallel_loop_vector, 
                         SourceLocation(), SourceLocation(), CollapsedNum,
                         NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTeamsDistributeParallelLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTeamsDistributeParallelLoopVectorDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTeamsDistributeParallelLoopVectorDirectiveClass;
  }
};

/// This represents '#pragma acc teams distribute parallel loop' composite
/// directive.
///
/// \code
/// #pragma acc teams distribute parallel loop private(x)
/// \endcode
/// In this example directive '#pragma acc teams distribute parallel loop'
/// has clause 'private' with the variables 'x'
///
class ACCTeamsDistributeParallelLoopDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// true if the construct has inner cancel directive.
  bool HasCancel = false;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTeamsDistributeParallelLoopDirective(SourceLocation StartLoc,
                                         SourceLocation EndLoc,
                                         unsigned CollapsedNum,
                                         unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeParallelLoopDirectiveClass,
                         ACCD_teams_distribute_parallel_loop, StartLoc, EndLoc,
                         CollapsedNum, NumClauses), HasCancel(false) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTeamsDistributeParallelLoopDirective(unsigned CollapsedNum,
                                                  unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTeamsDistributeParallelLoopDirectiveClass,
                         ACCD_teams_distribute_parallel_loop, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if this directive has inner cancel directive.
  ///
  static ACCTeamsDistributeParallelLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs, bool HasCancel);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTeamsDistributeParallelLoopDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  /// Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTeamsDistributeParallelLoopDirectiveClass;
  }
};

/// This represents '#pragma acc target teams' directive.
///
/// \code
/// #pragma acc target teams if(a>0)
/// \endcode
/// In this example directive '#pragma acc target teams' has clause 'if' with
/// condition 'a>0'.
///
class ACCTargetTeamsDirective final : public ACCExecutableDirective {
  friend class ASTStmtReader;
  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetTeamsDirective(SourceLocation StartLoc, SourceLocation EndLoc,
                          unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetTeamsDirectiveClass,
                               ACCD_target_teams, StartLoc, EndLoc, NumClauses,
                               1) {}

  /// Build an empty directive.
  ///
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetTeamsDirective(unsigned NumClauses)
      : ACCExecutableDirective(this, ACCTargetTeamsDirectiveClass,
                               ACCD_target_teams, SourceLocation(),
                               SourceLocation(), NumClauses, 1) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  ///
  static ACCTargetTeamsDirective *Create(const ASTContext &C,
                                         SourceLocation StartLoc,
                                         SourceLocation EndLoc,
                                         ArrayRef<ACCClause *> Clauses,
                                         Stmt *AssociatedStmt);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetTeamsDirective *CreateEmpty(const ASTContext &C,
                                              unsigned NumClauses, EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetTeamsDirectiveClass;
  }
};

/// This represents '#pragma acc target teams distribute' combined directive.
///
/// \code
/// #pragma acc target teams distribute private(x)
/// \endcode
/// In this example directive '#pragma acc target teams distribute' has clause
/// 'private' with the variables 'x'
///
class ACCTargetTeamsDistributeDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetTeamsDistributeDirective(SourceLocation StartLoc,
                                    SourceLocation EndLoc,
                                    unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetTeamsDistributeDirectiveClass,
                         ACCD_target_teams_distribute, StartLoc, EndLoc,
                         CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetTeamsDistributeDirective(unsigned CollapsedNum,
                                             unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetTeamsDistributeDirectiveClass,
                         ACCD_target_teams_distribute, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTargetTeamsDistributeDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetTeamsDistributeDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetTeamsDistributeDirectiveClass;
  }
};

/// This represents '#pragma acc target teams distribute parallel loop' combined
/// directive.
///
/// \code
/// #pragma acc target teams distribute parallel loop private(x)
/// \endcode
/// In this example directive '#pragma acc target teams distribute parallel
/// loop' has clause 'private' with the variables 'x'
///
class ACCTargetTeamsDistributeParallelLoopDirective final
    : public ACCLoopLikeDirective {
  friend class ASTStmtReader;
  /// true if the construct has inner cancel directive.
  bool HasCancel = false;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetTeamsDistributeParallelLoopDirective(SourceLocation StartLoc,
                                               SourceLocation EndLoc,
                                               unsigned CollapsedNum,
                                               unsigned NumClauses)
      : ACCLoopLikeDirective(this,
                         ACCTargetTeamsDistributeParallelLoopDirectiveClass,
                         ACCD_target_teams_distribute_parallel_loop, StartLoc,
                         EndLoc, CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetTeamsDistributeParallelLoopDirective(unsigned CollapsedNum,
                                                        unsigned NumClauses)
      : ACCLoopLikeDirective(
            this, ACCTargetTeamsDistributeParallelLoopDirectiveClass,
            ACCD_target_teams_distribute_parallel_loop, SourceLocation(),
            SourceLocation(), CollapsedNum, NumClauses),
        HasCancel(false) {}

  /// Set cancel state.
  void setHasCancel(bool Has) { HasCancel = Has; }

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  /// \param HasCancel true if this directive has inner cancel directive.
  ///
  static ACCTargetTeamsDistributeParallelLoopDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs, bool HasCancel);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetTeamsDistributeParallelLoopDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  /// Return true if current directive has inner cancel directive.
  bool hasCancel() const { return HasCancel; }

  static bool classof(const Stmt *T) {
    return T->getStmtClass() ==
           ACCTargetTeamsDistributeParallelLoopDirectiveClass;
  }
};

/// This represents '#pragma acc target teams distribute parallel loop simd'
/// combined directive.
///
/// \code
/// #pragma acc target teams distribute parallel loop simd private(x)
/// \endcode
/// In this example directive '#pragma acc target teams distribute parallel
/// loop simd' has clause 'private' with the variables 'x'
///
class ACCTargetTeamsDistributeParallelLoopVectorDirective final
    : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetTeamsDistributeParallelLoopVectorDirective(SourceLocation StartLoc,
                                                   SourceLocation EndLoc,
                                                   unsigned CollapsedNum,
                                                   unsigned NumClauses)
      : ACCLoopLikeDirective(this,
                         ACCTargetTeamsDistributeParallelLoopVectorDirectiveClass,
                         ACCD_target_teams_distribute_parallel_loop_vector,
                         StartLoc, EndLoc, CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetTeamsDistributeParallelLoopVectorDirective(
      unsigned CollapsedNum, unsigned NumClauses)
      : ACCLoopLikeDirective(
            this, ACCTargetTeamsDistributeParallelLoopVectorDirectiveClass,
            ACCD_target_teams_distribute_parallel_loop_vector, SourceLocation(),
            SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTargetTeamsDistributeParallelLoopVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetTeamsDistributeParallelLoopVectorDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() ==
           ACCTargetTeamsDistributeParallelLoopVectorDirectiveClass;
  }
};

/// This represents '#pragma acc target teams distribute simd' combined
/// directive.
///
/// \code
/// #pragma acc target teams distribute simd private(x)
/// \endcode
/// In this example directive '#pragma acc target teams distribute simd'
/// has clause 'private' with the variables 'x'
///
class ACCTargetTeamsDistributeVectorDirective final : public ACCLoopLikeDirective {
  friend class ASTStmtReader;

  /// Build directive with the given start and end location.
  ///
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending location of the directive.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  ACCTargetTeamsDistributeVectorDirective(SourceLocation StartLoc,
                                        SourceLocation EndLoc,
                                        unsigned CollapsedNum,
                                        unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetTeamsDistributeVectorDirectiveClass,
                         ACCD_target_teams_distribute_vector, StartLoc, EndLoc,
                         CollapsedNum, NumClauses) {}

  /// Build an empty directive.
  ///
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  explicit ACCTargetTeamsDistributeVectorDirective(unsigned CollapsedNum,
                                                 unsigned NumClauses)
      : ACCLoopLikeDirective(this, ACCTargetTeamsDistributeVectorDirectiveClass,
                         ACCD_target_teams_distribute_vector, SourceLocation(),
                         SourceLocation(), CollapsedNum, NumClauses) {}

public:
  /// Creates directive with a list of \a Clauses.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the directive kind.
  /// \param EndLoc Ending Location of the directive.
  /// \param CollapsedNum Number of collapsed loops.
  /// \param Clauses List of clauses.
  /// \param AssociatedStmt Statement, associated with the directive.
  /// \param Exprs Helper expressions for CodeGen.
  ///
  static ACCTargetTeamsDistributeVectorDirective *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
         unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses,
         Stmt *AssociatedStmt, const HelperExprs &Exprs);

  /// Creates an empty directive with the place for \a NumClauses clauses.
  ///
  /// \param C AST context.
  /// \param CollapsedNum Number of collapsed nested loops.
  /// \param NumClauses Number of clauses.
  ///
  static ACCTargetTeamsDistributeVectorDirective *
  CreateEmpty(const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
              EmptyShell);

  static bool classof(const Stmt *T) {
    return T->getStmtClass() == ACCTargetTeamsDistributeVectorDirectiveClass;
  }
};

} // end namespace clang

#endif
