//===--- StmtOpenACC.cpp - Classes for OpenACC directives -------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the subclesses of Stmt class declared in StmtOpenACC.h
//
//===----------------------------------------------------------------------===//

#include "clang/AST/StmtOpenACC.h"

#include "clang/AST/ASTContext.h"

using namespace clang;

void ACCExecutableDirective::setClauses(ArrayRef<ACCClause *> Clauses) {
  assert(Clauses.size() == getNumClauses() &&
         "Number of clauses is not the same as the preallocated buffer");
  std::copy(Clauses.begin(), Clauses.end(), getClauses().begin());
}

void ACCLoopLikeDirective::setCounters(ArrayRef<Expr *> A) {
  assert(A.size() == getCollapsedNumber() &&
         "Number of loop counters is not the same as the collapsed number");
  std::copy(A.begin(), A.end(), getCounters().begin());
}

void ACCLoopLikeDirective::setPrivateCounters(ArrayRef<Expr *> A) {
  assert(A.size() == getCollapsedNumber() && "Number of loop private counters "
                                             "is not the same as the collapsed "
                                             "number");
  std::copy(A.begin(), A.end(), getPrivateCounters().begin());
}

void ACCLoopLikeDirective::setInits(ArrayRef<Expr *> A) {
  assert(A.size() == getCollapsedNumber() &&
         "Number of counter inits is not the same as the collapsed number");
  std::copy(A.begin(), A.end(), getInits().begin());
}

void ACCLoopLikeDirective::setUpdates(ArrayRef<Expr *> A) {
  assert(A.size() == getCollapsedNumber() &&
         "Number of counter updates is not the same as the collapsed number");
  std::copy(A.begin(), A.end(), getUpdates().begin());
}

void ACCLoopLikeDirective::setFinals(ArrayRef<Expr *> A) {
  assert(A.size() == getCollapsedNumber() &&
         "Number of counter finals is not the same as the collapsed number");
  std::copy(A.begin(), A.end(), getFinals().begin());
}

ACCParallelDirective *ACCParallelDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCParallelDirective *Dir =
      new (Mem) ACCParallelDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCParallelDirective *ACCParallelDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCParallelDirective(NumClauses);
}

ACCSimdDirective *
ACCSimdDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                         SourceLocation EndLoc, unsigned CollapsedNum,
                         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
                         const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCSimdDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_simd));
  ACCSimdDirective *Dir = new (Mem)
      ACCSimdDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCSimdDirective *ACCSimdDirective::CreateEmpty(const ASTContext &C,
                                                unsigned NumClauses,
                                                unsigned CollapsedNum,
                                                EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCSimdDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_simd));
  return new (Mem) ACCSimdDirective(CollapsedNum, NumClauses);
}

ACCLoopDirective *
ACCLoopDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                        SourceLocation EndLoc, unsigned CollapsedNum,
                        ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
                        const HelperExprs &Exprs, bool HasCancel) {
  unsigned Size = llvm::alignTo(sizeof(ACCLoopDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop));
  ACCLoopDirective *Dir =
      new (Mem) ACCLoopDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCLoopDirective *ACCLoopDirective::CreateEmpty(const ASTContext &C,
                                              unsigned NumClauses,
                                              unsigned CollapsedNum,
                                              EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCLoopDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop));
  return new (Mem) ACCLoopDirective(CollapsedNum, NumClauses);
}

ACCLoopSimdDirective *
ACCLoopSimdDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                            SourceLocation EndLoc, unsigned CollapsedNum,
                            ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
                            const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCLoopSimdDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop_simd));
  ACCLoopSimdDirective *Dir = new (Mem)
      ACCLoopSimdDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCLoopSimdDirective *ACCLoopSimdDirective::CreateEmpty(const ASTContext &C,
                                                      unsigned NumClauses,
                                                      unsigned CollapsedNum,
                                                      EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCLoopSimdDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop_simd));
  return new (Mem) ACCLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCSectionsDirective *ACCSectionsDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCSectionsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCSectionsDirective *Dir =
      new (Mem) ACCSectionsDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCSectionsDirective *ACCSectionsDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCSectionsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCSectionsDirective(NumClauses);
}

ACCSectionDirective *ACCSectionDirective::Create(const ASTContext &C,
                                                 SourceLocation StartLoc,
                                                 SourceLocation EndLoc,
                                                 Stmt *AssociatedStmt,
                                                 bool HasCancel) {
  unsigned Size = llvm::alignTo(sizeof(ACCSectionDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *));
  ACCSectionDirective *Dir = new (Mem) ACCSectionDirective(StartLoc, EndLoc);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCSectionDirective *ACCSectionDirective::CreateEmpty(const ASTContext &C,
                                                      EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCSectionDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *));
  return new (Mem) ACCSectionDirective();
}

ACCSingleDirective *ACCSingleDirective::Create(const ASTContext &C,
                                               SourceLocation StartLoc,
                                               SourceLocation EndLoc,
                                               ArrayRef<ACCClause *> Clauses,
                                               Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCSingleDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCSingleDirective *Dir =
      new (Mem) ACCSingleDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCSingleDirective *ACCSingleDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCSingleDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCSingleDirective(NumClauses);
}

ACCMasterDirective *ACCMasterDirective::Create(const ASTContext &C,
                                               SourceLocation StartLoc,
                                               SourceLocation EndLoc,
                                               Stmt *AssociatedStmt) {
  unsigned Size = llvm::alignTo(sizeof(ACCMasterDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *));
  ACCMasterDirective *Dir = new (Mem) ACCMasterDirective(StartLoc, EndLoc);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCMasterDirective *ACCMasterDirective::CreateEmpty(const ASTContext &C,
                                                    EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCMasterDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *));
  return new (Mem) ACCMasterDirective();
}

ACCCriticalDirective *ACCCriticalDirective::Create(
    const ASTContext &C, const DeclarationNameInfo &Name,
    SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCCriticalDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCCriticalDirective *Dir =
      new (Mem) ACCCriticalDirective(Name, StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCCriticalDirective *ACCCriticalDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCCriticalDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCCriticalDirective(NumClauses);
}

ACCParallelLoopDirective *ACCParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_parallel_loop));

  ACCParallelLoopDirective *Dir = new (Mem)
      ACCParallelLoopDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCParallelLoopDirective *
ACCParallelLoopDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                     unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_parallel_loop));
  return new (Mem) ACCParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCParallelLoopSimdDirective *ACCParallelLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_parallel_loop_simd));
  ACCParallelLoopSimdDirective *Dir = new (Mem) ACCParallelLoopSimdDirective(
      StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCParallelLoopSimdDirective *
ACCParallelLoopSimdDirective::CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses,
                                         unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_parallel_loop_simd));
  return new (Mem) ACCParallelLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCParallelSectionsDirective *ACCParallelSectionsDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, bool HasCancel) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelSectionsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCParallelSectionsDirective *Dir =
      new (Mem) ACCParallelSectionsDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCParallelSectionsDirective *
ACCParallelSectionsDirective::CreateEmpty(const ASTContext &C,
                                          unsigned NumClauses, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelSectionsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCParallelSectionsDirective(NumClauses);
}

ACCTaskDirective *
ACCTaskDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                         SourceLocation EndLoc, ArrayRef<ACCClause *> Clauses,
                         Stmt *AssociatedStmt, bool HasCancel) {
  unsigned Size = llvm::alignTo(sizeof(ACCTaskDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTaskDirective *Dir =
      new (Mem) ACCTaskDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCTaskDirective *ACCTaskDirective::CreateEmpty(const ASTContext &C,
                                                unsigned NumClauses,
                                                EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTaskDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTaskDirective(NumClauses);
}

ACCTaskyieldDirective *ACCTaskyieldDirective::Create(const ASTContext &C,
                                                     SourceLocation StartLoc,
                                                     SourceLocation EndLoc) {
  void *Mem = C.Allocate(sizeof(ACCTaskyieldDirective));
  ACCTaskyieldDirective *Dir =
      new (Mem) ACCTaskyieldDirective(StartLoc, EndLoc);
  return Dir;
}

ACCTaskyieldDirective *ACCTaskyieldDirective::CreateEmpty(const ASTContext &C,
                                                          EmptyShell) {
  void *Mem = C.Allocate(sizeof(ACCTaskyieldDirective));
  return new (Mem) ACCTaskyieldDirective();
}

ACCBarrierDirective *ACCBarrierDirective::Create(const ASTContext &C,
                                                 SourceLocation StartLoc,
                                                 SourceLocation EndLoc) {
  void *Mem = C.Allocate(sizeof(ACCBarrierDirective));
  ACCBarrierDirective *Dir = new (Mem) ACCBarrierDirective(StartLoc, EndLoc);
  return Dir;
}

ACCBarrierDirective *ACCBarrierDirective::CreateEmpty(const ASTContext &C,
                                                      EmptyShell) {
  void *Mem = C.Allocate(sizeof(ACCBarrierDirective));
  return new (Mem) ACCBarrierDirective();
}

ACCTaskwaitDirective *ACCTaskwaitDirective::Create(const ASTContext &C,
                                                   SourceLocation StartLoc,
                                                   SourceLocation EndLoc) {
  void *Mem = C.Allocate(sizeof(ACCTaskwaitDirective));
  ACCTaskwaitDirective *Dir = new (Mem) ACCTaskwaitDirective(StartLoc, EndLoc);
  return Dir;
}

ACCTaskwaitDirective *ACCTaskwaitDirective::CreateEmpty(const ASTContext &C,
                                                        EmptyShell) {
  void *Mem = C.Allocate(sizeof(ACCTaskwaitDirective));
  return new (Mem) ACCTaskwaitDirective();
}

ACCTaskgroupDirective *ACCTaskgroupDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, Expr *ReductionRef) {
  unsigned Size = llvm::alignTo(sizeof(ACCTaskgroupDirective) +
                                    sizeof(ACCClause *) * Clauses.size(),
                                alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *) + sizeof(Expr *));
  ACCTaskgroupDirective *Dir =
      new (Mem) ACCTaskgroupDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setReductionRef(ReductionRef);
  Dir->setClauses(Clauses);
  return Dir;
}

ACCTaskgroupDirective *ACCTaskgroupDirective::CreateEmpty(const ASTContext &C,
                                                          unsigned NumClauses,
                                                          EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTaskgroupDirective) +
                                    sizeof(ACCClause *) * NumClauses,
                                alignof(Stmt *));
  void *Mem = C.Allocate(Size + sizeof(Stmt *) + sizeof(Expr *));
  return new (Mem) ACCTaskgroupDirective(NumClauses);
}

ACCCancellationPointDirective *ACCCancellationPointDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    OpenACCDirectiveKind CancelRegion) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCCancellationPointDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size);
  ACCCancellationPointDirective *Dir =
      new (Mem) ACCCancellationPointDirective(StartLoc, EndLoc);
  Dir->setCancelRegion(CancelRegion);
  return Dir;
}

ACCCancellationPointDirective *
ACCCancellationPointDirective::CreateEmpty(const ASTContext &C, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCCancellationPointDirective), alignof(Stmt *));
  void *Mem = C.Allocate(Size);
  return new (Mem) ACCCancellationPointDirective();
}

ACCCancelDirective *
ACCCancelDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                           SourceLocation EndLoc, ArrayRef<ACCClause *> Clauses,
                           OpenACCDirectiveKind CancelRegion) {
  unsigned Size = llvm::alignTo(sizeof(ACCCancelDirective) +
                                    sizeof(ACCClause *) * Clauses.size(),
                                alignof(Stmt *));
  void *Mem = C.Allocate(Size);
  ACCCancelDirective *Dir =
      new (Mem) ACCCancelDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setCancelRegion(CancelRegion);
  return Dir;
}

ACCCancelDirective *ACCCancelDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCCancelDirective) +
                                    sizeof(ACCClause *) * NumClauses,
                                alignof(Stmt *));
  void *Mem = C.Allocate(Size);
  return new (Mem) ACCCancelDirective(NumClauses);
}

ACCFlushDirective *ACCFlushDirective::Create(const ASTContext &C,
                                             SourceLocation StartLoc,
                                             SourceLocation EndLoc,
                                             ArrayRef<ACCClause *> Clauses) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCFlushDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size());
  ACCFlushDirective *Dir =
      new (Mem) ACCFlushDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  return Dir;
}

ACCFlushDirective *ACCFlushDirective::CreateEmpty(const ASTContext &C,
                                                  unsigned NumClauses,
                                                  EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCFlushDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses);
  return new (Mem) ACCFlushDirective(NumClauses);
}

ACCOrderedDirective *ACCOrderedDirective::Create(const ASTContext &C,
                                                 SourceLocation StartLoc,
                                                 SourceLocation EndLoc,
                                                 ArrayRef<ACCClause *> Clauses,
                                                 Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCOrderedDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(Stmt *) + sizeof(ACCClause *) * Clauses.size());
  ACCOrderedDirective *Dir =
      new (Mem) ACCOrderedDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCOrderedDirective *ACCOrderedDirective::CreateEmpty(const ASTContext &C,
                                                      unsigned NumClauses,
                                                      EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCOrderedDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(Stmt *) + sizeof(ACCClause *) * NumClauses);
  return new (Mem) ACCOrderedDirective(NumClauses);
}

ACCAtomicDirective *ACCAtomicDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt, Expr *X, Expr *V,
    Expr *E, Expr *UE, bool IsXLHSInRHSPart, bool IsPostfixUpdate) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCAtomicDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         5 * sizeof(Stmt *));
  ACCAtomicDirective *Dir =
      new (Mem) ACCAtomicDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setX(X);
  Dir->setV(V);
  Dir->setExpr(E);
  Dir->setUpdateExpr(UE);
  Dir->IsXLHSInRHSPart = IsXLHSInRHSPart;
  Dir->IsPostfixUpdate = IsPostfixUpdate;
  return Dir;
}

ACCAtomicDirective *ACCAtomicDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCAtomicDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + 5 * sizeof(Stmt *));
  return new (Mem) ACCAtomicDirective(NumClauses);
}

ACCTargetDirective *ACCTargetDirective::Create(const ASTContext &C,
                                               SourceLocation StartLoc,
                                               SourceLocation EndLoc,
                                               ArrayRef<ACCClause *> Clauses,
                                               Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetDirective *Dir =
      new (Mem) ACCTargetDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetDirective *ACCTargetDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTargetDirective(NumClauses);
}

ACCTargetParallelDirective *ACCTargetParallelDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetParallelDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetParallelDirective *Dir =
      new (Mem) ACCTargetParallelDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetParallelDirective *
ACCTargetParallelDirective::CreateEmpty(const ASTContext &C,
                                        unsigned NumClauses, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetParallelDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTargetParallelDirective(NumClauses);
}

ACCTargetParallelLoopDirective *ACCTargetParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_target_parallel_loop));
  ACCTargetParallelLoopDirective *Dir = new (Mem) ACCTargetParallelLoopDirective(
      StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setHasCancel(HasCancel);
  return Dir;
}

ACCTargetParallelLoopDirective *
ACCTargetParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                           unsigned NumClauses,
                                           unsigned CollapsedNum, EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_target_parallel_loop));
  return new (Mem) ACCTargetParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCTargetDataDirective *ACCTargetDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetDataDirective *Dir =
      new (Mem) ACCTargetDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetDataDirective *ACCTargetDataDirective::CreateEmpty(const ASTContext &C,
                                                            unsigned N,
                                                            EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCTargetDataDirective(N);
}

ACCTargetEnterDataDirective *ACCTargetEnterDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetEnterDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetEnterDataDirective *Dir =
      new (Mem) ACCTargetEnterDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetEnterDataDirective *
ACCTargetEnterDataDirective::CreateEmpty(const ASTContext &C, unsigned N,
                                         EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetEnterDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCTargetEnterDataDirective(N);
}

ACCTargetExitDataDirective *ACCTargetExitDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetExitDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetExitDataDirective *Dir =
      new (Mem) ACCTargetExitDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetExitDataDirective *
ACCTargetExitDataDirective::CreateEmpty(const ASTContext &C, unsigned N,
                                        EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCTargetExitDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCTargetExitDataDirective(N);
}

ACCTeamsDirective *ACCTeamsDirective::Create(const ASTContext &C,
                                             SourceLocation StartLoc,
                                             SourceLocation EndLoc,
                                             ArrayRef<ACCClause *> Clauses,
                                             Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTeamsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTeamsDirective *Dir =
      new (Mem) ACCTeamsDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTeamsDirective *ACCTeamsDirective::CreateEmpty(const ASTContext &C,
                                                  unsigned NumClauses,
                                                  EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTeamsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTeamsDirective(NumClauses);
}

ACCTaskLoopDirective *ACCTaskLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_taskloop));
  ACCTaskLoopDirective *Dir = new (Mem)
      ACCTaskLoopDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTaskLoopDirective *ACCTaskLoopDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        unsigned CollapsedNum,
                                                        EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_taskloop));
  return new (Mem) ACCTaskLoopDirective(CollapsedNum, NumClauses);
}

ACCTaskLoopSimdDirective *ACCTaskLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_taskloop_simd));
  ACCTaskLoopSimdDirective *Dir = new (Mem)
      ACCTaskLoopSimdDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTaskLoopSimdDirective *
ACCTaskLoopSimdDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                      unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_taskloop_simd));
  return new (Mem) ACCTaskLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCDistributeDirective *ACCDistributeDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_distribute));
  ACCDistributeDirective *Dir = new (Mem)
      ACCDistributeDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCDistributeDirective *
ACCDistributeDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                    unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_distribute));
  return new (Mem) ACCDistributeDirective(CollapsedNum, NumClauses);
}

ACCTargetUpdateDirective *ACCTargetUpdateDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetUpdateDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetUpdateDirective *Dir =
      new (Mem) ACCTargetUpdateDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetUpdateDirective *
ACCTargetUpdateDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                      EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetUpdateDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTargetUpdateDirective(NumClauses);
}

ACCDistributeParallelLoopDirective *ACCDistributeParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop));
  ACCDistributeParallelLoopDirective *Dir =
      new (Mem) ACCDistributeParallelLoopDirective(StartLoc, EndLoc,
                                                  CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  Dir->HasCancel = HasCancel;
  return Dir;
}

ACCDistributeParallelLoopDirective *
ACCDistributeParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop));
  return new (Mem) ACCDistributeParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCDistributeParallelLoopSimdDirective *
ACCDistributeParallelLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopSimdDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop_simd));
  ACCDistributeParallelLoopSimdDirective *Dir = new (Mem)
      ACCDistributeParallelLoopSimdDirective(StartLoc, EndLoc, CollapsedNum,
                                            Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  return Dir;
}

ACCDistributeParallelLoopSimdDirective *
ACCDistributeParallelLoopSimdDirective::CreateEmpty(const ASTContext &C,
                                                   unsigned NumClauses,
                                                   unsigned CollapsedNum,
                                                   EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopSimdDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop_simd));
  return new (Mem)
      ACCDistributeParallelLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCDistributeSimdDirective *ACCDistributeSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_simd));
  ACCDistributeSimdDirective *Dir = new (Mem) ACCDistributeSimdDirective(
      StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCDistributeSimdDirective *
ACCDistributeSimdDirective::CreateEmpty(const ASTContext &C,
                                        unsigned NumClauses,
                                        unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_simd));
  return new (Mem) ACCDistributeSimdDirective(CollapsedNum, NumClauses);
}

ACCTargetParallelLoopSimdDirective *ACCTargetParallelLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopSimdDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * 
          numLoopChildren(CollapsedNum, ACCD_target_parallel_loop_simd));
  ACCTargetParallelLoopSimdDirective *Dir = 
      new (Mem) ACCTargetParallelLoopSimdDirective(StartLoc, EndLoc,
                                                  CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTargetParallelLoopSimdDirective *
ACCTargetParallelLoopSimdDirective::CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopSimdDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * 
          numLoopChildren(CollapsedNum, ACCD_target_parallel_loop_simd));
  return new (Mem) ACCTargetParallelLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCTargetSimdDirective *
ACCTargetSimdDirective::Create(const ASTContext &C, SourceLocation StartLoc, 
                               SourceLocation EndLoc, unsigned CollapsedNum,
                               ArrayRef<ACCClause *> Clauses,
                               Stmt *AssociatedStmt, const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) * 
                             numLoopChildren(CollapsedNum, ACCD_target_simd));
  ACCTargetSimdDirective *Dir = new (Mem)
      ACCTargetSimdDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTargetSimdDirective *
ACCTargetSimdDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                    unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetSimdDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) * 
                             numLoopChildren(CollapsedNum, ACCD_target_simd));
  return new (Mem) ACCTargetSimdDirective(CollapsedNum, NumClauses);
}

ACCTeamsDistributeDirective *ACCTeamsDistributeDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTeamsDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_teams_distribute));
  ACCTeamsDistributeDirective *Dir = new (Mem) ACCTeamsDistributeDirective(
      StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTeamsDistributeDirective *
ACCTeamsDistributeDirective::CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses,
                                         unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTeamsDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_teams_distribute));
  return new (Mem) ACCTeamsDistributeDirective(CollapsedNum, NumClauses);
}

ACCTeamsDistributeSimdDirective *ACCTeamsDistributeSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCTeamsDistributeSimdDirective),
                                alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum, ACCD_teams_distribute_simd));
  ACCTeamsDistributeSimdDirective *Dir =
      new (Mem) ACCTeamsDistributeSimdDirective(StartLoc, EndLoc, CollapsedNum,
                                                Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTeamsDistributeSimdDirective *ACCTeamsDistributeSimdDirective::CreateEmpty(
    const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
    EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTeamsDistributeSimdDirective),
                                alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum, ACCD_teams_distribute_simd));
  return new (Mem) ACCTeamsDistributeSimdDirective(CollapsedNum, NumClauses);
}

ACCTeamsDistributeParallelLoopSimdDirective *
ACCTeamsDistributeParallelLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCTeamsDistributeParallelLoopSimdDirective),
                            alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum,
                                     ACCD_teams_distribute_parallel_loop_simd));
  ACCTeamsDistributeParallelLoopSimdDirective *Dir = new (Mem)
      ACCTeamsDistributeParallelLoopSimdDirective(StartLoc, EndLoc, CollapsedNum,
                                                 Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  return Dir;
}

ACCTeamsDistributeParallelLoopSimdDirective *
ACCTeamsDistributeParallelLoopSimdDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        unsigned CollapsedNum,
                                                        EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTeamsDistributeParallelLoopSimdDirective),
                            alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum,
                                     ACCD_teams_distribute_parallel_loop_simd));
  return new (Mem)
      ACCTeamsDistributeParallelLoopSimdDirective(CollapsedNum, NumClauses);
}

ACCTeamsDistributeParallelLoopDirective *
ACCTeamsDistributeParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  auto Size = llvm::alignTo(sizeof(ACCTeamsDistributeParallelLoopDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_teams_distribute_parallel_loop));
  ACCTeamsDistributeParallelLoopDirective *Dir = new (Mem)
      ACCTeamsDistributeParallelLoopDirective(StartLoc, EndLoc, CollapsedNum,
                                             Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  Dir->HasCancel = HasCancel;
  return Dir;
}

ACCTeamsDistributeParallelLoopDirective *
ACCTeamsDistributeParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    unsigned CollapsedNum,
                                                    EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTeamsDistributeParallelLoopDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_teams_distribute_parallel_loop));
  return new (Mem)
      ACCTeamsDistributeParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCTargetTeamsDirective *ACCTargetTeamsDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetTeamsDirective *Dir =
      new (Mem) ACCTargetTeamsDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetTeamsDirective *
ACCTargetTeamsDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                     EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTargetTeamsDirective(NumClauses);
}

ACCTargetTeamsDistributeDirective *ACCTargetTeamsDistributeDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCTargetTeamsDistributeDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_teams_distribute));
  ACCTargetTeamsDistributeDirective *Dir =
      new (Mem) ACCTargetTeamsDistributeDirective(StartLoc, EndLoc, CollapsedNum,
                                                  Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTargetTeamsDistributeDirective *
ACCTargetTeamsDistributeDirective::CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTargetTeamsDistributeDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
           numLoopChildren(CollapsedNum, ACCD_target_teams_distribute));
  return new (Mem) ACCTargetTeamsDistributeDirective(CollapsedNum, NumClauses);
}

ACCTargetTeamsDistributeParallelLoopDirective *
ACCTargetTeamsDistributeParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDistributeParallelLoopDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_teams_distribute_parallel_loop));
  ACCTargetTeamsDistributeParallelLoopDirective *Dir =
      new (Mem) ACCTargetTeamsDistributeParallelLoopDirective(
           StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  Dir->HasCancel = HasCancel;
  return Dir;
}

ACCTargetTeamsDistributeParallelLoopDirective *
ACCTargetTeamsDistributeParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                                          unsigned NumClauses,
                                                          unsigned CollapsedNum,
                                                          EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDistributeParallelLoopDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
           numLoopChildren(CollapsedNum,
                           ACCD_target_teams_distribute_parallel_loop));
  return new (Mem)
      ACCTargetTeamsDistributeParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCTargetTeamsDistributeParallelLoopSimdDirective *
ACCTargetTeamsDistributeParallelLoopSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDistributeParallelLoopSimdDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_teams_distribute_parallel_loop_simd));
  ACCTargetTeamsDistributeParallelLoopSimdDirective *Dir =
      new (Mem) ACCTargetTeamsDistributeParallelLoopSimdDirective(
           StartLoc, EndLoc, CollapsedNum, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setPrevLowerBoundVariable(Exprs.PrevLB);
  Dir->setPrevUpperBoundVariable(Exprs.PrevUB);
  Dir->setDistInc(Exprs.DistInc);
  Dir->setPrevEnsureUpperBound(Exprs.PrevEUB);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  Dir->setCombinedLowerBoundVariable(Exprs.DistCombinedFields.LB);
  Dir->setCombinedUpperBoundVariable(Exprs.DistCombinedFields.UB);
  Dir->setCombinedEnsureUpperBound(Exprs.DistCombinedFields.EUB);
  Dir->setCombinedInit(Exprs.DistCombinedFields.Init);
  Dir->setCombinedCond(Exprs.DistCombinedFields.Cond);
  Dir->setCombinedNextLowerBound(Exprs.DistCombinedFields.NLB);
  Dir->setCombinedNextUpperBound(Exprs.DistCombinedFields.NUB);
  return Dir;
}

ACCTargetTeamsDistributeParallelLoopSimdDirective *
ACCTargetTeamsDistributeParallelLoopSimdDirective::CreateEmpty(
    const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
    EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetTeamsDistributeParallelLoopSimdDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_teams_distribute_parallel_loop_simd));
  return new (Mem) ACCTargetTeamsDistributeParallelLoopSimdDirective(
      CollapsedNum, NumClauses);
}

ACCTargetTeamsDistributeSimdDirective *
ACCTargetTeamsDistributeSimdDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCTargetTeamsDistributeSimdDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_teams_distribute_simd));
  ACCTargetTeamsDistributeSimdDirective *Dir = new (Mem)
      ACCTargetTeamsDistributeSimdDirective(StartLoc, EndLoc, CollapsedNum,
                                            Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  Dir->setIterationVariable(Exprs.IterationVarRef);
  Dir->setLastIteration(Exprs.LastIteration);
  Dir->setCalcLastIteration(Exprs.CalcLastIteration);
  Dir->setPreCond(Exprs.PreCond);
  Dir->setCond(Exprs.Cond);
  Dir->setInit(Exprs.Init);
  Dir->setInc(Exprs.Inc);
  Dir->setIsLastIterVariable(Exprs.IL);
  Dir->setLowerBoundVariable(Exprs.LB);
  Dir->setUpperBoundVariable(Exprs.UB);
  Dir->setStrideVariable(Exprs.ST);
  Dir->setEnsureUpperBound(Exprs.EUB);
  Dir->setNextLowerBound(Exprs.NLB);
  Dir->setNextUpperBound(Exprs.NUB);
  Dir->setNumIterations(Exprs.NumIterations);
  Dir->setCounters(Exprs.Counters);
  Dir->setPrivateCounters(Exprs.PrivateCounters);
  Dir->setInits(Exprs.Inits);
  Dir->setUpdates(Exprs.Updates);
  Dir->setFinals(Exprs.Finals);
  Dir->setPreInits(Exprs.PreInits);
  return Dir;
}

ACCTargetTeamsDistributeSimdDirective *
ACCTargetTeamsDistributeSimdDirective::CreateEmpty(const ASTContext &C,
                                                   unsigned NumClauses,
                                                   unsigned CollapsedNum,
                                                   EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTargetTeamsDistributeSimdDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_teams_distribute_simd));
  return new (Mem)
      ACCTargetTeamsDistributeSimdDirective(CollapsedNum, NumClauses);
}
