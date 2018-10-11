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

ACCVectorDirective *
ACCVectorDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                         SourceLocation EndLoc, unsigned CollapsedNum,
                         ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
                         const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCVectorDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_vector));
  ACCVectorDirective *Dir = new (Mem)
      ACCVectorDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
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

ACCVectorDirective *ACCVectorDirective::CreateEmpty(const ASTContext &C,
                                                unsigned NumClauses,
                                                unsigned CollapsedNum,
                                                EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCVectorDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_vector));
  return new (Mem) ACCVectorDirective(CollapsedNum, NumClauses);
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

ACCLoopVectorDirective *
ACCLoopVectorDirective::Create(const ASTContext &C, SourceLocation StartLoc,
                            SourceLocation EndLoc, unsigned CollapsedNum,
                            ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
                            const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCLoopVectorDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop_vector));
  ACCLoopVectorDirective *Dir = new (Mem)
      ACCLoopVectorDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
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

ACCLoopVectorDirective *ACCLoopVectorDirective::CreateEmpty(const ASTContext &C,
                                                      unsigned NumClauses,
                                                      unsigned CollapsedNum,
                                                      EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCLoopVectorDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_loop_vector));
  return new (Mem) ACCLoopVectorDirective(CollapsedNum, NumClauses);
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

ACCParallelLoopVectorDirective *ACCParallelLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_parallel_loop_vector));
  ACCParallelLoopVectorDirective *Dir = new (Mem) ACCParallelLoopVectorDirective(
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

ACCParallelLoopVectorDirective *
ACCParallelLoopVectorDirective::CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses,
                                         unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCParallelLoopVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_parallel_loop_vector));
  return new (Mem) ACCParallelLoopVectorDirective(CollapsedNum, NumClauses);
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

ACCDataDirective *ACCDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCDataDirective *Dir =
      new (Mem) ACCDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCDataDirective *ACCDataDirective::CreateEmpty(const ASTContext &C,
                                                            unsigned N,
                                                            EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCDataDirective(N);
}

ACCEnterDataDirective *ACCEnterDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCEnterDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCEnterDataDirective *Dir =
      new (Mem) ACCEnterDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCEnterDataDirective *
ACCEnterDataDirective::CreateEmpty(const ASTContext &C, unsigned N,
                                         EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCEnterDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCEnterDataDirective(N);
}

ACCExitDataDirective *ACCExitDataDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCExitDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCExitDataDirective *Dir =
      new (Mem) ACCExitDataDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCExitDataDirective *
ACCExitDataDirective::CreateEmpty(const ASTContext &C, unsigned N,
                                        EmptyShell) {
  void *Mem = C.Allocate(
      llvm::alignTo(sizeof(ACCExitDataDirective), alignof(ACCClause *)) +
      sizeof(ACCClause *) * N + sizeof(Stmt *));
  return new (Mem) ACCExitDataDirective(N);
}

ACCGangDirective *ACCGangDirective::Create(const ASTContext &C,
                                             SourceLocation StartLoc,
                                             SourceLocation EndLoc,
                                             ArrayRef<ACCClause *> Clauses,
                                             Stmt *AssociatedStmt) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCGangDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCGangDirective *Dir =
      new (Mem) ACCGangDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCGangDirective *ACCGangDirective::CreateEmpty(const ASTContext &C,
                                                  unsigned NumClauses,
                                                  EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCGangDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCGangDirective(NumClauses);
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

ACCTaskLoopVectorDirective *ACCTaskLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_taskloop_vector));
  ACCTaskLoopVectorDirective *Dir = new (Mem)
      ACCTaskLoopVectorDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
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

ACCTaskLoopVectorDirective *
ACCTaskLoopVectorDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                      unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTaskLoopVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) *
                             numLoopChildren(CollapsedNum, ACCD_taskloop_vector));
  return new (Mem) ACCTaskLoopVectorDirective(CollapsedNum, NumClauses);
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

ACCDistributeParallelLoopVectorDirective *
ACCDistributeParallelLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopVectorDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop_vector));
  ACCDistributeParallelLoopVectorDirective *Dir = new (Mem)
      ACCDistributeParallelLoopVectorDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCDistributeParallelLoopVectorDirective *
ACCDistributeParallelLoopVectorDirective::CreateEmpty(const ASTContext &C,
                                                   unsigned NumClauses,
                                                   unsigned CollapsedNum,
                                                   EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCDistributeParallelLoopVectorDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_parallel_loop_vector));
  return new (Mem)
      ACCDistributeParallelLoopVectorDirective(CollapsedNum, NumClauses);
}

ACCDistributeVectorDirective *ACCDistributeVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_vector));
  ACCDistributeVectorDirective *Dir = new (Mem) ACCDistributeVectorDirective(
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

ACCDistributeVectorDirective *
ACCDistributeVectorDirective::CreateEmpty(const ASTContext &C,
                                        unsigned NumClauses,
                                        unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCDistributeVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_distribute_vector));
  return new (Mem) ACCDistributeVectorDirective(CollapsedNum, NumClauses);
}

ACCTargetParallelLoopVectorDirective *ACCTargetParallelLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopVectorDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * 
          numLoopChildren(CollapsedNum, ACCD_target_parallel_loop_vector));
  ACCTargetParallelLoopVectorDirective *Dir = 
      new (Mem) ACCTargetParallelLoopVectorDirective(StartLoc, EndLoc,
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

ACCTargetParallelLoopVectorDirective *
ACCTargetParallelLoopVectorDirective::CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCTargetParallelLoopVectorDirective),
                                alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * 
          numLoopChildren(CollapsedNum, ACCD_target_parallel_loop_vector));
  return new (Mem) ACCTargetParallelLoopVectorDirective(CollapsedNum, NumClauses);
}

ACCTargetVectorDirective *
ACCTargetVectorDirective::Create(const ASTContext &C, SourceLocation StartLoc, 
                               SourceLocation EndLoc, unsigned CollapsedNum,
                               ArrayRef<ACCClause *> Clauses,
                               Stmt *AssociatedStmt, const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                         sizeof(Stmt *) * 
                             numLoopChildren(CollapsedNum, ACCD_target_vector));
  ACCTargetVectorDirective *Dir = new (Mem)
      ACCTargetVectorDirective(StartLoc, EndLoc, CollapsedNum, Clauses.size());
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

ACCTargetVectorDirective *
ACCTargetVectorDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                    unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCTargetVectorDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                         sizeof(Stmt *) * 
                             numLoopChildren(CollapsedNum, ACCD_target_vector));
  return new (Mem) ACCTargetVectorDirective(CollapsedNum, NumClauses);
}

ACCGangDistributeDirective *ACCGangDistributeDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCGangDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_gang_distribute));
  ACCGangDistributeDirective *Dir = new (Mem) ACCGangDistributeDirective(
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

ACCGangDistributeDirective *
ACCGangDistributeDirective::CreateEmpty(const ASTContext &C,
                                         unsigned NumClauses,
                                         unsigned CollapsedNum, EmptyShell) {
  unsigned Size =
      llvm::alignTo(sizeof(ACCGangDistributeDirective), alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) * numLoopChildren(CollapsedNum, ACCD_gang_distribute));
  return new (Mem) ACCGangDistributeDirective(CollapsedNum, NumClauses);
}

ACCGangDistributeVectorDirective *ACCGangDistributeVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  unsigned Size = llvm::alignTo(sizeof(ACCGangDistributeVectorDirective),
                                alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum, ACCD_gang_distribute_vector));
  ACCGangDistributeVectorDirective *Dir =
      new (Mem) ACCGangDistributeVectorDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCGangDistributeVectorDirective *ACCGangDistributeVectorDirective::CreateEmpty(
    const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
    EmptyShell) {
  unsigned Size = llvm::alignTo(sizeof(ACCGangDistributeVectorDirective),
                                alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum, ACCD_gang_distribute_vector));
  return new (Mem) ACCGangDistributeVectorDirective(CollapsedNum, NumClauses);
}

ACCGangDistributeParallelLoopVectorDirective *
ACCGangDistributeParallelLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCGangDistributeParallelLoopVectorDirective),
                            alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum,
                                     ACCD_gang_distribute_parallel_loop_vector));
  ACCGangDistributeParallelLoopVectorDirective *Dir = new (Mem)
      ACCGangDistributeParallelLoopVectorDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCGangDistributeParallelLoopVectorDirective *
ACCGangDistributeParallelLoopVectorDirective::CreateEmpty(const ASTContext &C,
                                                        unsigned NumClauses,
                                                        unsigned CollapsedNum,
                                                        EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCGangDistributeParallelLoopVectorDirective),
                            alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses +
                 sizeof(Stmt *) *
                     numLoopChildren(CollapsedNum,
                                     ACCD_gang_distribute_parallel_loop_vector));
  return new (Mem)
      ACCGangDistributeParallelLoopVectorDirective(CollapsedNum, NumClauses);
}

ACCGangDistributeParallelLoopDirective *
ACCGangDistributeParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  auto Size = llvm::alignTo(sizeof(ACCGangDistributeParallelLoopDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_gang_distribute_parallel_loop));
  ACCGangDistributeParallelLoopDirective *Dir = new (Mem)
      ACCGangDistributeParallelLoopDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCGangDistributeParallelLoopDirective *
ACCGangDistributeParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                                    unsigned NumClauses,
                                                    unsigned CollapsedNum,
                                                    EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCGangDistributeParallelLoopDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_gang_distribute_parallel_loop));
  return new (Mem)
      ACCGangDistributeParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCTargetGangDirective *ACCTargetGangDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * Clauses.size() + sizeof(Stmt *));
  ACCTargetGangDirective *Dir =
      new (Mem) ACCTargetGangDirective(StartLoc, EndLoc, Clauses.size());
  Dir->setClauses(Clauses);
  Dir->setAssociatedStmt(AssociatedStmt);
  return Dir;
}

ACCTargetGangDirective *
ACCTargetGangDirective::CreateEmpty(const ASTContext &C, unsigned NumClauses,
                                     EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDirective), alignof(ACCClause *));
  void *Mem =
      C.Allocate(Size + sizeof(ACCClause *) * NumClauses + sizeof(Stmt *));
  return new (Mem) ACCTargetGangDirective(NumClauses);
}

ACCTargetGangDistributeDirective *ACCTargetGangDistributeDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCTargetGangDistributeDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_gang_distribute));
  ACCTargetGangDistributeDirective *Dir =
      new (Mem) ACCTargetGangDistributeDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCTargetGangDistributeDirective *
ACCTargetGangDistributeDirective::CreateEmpty(const ASTContext &C,
                                               unsigned NumClauses,
                                               unsigned CollapsedNum,
                                               EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTargetGangDistributeDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
           numLoopChildren(CollapsedNum, ACCD_target_gang_distribute));
  return new (Mem) ACCTargetGangDistributeDirective(CollapsedNum, NumClauses);
}

ACCTargetGangDistributeParallelLoopDirective *
ACCTargetGangDistributeParallelLoopDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs, bool HasCancel) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDistributeParallelLoopDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_gang_distribute_parallel_loop));
  ACCTargetGangDistributeParallelLoopDirective *Dir =
      new (Mem) ACCTargetGangDistributeParallelLoopDirective(
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

ACCTargetGangDistributeParallelLoopDirective *
ACCTargetGangDistributeParallelLoopDirective::CreateEmpty(const ASTContext &C,
                                                          unsigned NumClauses,
                                                          unsigned CollapsedNum,
                                                          EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDistributeParallelLoopDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
           numLoopChildren(CollapsedNum,
                           ACCD_target_gang_distribute_parallel_loop));
  return new (Mem)
      ACCTargetGangDistributeParallelLoopDirective(CollapsedNum, NumClauses);
}

ACCTargetGangDistributeParallelLoopVectorDirective *
ACCTargetGangDistributeParallelLoopVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDistributeParallelLoopVectorDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_gang_distribute_parallel_loop_vector));
  ACCTargetGangDistributeParallelLoopVectorDirective *Dir =
      new (Mem) ACCTargetGangDistributeParallelLoopVectorDirective(
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

ACCTargetGangDistributeParallelLoopVectorDirective *
ACCTargetGangDistributeParallelLoopVectorDirective::CreateEmpty(
    const ASTContext &C, unsigned NumClauses, unsigned CollapsedNum,
    EmptyShell) {
  auto Size =
      llvm::alignTo(sizeof(ACCTargetGangDistributeParallelLoopVectorDirective),
                    alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum,
                          ACCD_target_gang_distribute_parallel_loop_vector));
  return new (Mem) ACCTargetGangDistributeParallelLoopVectorDirective(
      CollapsedNum, NumClauses);
}

ACCTargetGangDistributeVectorDirective *
ACCTargetGangDistributeVectorDirective::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation EndLoc,
    unsigned CollapsedNum, ArrayRef<ACCClause *> Clauses, Stmt *AssociatedStmt,
    const HelperExprs &Exprs) {
  auto Size = llvm::alignTo(sizeof(ACCTargetGangDistributeVectorDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * Clauses.size() +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_gang_distribute_vector));
  ACCTargetGangDistributeVectorDirective *Dir = new (Mem)
      ACCTargetGangDistributeVectorDirective(StartLoc, EndLoc, CollapsedNum,
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

ACCTargetGangDistributeVectorDirective *
ACCTargetGangDistributeVectorDirective::CreateEmpty(const ASTContext &C,
                                                   unsigned NumClauses,
                                                   unsigned CollapsedNum,
                                                   EmptyShell) {
  auto Size = llvm::alignTo(sizeof(ACCTargetGangDistributeVectorDirective),
                            alignof(ACCClause *));
  void *Mem = C.Allocate(
      Size + sizeof(ACCClause *) * NumClauses +
      sizeof(Stmt *) *
          numLoopChildren(CollapsedNum, ACCD_target_gang_distribute_vector));
  return new (Mem)
      ACCTargetGangDistributeVectorDirective(CollapsedNum, NumClauses);
}
