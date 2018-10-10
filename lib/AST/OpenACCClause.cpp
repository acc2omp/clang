//===- OpenACCClause.cpp - Classes for OpenACC clauses ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the subclesses of Stmt class declared in OpenACCClause.h
//
//===----------------------------------------------------------------------===//

#include "clang/AST/OpenACCClause.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/LLVM.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"
#include <algorithm>
#include <cassert>

using namespace clang;

ACCClause::child_range ACCClause::children() {
  switch (getClauseKind()) {
  default:
    break;
#define OPENMP_CLAUSE(Name, Class)                                             \
  case ACCC_##Name:                                                            \
    return static_cast<Class *>(this)->children();
#include "clang/Basic/OpenACCKinds.def"
  }
  llvm_unreachable("unknown ACCClause");
}

ACCClauseWithPreInit *ACCClauseWithPreInit::get(ACCClause *C) {
  auto *Res = ACCClauseWithPreInit::get(const_cast<const ACCClause *>(C));
  return Res ? const_cast<ACCClauseWithPreInit *>(Res) : nullptr;
}

const ACCClauseWithPreInit *ACCClauseWithPreInit::get(const ACCClause *C) {
  switch (C->getClauseKind()) {
  case ACCC_schedule:
    return static_cast<const ACCScheduleClause *>(C);
  case ACCC_dist_schedule:
    return static_cast<const ACCDistScheduleClause *>(C);
  case ACCC_firstprivate:
    return static_cast<const ACCFirstprivateClause *>(C);
  case ACCC_lastprivate:
    return static_cast<const ACCLastprivateClause *>(C);
  case ACCC_reduction:
    return static_cast<const ACCReductionClause *>(C);
  case ACCC_task_reduction:
    return static_cast<const ACCTaskReductionClause *>(C);
  case ACCC_in_reduction:
    return static_cast<const ACCInReductionClause *>(C);
  case ACCC_linear:
    return static_cast<const ACCLinearClause *>(C);
  case ACCC_if:
    return static_cast<const ACCIfClause *>(C);
  case ACCC_num_threads:
    return static_cast<const ACCNumThreadsClause *>(C);
  case ACCC_num_teams:
    return static_cast<const ACCNumTeamsClause *>(C);
  case ACCC_thread_limit:
    return static_cast<const ACCThreadLimitClause *>(C);
  case ACCC_device:
    return static_cast<const ACCDeviceClause *>(C);
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_final:
  case ACCC_safelen:
  case ACCC_vectorlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_shared:
  case ACCC_aligned:
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
  case ACCC_vector:
  case ACCC_map:
  case ACCC_create:
  case ACCC_copy:
  case ACCC_copyin:
  case ACCC_copyout:
  case ACCC_delete:
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
    break;
  }

  return nullptr;
}

ACCClauseWithPostUpdate *ACCClauseWithPostUpdate::get(ACCClause *C) {
  auto *Res = ACCClauseWithPostUpdate::get(const_cast<const ACCClause *>(C));
  return Res ? const_cast<ACCClauseWithPostUpdate *>(Res) : nullptr;
}

const ACCClauseWithPostUpdate *ACCClauseWithPostUpdate::get(const ACCClause *C) {
  switch (C->getClauseKind()) {
  case ACCC_lastprivate:
    return static_cast<const ACCLastprivateClause *>(C);
  case ACCC_reduction:
    return static_cast<const ACCReductionClause *>(C);
  case ACCC_task_reduction:
    return static_cast<const ACCTaskReductionClause *>(C);
  case ACCC_in_reduction:
    return static_cast<const ACCInReductionClause *>(C);
  case ACCC_linear:
    return static_cast<const ACCLinearClause *>(C);
  case ACCC_schedule:
  case ACCC_dist_schedule:
  case ACCC_firstprivate:
  case ACCC_default:
  case ACCC_proc_bind:
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_vectorlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_shared:
  case ACCC_aligned:
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
  case ACCC_vector:
  case ACCC_map:
  case ACCC_create:
  case ACCC_copy:
  case ACCC_copyin:
  case ACCC_copyout:
  case ACCC_delete:
  case ACCC_num_teams:
  case ACCC_thread_limit:
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
    break;
  }

  return nullptr;
}

void ACCPrivateClause::setPrivateCopies(ArrayRef<Expr *> VL) {
  assert(VL.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(VL.begin(), VL.end(), varlist_end());
}

ACCPrivateClause *
ACCPrivateClause::Create(const ASTContext &C, SourceLocation StartLoc,
                         SourceLocation LParenLoc, SourceLocation EndLoc,
                         ArrayRef<Expr *> VL, ArrayRef<Expr *> PrivateVL) {
  // Allocate space for private variables and initializer expressions.
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(2 * VL.size()));
  ACCPrivateClause *Clause =
      new (Mem) ACCPrivateClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setPrivateCopies(PrivateVL);
  return Clause;
}

ACCPrivateClause *ACCPrivateClause::CreateEmpty(const ASTContext &C,
                                                unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(2 * N));
  return new (Mem) ACCPrivateClause(N);
}

void ACCFirstprivateClause::setPrivateCopies(ArrayRef<Expr *> VL) {
  assert(VL.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(VL.begin(), VL.end(), varlist_end());
}

void ACCFirstprivateClause::setInits(ArrayRef<Expr *> VL) {
  assert(VL.size() == varlist_size() &&
         "Number of inits is not the same as the preallocated buffer");
  std::copy(VL.begin(), VL.end(), getPrivateCopies().end());
}

ACCFirstprivateClause *
ACCFirstprivateClause::Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> VL, ArrayRef<Expr *> PrivateVL,
                              ArrayRef<Expr *> InitVL, Stmt *PreInit) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(3 * VL.size()));
  ACCFirstprivateClause *Clause =
      new (Mem) ACCFirstprivateClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setPrivateCopies(PrivateVL);
  Clause->setInits(InitVL);
  Clause->setPreInitStmt(PreInit);
  return Clause;
}

ACCFirstprivateClause *ACCFirstprivateClause::CreateEmpty(const ASTContext &C,
                                                          unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(3 * N));
  return new (Mem) ACCFirstprivateClause(N);
}

void ACCLastprivateClause::setPrivateCopies(ArrayRef<Expr *> PrivateCopies) {
  assert(PrivateCopies.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(PrivateCopies.begin(), PrivateCopies.end(), varlist_end());
}

void ACCLastprivateClause::setSourceExprs(ArrayRef<Expr *> SrcExprs) {
  assert(SrcExprs.size() == varlist_size() && "Number of source expressions is "
                                              "not the same as the "
                                              "preallocated buffer");
  std::copy(SrcExprs.begin(), SrcExprs.end(), getPrivateCopies().end());
}

void ACCLastprivateClause::setDestinationExprs(ArrayRef<Expr *> DstExprs) {
  assert(DstExprs.size() == varlist_size() && "Number of destination "
                                              "expressions is not the same as "
                                              "the preallocated buffer");
  std::copy(DstExprs.begin(), DstExprs.end(), getSourceExprs().end());
}

void ACCLastprivateClause::setAssignmentOps(ArrayRef<Expr *> AssignmentOps) {
  assert(AssignmentOps.size() == varlist_size() &&
         "Number of assignment expressions is not the same as the preallocated "
         "buffer");
  std::copy(AssignmentOps.begin(), AssignmentOps.end(),
            getDestinationExprs().end());
}

ACCLastprivateClause *ACCLastprivateClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> SrcExprs,
    ArrayRef<Expr *> DstExprs, ArrayRef<Expr *> AssignmentOps, Stmt *PreInit,
    Expr *PostUpdate) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * VL.size()));
  ACCLastprivateClause *Clause =
      new (Mem) ACCLastprivateClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setSourceExprs(SrcExprs);
  Clause->setDestinationExprs(DstExprs);
  Clause->setAssignmentOps(AssignmentOps);
  Clause->setPreInitStmt(PreInit);
  Clause->setPostUpdateExpr(PostUpdate);
  return Clause;
}

ACCLastprivateClause *ACCLastprivateClause::CreateEmpty(const ASTContext &C,
                                                        unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * N));
  return new (Mem) ACCLastprivateClause(N);
}

ACCSharedClause *ACCSharedClause::Create(const ASTContext &C,
                                         SourceLocation StartLoc,
                                         SourceLocation LParenLoc,
                                         SourceLocation EndLoc,
                                         ArrayRef<Expr *> VL) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(VL.size()));
  ACCSharedClause *Clause =
      new (Mem) ACCSharedClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  return Clause;
}

ACCSharedClause *ACCSharedClause::CreateEmpty(const ASTContext &C, unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(N));
  return new (Mem) ACCSharedClause(N);
}

void ACCLinearClause::setPrivates(ArrayRef<Expr *> PL) {
  assert(PL.size() == varlist_size() &&
         "Number of privates is not the same as the preallocated buffer");
  std::copy(PL.begin(), PL.end(), varlist_end());
}

void ACCLinearClause::setInits(ArrayRef<Expr *> IL) {
  assert(IL.size() == varlist_size() &&
         "Number of inits is not the same as the preallocated buffer");
  std::copy(IL.begin(), IL.end(), getPrivates().end());
}

void ACCLinearClause::setUpdates(ArrayRef<Expr *> UL) {
  assert(UL.size() == varlist_size() &&
         "Number of updates is not the same as the preallocated buffer");
  std::copy(UL.begin(), UL.end(), getInits().end());
}

void ACCLinearClause::setFinals(ArrayRef<Expr *> FL) {
  assert(FL.size() == varlist_size() &&
         "Number of final updates is not the same as the preallocated buffer");
  std::copy(FL.begin(), FL.end(), getUpdates().end());
}

ACCLinearClause *ACCLinearClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    OpenACCLinearClauseKind Modifier, SourceLocation ModifierLoc,
    SourceLocation ColonLoc, SourceLocation EndLoc, ArrayRef<Expr *> VL,
    ArrayRef<Expr *> PL, ArrayRef<Expr *> IL, Expr *Step, Expr *CalcStep,
    Stmt *PreInit, Expr *PostUpdate) {
  // Allocate space for 4 lists (Vars, Inits, Updates, Finals) and 2 expressions
  // (Step and CalcStep).
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * VL.size() + 2));
  ACCLinearClause *Clause = new (Mem) ACCLinearClause(
      StartLoc, LParenLoc, Modifier, ModifierLoc, ColonLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setPrivates(PL);
  Clause->setInits(IL);
  // Fill update and final expressions with zeroes, they are provided later,
  // after the directive construction.
  std::fill(Clause->getInits().end(), Clause->getInits().end() + VL.size(),
            nullptr);
  std::fill(Clause->getUpdates().end(), Clause->getUpdates().end() + VL.size(),
            nullptr);
  Clause->setStep(Step);
  Clause->setCalcStep(CalcStep);
  Clause->setPreInitStmt(PreInit);
  Clause->setPostUpdateExpr(PostUpdate);
  return Clause;
}

ACCLinearClause *ACCLinearClause::CreateEmpty(const ASTContext &C,
                                              unsigned NumVars) {
  // Allocate space for 4 lists (Vars, Inits, Updates, Finals) and 2 expressions
  // (Step and CalcStep).
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * NumVars + 2));
  return new (Mem) ACCLinearClause(NumVars);
}

ACCAlignedClause *
ACCAlignedClause::Create(const ASTContext &C, SourceLocation StartLoc,
                         SourceLocation LParenLoc, SourceLocation ColonLoc,
                         SourceLocation EndLoc, ArrayRef<Expr *> VL, Expr *A) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(VL.size() + 1));
  ACCAlignedClause *Clause = new (Mem)
      ACCAlignedClause(StartLoc, LParenLoc, ColonLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setAlignment(A);
  return Clause;
}

ACCAlignedClause *ACCAlignedClause::CreateEmpty(const ASTContext &C,
                                                unsigned NumVars) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(NumVars + 1));
  return new (Mem) ACCAlignedClause(NumVars);
}

/* void ACCCopyinClause::setSourceExprs(ArrayRef<Expr *> SrcExprs) { */
/*   assert(SrcExprs.size() == varlist_size() && "Number of source expressions is " */
/*                                               "not the same as the " */
/*                                               "preallocated buffer"); */
/*   std::copy(SrcExprs.begin(), SrcExprs.end(), varlist_end()); */
/* } */

/* void ACCCopyinClause::setDestinationExprs(ArrayRef<Expr *> DstExprs) { */
/*   assert(DstExprs.size() == varlist_size() && "Number of destination " */
/*                                               "expressions is not the same as " */
/*                                               "the preallocated buffer"); */
/*   std::copy(DstExprs.begin(), DstExprs.end(), getSourceExprs().end()); */
/* } */

/* void ACCCopyinClause::setAssignmentOps(ArrayRef<Expr *> AssignmentOps) { */
/*   assert(AssignmentOps.size() == varlist_size() && */
/*          "Number of assignment expressions is not the same as the preallocated " */
/*          "buffer"); */
/*   std::copy(AssignmentOps.begin(), AssignmentOps.end(), */
/*             getDestinationExprs().end()); */
/* } */

/* ACCCopyinClause *ACCCopyinClause::Create( */
/*     const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc, */
/*     SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> SrcExprs, */
/*     ArrayRef<Expr *> DstExprs, ArrayRef<Expr *> AssignmentOps) { */
/*   void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(4 * VL.size())); */
/*   ACCCopyinClause *Clause = */
/*       new (Mem) ACCCopyinClause(StartLoc, LParenLoc, EndLoc, VL.size()); */
/*   Clause->setVarRefs(VL); */
/*   Clause->setSourceExprs(SrcExprs); */
/*   Clause->setDestinationExprs(DstExprs); */
/*   Clause->setAssignmentOps(AssignmentOps); */
/*   return Clause; */
/* } */

/* ACCCopyinClause *ACCCopyinClause::CreateEmpty(const ASTContext &C, unsigned N) { */
/*   void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(4 * N)); */
/*   return new (Mem) ACCCopyinClause(N); */
/* } */

void ACCCopyprivateClause::setSourceExprs(ArrayRef<Expr *> SrcExprs) {
  assert(SrcExprs.size() == varlist_size() && "Number of source expressions is "
                                              "not the same as the "
                                              "preallocated buffer");
  std::copy(SrcExprs.begin(), SrcExprs.end(), varlist_end());
}

void ACCCopyprivateClause::setDestinationExprs(ArrayRef<Expr *> DstExprs) {
  assert(DstExprs.size() == varlist_size() && "Number of destination "
                                              "expressions is not the same as "
                                              "the preallocated buffer");
  std::copy(DstExprs.begin(), DstExprs.end(), getSourceExprs().end());
}

void ACCCopyprivateClause::setAssignmentOps(ArrayRef<Expr *> AssignmentOps) {
  assert(AssignmentOps.size() == varlist_size() &&
         "Number of assignment expressions is not the same as the preallocated "
         "buffer");
  std::copy(AssignmentOps.begin(), AssignmentOps.end(),
            getDestinationExprs().end());
}

ACCCopyprivateClause *ACCCopyprivateClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> SrcExprs,
    ArrayRef<Expr *> DstExprs, ArrayRef<Expr *> AssignmentOps) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(4 * VL.size()));
  ACCCopyprivateClause *Clause =
      new (Mem) ACCCopyprivateClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setSourceExprs(SrcExprs);
  Clause->setDestinationExprs(DstExprs);
  Clause->setAssignmentOps(AssignmentOps);
  return Clause;
}

ACCCopyprivateClause *ACCCopyprivateClause::CreateEmpty(const ASTContext &C,
                                                        unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(4 * N));
  return new (Mem) ACCCopyprivateClause(N);
}

void ACCReductionClause::setPrivates(ArrayRef<Expr *> Privates) {
  assert(Privates.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(Privates.begin(), Privates.end(), varlist_end());
}

void ACCReductionClause::setLHSExprs(ArrayRef<Expr *> LHSExprs) {
  assert(
      LHSExprs.size() == varlist_size() &&
      "Number of LHS expressions is not the same as the preallocated buffer");
  std::copy(LHSExprs.begin(), LHSExprs.end(), getPrivates().end());
}

void ACCReductionClause::setRHSExprs(ArrayRef<Expr *> RHSExprs) {
  assert(
      RHSExprs.size() == varlist_size() &&
      "Number of RHS expressions is not the same as the preallocated buffer");
  std::copy(RHSExprs.begin(), RHSExprs.end(), getLHSExprs().end());
}

void ACCReductionClause::setReductionOps(ArrayRef<Expr *> ReductionOps) {
  assert(ReductionOps.size() == varlist_size() && "Number of reduction "
                                                  "expressions is not the same "
                                                  "as the preallocated buffer");
  std::copy(ReductionOps.begin(), ReductionOps.end(), getRHSExprs().end());
}

ACCReductionClause *ACCReductionClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, SourceLocation ColonLoc, ArrayRef<Expr *> VL,
    NestedNameSpecifierLoc QualifierLoc, const DeclarationNameInfo &NameInfo,
    ArrayRef<Expr *> Privates, ArrayRef<Expr *> LHSExprs,
    ArrayRef<Expr *> RHSExprs, ArrayRef<Expr *> ReductionOps, Stmt *PreInit,
    Expr *PostUpdate) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * VL.size()));
  ACCReductionClause *Clause = new (Mem) ACCReductionClause(
      StartLoc, LParenLoc, EndLoc, ColonLoc, VL.size(), QualifierLoc, NameInfo);
  Clause->setVarRefs(VL);
  Clause->setPrivates(Privates);
  Clause->setLHSExprs(LHSExprs);
  Clause->setRHSExprs(RHSExprs);
  Clause->setReductionOps(ReductionOps);
  Clause->setPreInitStmt(PreInit);
  Clause->setPostUpdateExpr(PostUpdate);
  return Clause;
}

ACCReductionClause *ACCReductionClause::CreateEmpty(const ASTContext &C,
                                                    unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * N));
  return new (Mem) ACCReductionClause(N);
}

void ACCTaskReductionClause::setPrivates(ArrayRef<Expr *> Privates) {
  assert(Privates.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(Privates.begin(), Privates.end(), varlist_end());
}

void ACCTaskReductionClause::setLHSExprs(ArrayRef<Expr *> LHSExprs) {
  assert(
      LHSExprs.size() == varlist_size() &&
      "Number of LHS expressions is not the same as the preallocated buffer");
  std::copy(LHSExprs.begin(), LHSExprs.end(), getPrivates().end());
}

void ACCTaskReductionClause::setRHSExprs(ArrayRef<Expr *> RHSExprs) {
  assert(
      RHSExprs.size() == varlist_size() &&
      "Number of RHS expressions is not the same as the preallocated buffer");
  std::copy(RHSExprs.begin(), RHSExprs.end(), getLHSExprs().end());
}

void ACCTaskReductionClause::setReductionOps(ArrayRef<Expr *> ReductionOps) {
  assert(ReductionOps.size() == varlist_size() && "Number of task reduction "
                                                  "expressions is not the same "
                                                  "as the preallocated buffer");
  std::copy(ReductionOps.begin(), ReductionOps.end(), getRHSExprs().end());
}

ACCTaskReductionClause *ACCTaskReductionClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, SourceLocation ColonLoc, ArrayRef<Expr *> VL,
    NestedNameSpecifierLoc QualifierLoc, const DeclarationNameInfo &NameInfo,
    ArrayRef<Expr *> Privates, ArrayRef<Expr *> LHSExprs,
    ArrayRef<Expr *> RHSExprs, ArrayRef<Expr *> ReductionOps, Stmt *PreInit,
    Expr *PostUpdate) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * VL.size()));
  ACCTaskReductionClause *Clause = new (Mem) ACCTaskReductionClause(
      StartLoc, LParenLoc, EndLoc, ColonLoc, VL.size(), QualifierLoc, NameInfo);
  Clause->setVarRefs(VL);
  Clause->setPrivates(Privates);
  Clause->setLHSExprs(LHSExprs);
  Clause->setRHSExprs(RHSExprs);
  Clause->setReductionOps(ReductionOps);
  Clause->setPreInitStmt(PreInit);
  Clause->setPostUpdateExpr(PostUpdate);
  return Clause;
}

ACCTaskReductionClause *ACCTaskReductionClause::CreateEmpty(const ASTContext &C,
                                                            unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(5 * N));
  return new (Mem) ACCTaskReductionClause(N);
}

void ACCInReductionClause::setPrivates(ArrayRef<Expr *> Privates) {
  assert(Privates.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(Privates.begin(), Privates.end(), varlist_end());
}

void ACCInReductionClause::setLHSExprs(ArrayRef<Expr *> LHSExprs) {
  assert(
      LHSExprs.size() == varlist_size() &&
      "Number of LHS expressions is not the same as the preallocated buffer");
  std::copy(LHSExprs.begin(), LHSExprs.end(), getPrivates().end());
}

void ACCInReductionClause::setRHSExprs(ArrayRef<Expr *> RHSExprs) {
  assert(
      RHSExprs.size() == varlist_size() &&
      "Number of RHS expressions is not the same as the preallocated buffer");
  std::copy(RHSExprs.begin(), RHSExprs.end(), getLHSExprs().end());
}

void ACCInReductionClause::setReductionOps(ArrayRef<Expr *> ReductionOps) {
  assert(ReductionOps.size() == varlist_size() && "Number of in reduction "
                                                  "expressions is not the same "
                                                  "as the preallocated buffer");
  std::copy(ReductionOps.begin(), ReductionOps.end(), getRHSExprs().end());
}

void ACCInReductionClause::setTaskgroupDescriptors(
    ArrayRef<Expr *> TaskgroupDescriptors) {
  assert(TaskgroupDescriptors.size() == varlist_size() &&
         "Number of in reduction descriptors is not the same as the "
         "preallocated buffer");
  std::copy(TaskgroupDescriptors.begin(), TaskgroupDescriptors.end(),
            getReductionOps().end());
}

ACCInReductionClause *ACCInReductionClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, SourceLocation ColonLoc, ArrayRef<Expr *> VL,
    NestedNameSpecifierLoc QualifierLoc, const DeclarationNameInfo &NameInfo,
    ArrayRef<Expr *> Privates, ArrayRef<Expr *> LHSExprs,
    ArrayRef<Expr *> RHSExprs, ArrayRef<Expr *> ReductionOps,
    ArrayRef<Expr *> TaskgroupDescriptors, Stmt *PreInit, Expr *PostUpdate) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(6 * VL.size()));
  ACCInReductionClause *Clause = new (Mem) ACCInReductionClause(
      StartLoc, LParenLoc, EndLoc, ColonLoc, VL.size(), QualifierLoc, NameInfo);
  Clause->setVarRefs(VL);
  Clause->setPrivates(Privates);
  Clause->setLHSExprs(LHSExprs);
  Clause->setRHSExprs(RHSExprs);
  Clause->setReductionOps(ReductionOps);
  Clause->setTaskgroupDescriptors(TaskgroupDescriptors);
  Clause->setPreInitStmt(PreInit);
  Clause->setPostUpdateExpr(PostUpdate);
  return Clause;
}

ACCInReductionClause *ACCInReductionClause::CreateEmpty(const ASTContext &C,
                                                        unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(6 * N));
  return new (Mem) ACCInReductionClause(N);
}

ACCFlushClause *ACCFlushClause::Create(const ASTContext &C,
                                       SourceLocation StartLoc,
                                       SourceLocation LParenLoc,
                                       SourceLocation EndLoc,
                                       ArrayRef<Expr *> VL) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(VL.size() + 1));
  ACCFlushClause *Clause =
      new (Mem) ACCFlushClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  return Clause;
}

ACCFlushClause *ACCFlushClause::CreateEmpty(const ASTContext &C, unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(N));
  return new (Mem) ACCFlushClause(N);
}

ACCDependClause *ACCDependClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, OpenACCDependClauseKind DepKind,
    SourceLocation DepLoc, SourceLocation ColonLoc, ArrayRef<Expr *> VL) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(VL.size() + 1));
  ACCDependClause *Clause =
      new (Mem) ACCDependClause(StartLoc, LParenLoc, EndLoc, VL.size());
  Clause->setVarRefs(VL);
  Clause->setDependencyKind(DepKind);
  Clause->setDependencyLoc(DepLoc);
  Clause->setColonLoc(ColonLoc);
  Clause->setCounterValue(nullptr);
  return Clause;
}

ACCDependClause *ACCDependClause::CreateEmpty(const ASTContext &C, unsigned N) {
  void *Mem = C.Allocate(totalSizeToAlloc<Expr *>(N + 1));
  return new (Mem) ACCDependClause(N);
}

void ACCDependClause::setCounterValue(Expr *V) {
  assert(getDependencyKind() == ACCC_DEPEND_sink ||
         getDependencyKind() == ACCC_DEPEND_source || V == nullptr);
  *getVarRefs().end() = V;
}

const Expr *ACCDependClause::getCounterValue() const {
  auto *V = *getVarRefs().end();
  assert(getDependencyKind() == ACCC_DEPEND_sink ||
         getDependencyKind() == ACCC_DEPEND_source || V == nullptr);
  return V;
}

Expr *ACCDependClause::getCounterValue() {
  auto *V = *getVarRefs().end();
  assert(getDependencyKind() == ACCC_DEPEND_sink ||
         getDependencyKind() == ACCC_DEPEND_source || V == nullptr);
  return V;
}

unsigned ACCClauseMappableExprCommon::getComponentsTotalNumber(
    MappableExprComponentListsRef ComponentLists) {
  unsigned TotalNum = 0u;
  for (auto &C : ComponentLists)
    TotalNum += C.size();
  return TotalNum;
}

unsigned ACCClauseMappableExprCommon::getUniqueDeclarationsTotalNumber(
    ArrayRef<ValueDecl *> Declarations) {
  unsigned TotalNum = 0u;
  llvm::SmallPtrSet<const ValueDecl *, 8> Cache;
  for (auto *D : Declarations) {
    const ValueDecl *VD = D ? cast<ValueDecl>(D->getCanonicalDecl()) : nullptr;
    if (Cache.count(VD))
      continue;
    ++TotalNum;
    Cache.insert(VD);
  }
  return TotalNum;
}

ACCMapClause *
ACCMapClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCMapClause *Clause = new (Mem) ACCMapClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCMapClause *ACCMapClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCMapClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}
/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Create
ACCCreateClause *
ACCCreateClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCCreateClause *Clause = new (Mem) ACCCreateClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCCreateClause *ACCCreateClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCCreateClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}

/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copy
ACCCopyClause *
ACCCopyClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCCopyClause *Clause = new (Mem) ACCCopyClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCCopyClause *ACCCopyClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCCopyClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}

/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copyin
ACCCopyinClause *
ACCCopyinClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCCopyinClause *Clause = new (Mem) ACCCopyinClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCCopyinClause *ACCCopyinClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCCopyinClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}

/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copyout
ACCCopyoutClause *
ACCCopyoutClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCCopyoutClause *Clause = new (Mem) ACCCopyoutClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCCopyoutClause *ACCCopyoutClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCCopyoutClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}
/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Delete
ACCDeleteClause *
ACCDeleteClause::Create(const ASTContext &C, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc,
                     ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists,
                     OpenACCMapClauseKind TypeModifier, OpenACCMapClauseKind Type,
                     bool TypeIsImplicit, SourceLocation TypeLoc) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  ACCDeleteClause *Clause = new (Mem) ACCDeleteClause(
      TypeModifier, Type, TypeIsImplicit, TypeLoc, StartLoc, LParenLoc, EndLoc,
      NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  Clause->setMapTypeModifier(TypeModifier);
  Clause->setMapType(Type);
  Clause->setMapLoc(TypeLoc);
  return Clause;
}

ACCDeleteClause *ACCDeleteClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                        unsigned NumUniqueDeclarations,
                                        unsigned NumComponentLists,
                                        unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCDeleteClause(NumVars, NumUniqueDeclarations,
                                NumComponentLists, NumComponents);
}

ACCToClause *ACCToClause::Create(const ASTContext &C, SourceLocation StartLoc,
                                 SourceLocation LParenLoc,
                                 SourceLocation EndLoc, ArrayRef<Expr *> Vars,
                                 ArrayRef<ValueDecl *> Declarations,
                                 MappableExprComponentListsRef ComponentLists) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));

  ACCToClause *Clause = new (Mem)
      ACCToClause(StartLoc, LParenLoc, EndLoc, NumVars, NumUniqueDeclarations,
                  NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  return Clause;
}

ACCToClause *ACCToClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                      unsigned NumUniqueDeclarations,
                                      unsigned NumComponentLists,
                                      unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCToClause(NumVars, NumUniqueDeclarations,
                               NumComponentLists, NumComponents);
}

ACCFromClause *
ACCFromClause::Create(const ASTContext &C, SourceLocation StartLoc,
                      SourceLocation LParenLoc, SourceLocation EndLoc,
                      ArrayRef<Expr *> Vars, ArrayRef<ValueDecl *> Declarations,
                      MappableExprComponentListsRef ComponentLists) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));

  ACCFromClause *Clause = new (Mem)
      ACCFromClause(StartLoc, LParenLoc, EndLoc, NumVars, NumUniqueDeclarations,
                    NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  return Clause;
}

ACCFromClause *ACCFromClause::CreateEmpty(const ASTContext &C, unsigned NumVars,
                                          unsigned NumUniqueDeclarations,
                                          unsigned NumComponentLists,
                                          unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCFromClause(NumVars, NumUniqueDeclarations,
                                 NumComponentLists, NumComponents);
}

void ACCUseDevicePtrClause::setPrivateCopies(ArrayRef<Expr *> VL) {
  assert(VL.size() == varlist_size() &&
         "Number of private copies is not the same as the preallocated buffer");
  std::copy(VL.begin(), VL.end(), varlist_end());
}

void ACCUseDevicePtrClause::setInits(ArrayRef<Expr *> VL) {
  assert(VL.size() == varlist_size() &&
         "Number of inits is not the same as the preallocated buffer");
  std::copy(VL.begin(), VL.end(), getPrivateCopies().end());
}

ACCUseDevicePtrClause *ACCUseDevicePtrClause::Create(
    const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
    SourceLocation EndLoc, ArrayRef<Expr *> Vars, ArrayRef<Expr *> PrivateVars,
    ArrayRef<Expr *> Inits, ArrayRef<ValueDecl *> Declarations,
    MappableExprComponentListsRef ComponentLists) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // 3 x NumVars x Expr* - we have an original list expression for each clause
  // list entry and an equal number of private copies and inits.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          3 * NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));

  ACCUseDevicePtrClause *Clause = new (Mem) ACCUseDevicePtrClause(
      StartLoc, LParenLoc, EndLoc, NumVars, NumUniqueDeclarations,
      NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setPrivateCopies(PrivateVars);
  Clause->setInits(Inits);
  Clause->setClauseInfo(Declarations, ComponentLists);
  return Clause;
}

ACCUseDevicePtrClause *ACCUseDevicePtrClause::CreateEmpty(
    const ASTContext &C, unsigned NumVars, unsigned NumUniqueDeclarations,
    unsigned NumComponentLists, unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          3 * NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCUseDevicePtrClause(NumVars, NumUniqueDeclarations,
                                         NumComponentLists, NumComponents);
}

ACCIsDevicePtrClause *
ACCIsDevicePtrClause::Create(const ASTContext &C, SourceLocation StartLoc,
                             SourceLocation LParenLoc, SourceLocation EndLoc,
                             ArrayRef<Expr *> Vars,
                             ArrayRef<ValueDecl *> Declarations,
                             MappableExprComponentListsRef ComponentLists) {
  unsigned NumVars = Vars.size();
  unsigned NumUniqueDeclarations =
      getUniqueDeclarationsTotalNumber(Declarations);
  unsigned NumComponentLists = ComponentLists.size();
  unsigned NumComponents = getComponentsTotalNumber(ComponentLists);

  // We need to allocate:
  // NumVars x Expr* - we have an original list expression for each clause list
  // entry.
  // NumUniqueDeclarations x ValueDecl* - unique base declarations associated
  // with each component list.
  // (NumUniqueDeclarations + NumComponentLists) x unsigned - we specify the
  // number of lists for each unique declaration and the size of each component
  // list.
  // NumComponents x MappableComponent - the total of all the components in all
  // the lists.
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));

  ACCIsDevicePtrClause *Clause = new (Mem) ACCIsDevicePtrClause(
      StartLoc, LParenLoc, EndLoc, NumVars, NumUniqueDeclarations,
      NumComponentLists, NumComponents);

  Clause->setVarRefs(Vars);
  Clause->setClauseInfo(Declarations, ComponentLists);
  return Clause;
}

ACCIsDevicePtrClause *ACCIsDevicePtrClause::CreateEmpty(
    const ASTContext &C, unsigned NumVars, unsigned NumUniqueDeclarations,
    unsigned NumComponentLists, unsigned NumComponents) {
  void *Mem = C.Allocate(
      totalSizeToAlloc<Expr *, ValueDecl *, unsigned,
                       ACCClauseMappableExprCommon::MappableComponent>(
          NumVars, NumUniqueDeclarations,
          NumUniqueDeclarations + NumComponentLists, NumComponents));
  return new (Mem) ACCIsDevicePtrClause(NumVars, NumUniqueDeclarations,
                                        NumComponentLists, NumComponents);
}
