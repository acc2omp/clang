//===--- OpenACCKinds.cpp - Token Kinds Support ----------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file implements the OpenACC enum and support functions.
///
//===----------------------------------------------------------------------===//
#include "clang/AST/ASTContext.h"

#include "clang/Basic/OpenACCKinds.h"
#include "clang/Basic/IdentifierTable.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/ErrorHandling.h"
#include <cassert>

using namespace clang;

OpenACCDirectiveKind clang::getOpenACCDirectiveKind(StringRef Str) {
  return llvm::StringSwitch<OpenACCDirectiveKind>(Str)
#define OPENACC_DIRECTIVE(Name) .Case(#Name, ACCD_##Name)
#define OPENACC_DIRECTIVE_EXT(Name, Str) .Case(Str, ACCD_##Name)
#include "clang/Basic/OpenACCKinds.def"
      .Default(ACCD_unknown);
}

const char *clang::getOpenACCDirectiveName(OpenACCDirectiveKind Kind) {
  assert(Kind <= ACCD_unknown);
  switch (Kind) {
  case ACCD_unknown:
    return "unknown";
#define OPENACC_DIRECTIVE(Name)                                                 \
  case ACCD_##Name:                                                            \
    return #Name;
#define OPENACC_DIRECTIVE_EXT(Name, Str)                                        \
  case ACCD_##Name:                                                            \
    return Str;
#include "clang/Basic/OpenACCKinds.def"
    break;
  }
  llvm_unreachable("Invalid OpenACC directive kind");
}

OpenACCClauseKind clang::getOpenACCClauseKind(StringRef Str) {
  // 'flush' clause cannot be specified explicitly, because this is an implicit
  // clause for 'flush' directive. If the 'flush' clause is explicitly specified
  // the Parser should generate a warning about extra tokens at the end of the
  // directive.
  if (Str == "flush")
    return ACCC_unknown;
  return llvm::StringSwitch<OpenACCClauseKind>(Str)
#define OPENACC_CLAUSE(Name, Class) .Case(#Name, ACCC_##Name)
#include "clang/Basic/OpenACCKinds.def"
      .Case("uniform", ACCC_uniform)

      .Default(ACCC_unknown);
}

const char *clang::getOpenACCClauseName(OpenACCClauseKind Kind) {
  assert(Kind <= ACCC_unknown);
  switch (Kind) {
  case ACCC_unknown:
    return "unknown";
#define OPENACC_CLAUSE(Name, Class)                                             \
  case ACCC_##Name:                                                            \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
  case ACCC_uniform:
    return "uniform";
  case ACCC_threadprivate:
    return "threadprivate or thread local";
  }
  llvm_unreachable("Invalid OpenACC clause kind");
}

unsigned clang::getOpenACCSimpleClauseType(OpenACCClauseKind Kind,
                                          StringRef Str) {

    llvm::outs() << " ######### getOpenACCSimpleClauseType = " << getOpenACCClauseName(Kind) << " ##########\n";

  switch (Kind) {
  case ACCC_default:
    return llvm::StringSwitch<OpenACCDefaultClauseKind>(Str)
#define OPENACC_DEFAULT_KIND(Name) .Case(#Name, ACCC_DEFAULT_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_DEFAULT_unknown);
  case ACCC_proc_bind:
    return llvm::StringSwitch<OpenACCProcBindClauseKind>(Str)
#define OPENACC_PROC_BIND_KIND(Name) .Case(#Name, ACCC_PROC_BIND_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_PROC_BIND_unknown);
  case ACCC_schedule:
    return llvm::StringSwitch<unsigned>(Str)
#define OPENACC_SCHEDULE_KIND(Name)                                             \
  .Case(#Name, static_cast<unsigned>(ACCC_SCHEDULE_##Name))
#define OPENACC_SCHEDULE_MODIFIER(Name)                                         \
  .Case(#Name, static_cast<unsigned>(ACCC_SCHEDULE_MODIFIER_##Name))
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_SCHEDULE_unknown);
  case ACCC_depend:
    return llvm::StringSwitch<OpenACCDependClauseKind>(Str)
#define OPENACC_DEPEND_KIND(Name) .Case(#Name, ACCC_DEPEND_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_DEPEND_unknown);
  case ACCC_linear:
    return llvm::StringSwitch<OpenACCLinearClauseKind>(Str)
#define OPENACC_LINEAR_KIND(Name) .Case(#Name, ACCC_LINEAR_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_LINEAR_unknown);
  case ACCC_map:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
    //
    //TODO acc2mp Substitute Map clause for actual create, copy, copyin, copyout, delete
  case ACCC_create:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
  case ACCC_copy:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
  case ACCC_copyin:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
  case ACCC_copyout:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
  case ACCC_delete:
    return llvm::StringSwitch<OpenACCMapClauseKind>(Str)
#define OPENACC_MAP_KIND(Name) .Case(#Name, ACCC_MAP_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_MAP_unknown);
  /* case ACCC_create: */
  /*   return ACCC_MAP_alloc; */
  /* case ACCC_copy: */
  /*   return ACCC_MAP_tofrom; */
  /* case ACCC_copyin: */
  /*   return ACCC_MAP_to; */
  /* case ACCC_copyout: */
  /*   return ACCC_MAP_from; */
  /* case ACCC_delete: */
  /*   return ACCC_MAP_delete; */

  case ACCC_dist_schedule:
    return llvm::StringSwitch<OpenACCDistScheduleClauseKind>(Str)
#define OPENACC_DIST_SCHEDULE_KIND(Name) .Case(#Name, ACCC_DIST_SCHEDULE_##Name)
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_DIST_SCHEDULE_unknown);
  case ACCC_defaultmap:
    return llvm::StringSwitch<unsigned>(Str)
#define OPENACC_DEFAULTMAP_KIND(Name)                                           \
  .Case(#Name, static_cast<unsigned>(ACCC_DEFAULTMAP_##Name))
#define OPENACC_DEFAULTMAP_MODIFIER(Name)                                       \
  .Case(#Name, static_cast<unsigned>(ACCC_DEFAULTMAP_MODIFIER_##Name))
#include "clang/Basic/OpenACCKinds.def"
        .Default(ACCC_DEFAULTMAP_unknown);
  case ACCC_unknown:
  case ACCC_threadprivate:
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_vectorlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_shared:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_aligned:
  case ACCC_copyprivate:
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_vector:
  case ACCC_num_gangs:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    break;
  }
  llvm_unreachable("Invalid OpenACC simple clause kind");
}

const char *clang::getOpenACCSimpleClauseTypeName(OpenACCClauseKind Kind,
                                                 unsigned Type) {
  switch (Kind) {
  case ACCC_default:
    switch (Type) {
    case ACCC_DEFAULT_unknown:
      return "unknown";
#define OPENACC_DEFAULT_KIND(Name)                                              \
  case ACCC_DEFAULT_##Name:                                                    \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'default' clause type");
  case ACCC_proc_bind:
    switch (Type) {
    case ACCC_PROC_BIND_unknown:
      return "unknown";
#define OPENACC_PROC_BIND_KIND(Name)                                            \
  case ACCC_PROC_BIND_##Name:                                                  \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'proc_bind' clause type");
  case ACCC_schedule:
    switch (Type) {
    case ACCC_SCHEDULE_unknown:
    case ACCC_SCHEDULE_MODIFIER_last:
      return "unknown";
#define OPENACC_SCHEDULE_KIND(Name)                                             \
    case ACCC_SCHEDULE_##Name:                                                 \
      return #Name;
#define OPENACC_SCHEDULE_MODIFIER(Name)                                         \
    case ACCC_SCHEDULE_MODIFIER_##Name:                                        \
      return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'schedule' clause type");
  case ACCC_depend:
    switch (Type) {
    case ACCC_DEPEND_unknown:
      return "unknown";
#define OPENACC_DEPEND_KIND(Name)                                             \
  case ACCC_DEPEND_##Name:                                                   \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'depend' clause type");
  case ACCC_linear:
    switch (Type) {
    case ACCC_LINEAR_unknown:
      return "unknown";
#define OPENACC_LINEAR_KIND(Name)                                             \
  case ACCC_LINEAR_##Name:                                                   \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'linear' clause type");
  case ACCC_map:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
  case ACCC_create:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    llvm_unreachable("Invalid OpenACC 'create' clause type");
  case ACCC_copy:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    llvm_unreachable("Invalid OpenACC 'copy' clause type");
  case ACCC_copyin:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    llvm_unreachable("Invalid OpenACC 'copyin' clause type");
  case ACCC_copyout:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    llvm_unreachable("Invalid OpenACC 'copyout' clause type");
  case ACCC_delete:
    switch (Type) {
    case ACCC_MAP_unknown:
      return "unknown";
#define OPENACC_MAP_KIND(Name)                                                \
  case ACCC_MAP_##Name:                                                      \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    llvm_unreachable("Invalid OpenACC 'delete' clause type");
  case ACCC_dist_schedule:
    switch (Type) {
    case ACCC_DIST_SCHEDULE_unknown:
      return "unknown";
#define OPENACC_DIST_SCHEDULE_KIND(Name)                                      \
  case ACCC_DIST_SCHEDULE_##Name:                                            \
    return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'dist_schedule' clause type");
  case ACCC_defaultmap:
    switch (Type) {
    case ACCC_DEFAULTMAP_unknown:
    case ACCC_DEFAULTMAP_MODIFIER_last:
      return "unknown";
#define OPENACC_DEFAULTMAP_KIND(Name)                                         \
    case ACCC_DEFAULTMAP_##Name:                                             \
      return #Name;
#define OPENACC_DEFAULTMAP_MODIFIER(Name)                                     \
    case ACCC_DEFAULTMAP_MODIFIER_##Name:                                    \
      return #Name;
#include "clang/Basic/OpenACCKinds.def"
    }
    llvm_unreachable("Invalid OpenACC 'schedule' clause type");
  case ACCC_unknown:
  case ACCC_threadprivate:
  case ACCC_if:
  case ACCC_final:
  case ACCC_num_threads:
  case ACCC_safelen:
  case ACCC_vectorlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_shared:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_aligned:
  case ACCC_copyprivate:
  case ACCC_ordered:
  case ACCC_nowait:
  case ACCC_untied:
  case ACCC_mergeable:
  case ACCC_flush:
  case ACCC_read:
  case ACCC_write:
  case ACCC_update:
  case ACCC_capture:
  case ACCC_seq_cst:
  case ACCC_device:
  case ACCC_threads:
  case ACCC_vector:
  case ACCC_num_gangs:
  case ACCC_thread_limit:
  case ACCC_priority:
  case ACCC_grainsize:
  case ACCC_nogroup:
  case ACCC_num_tasks:
  case ACCC_hint:
  case ACCC_uniform:
  case ACCC_to:
  case ACCC_from:
  case ACCC_use_device_ptr:
  case ACCC_is_device_ptr:
    break;
  }
  llvm_unreachable("Invalid OpenACC simple clause kind");
}

bool clang::isAllowedClauseForDirective(OpenACCDirectiveKind DKind,
                                        OpenACCClauseKind CKind) {
  assert(DKind <= ACCD_unknown);
  assert(CKind <= ACCC_unknown);
  switch (DKind) {
  case ACCD_parallel:
    switch (CKind) {
#define OPENACC_PARALLEL_CLAUSE(Name)                                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_vector:
    switch (CKind) {
#define OPENACC_SIMD_CLAUSE(Name)                                               \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_loop:
    switch (CKind) {
#define OPENACC_LOOP_CLAUSE(Name)                                                \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_loop_vector:
    switch (CKind) {
#define OPENACC_LOOP_SIMD_CLAUSE(Name)                                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_sections:
    switch (CKind) {
#define OPENACC_SECTIONS_CLAUSE(Name)                                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_single:
    switch (CKind) {
#define OPENACC_SINGLE_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  // LUIS
  case ACCD_parallel_loop:
    switch (CKind) {
#define OPENACC_PARALLEL_LOOP_CLAUSE(Name)                                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_parallel_loop_vector:
    switch (CKind) {
#define OPENACC_PARALLEL_LOOP_SIMD_CLAUSE(Name)                                  \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_parallel_sections:
    switch (CKind) {
#define OPENACC_PARALLEL_SECTIONS_CLAUSE(Name)                                  \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_task:
    switch (CKind) {
#define OPENACC_TASK_CLAUSE(Name)                                               \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_flush:
    return CKind == ACCC_flush;
    break;
  case ACCD_atomic:
    switch (CKind) {
#define OPENACC_ATOMIC_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_data:
    switch (CKind) {
#define OPENACC_DATA_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_enter_data:
    switch (CKind) {
#define OPENACC_ENTER_DATA_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_exit_data:
    switch (CKind) {
#define OPENACC_EXIT_DATA_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target:
    switch (CKind) {
#define OPENACC_TARGET_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_parallel:
    switch (CKind) {
#define OPENACC_TARGET_PARALLEL_CLAUSE(Name)                                    \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_parallel_loop:
    switch (CKind) {
#define OPENACC_TARGET_PARALLEL_LOOP_CLAUSE(Name)                                \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_update:
    switch (CKind) {
#define OPENACC_TARGET_UPDATE_CLAUSE(Name)                                      \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_gang:
    switch (CKind) {
#define OPENACC_GANG_CLAUSE(Name)                                              \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_declare_vector:
    break;
  case ACCD_cancel:
    switch (CKind) {
#define OPENACC_CANCEL_CLAUSE(Name)                                             \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_ordered:
    switch (CKind) {
#define OPENACC_ORDERED_CLAUSE(Name)                                            \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_taskloop:
    switch (CKind) {
#define OPENACC_TASKLOOP_CLAUSE(Name)                                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_taskloop_vector:
    switch (CKind) {
#define OPENACC_TASKLOOP_SIMD_CLAUSE(Name)                                      \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_critical:
    switch (CKind) {
#define OPENACC_CRITICAL_CLAUSE(Name)                                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_CLAUSE(Name)                                         \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute_parallel_loop:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)                            \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute_parallel_loop_vector:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute_vector:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_SIMD_CLAUSE(Name)                                    \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_parallel_loop_vector:
    switch (CKind) {
#define OPENACC_TARGET_PARALLEL_LOOP_SIMD_CLAUSE(Name)                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_vector:
    switch (CKind) {
#define OPENACC_TARGET_SIMD_CLAUSE(Name)                                        \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_gang_distribute:
    switch (CKind) {
#define OPENACC_GANG_DISTRIBUTE_CLAUSE(Name)                                   \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_gang_distribute_vector:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_SIMD_CLAUSE(Name)                              \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_gang_distribute_parallel_loop_vector:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)                 \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_gang_distribute_parallel_loop:
    switch (CKind) {
#define OPENACC_GANG_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)                      \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_gang:
    switch (CKind) {
#define OPENACC_TARGET_GANG_CLAUSE(Name)                                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_gang_distribute:
    switch (CKind) {
#define OPENACC_TARGET_GANG_DISTRIBUTE_CLAUSE(Name)                            \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_gang_distribute_parallel_loop:
    switch (CKind) {
#define OPENACC_TARGET_GANG_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)               \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_gang_distribute_parallel_loop_vector:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)          \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_gang_distribute_vector:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_DISTRIBUTE_SIMD_CLAUSE(Name)                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_taskgroup:
    switch (CKind) {
#define OPENACC_TASKGROUP_CLAUSE(Name)                                          \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_declare_target:
  case ACCD_end_declare_target:
  case ACCD_unknown:
  case ACCD_threadprivate:
  case ACCD_section:
  case ACCD_master:
  case ACCD_taskyield:
  case ACCD_barrier:
  case ACCD_taskwait:
  case ACCD_cancellation_point:
  case ACCD_declare_reduction:
    break;
  }
  return false;
}

bool clang::isOpenACCLoopLikeDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_vector || DKind == ACCD_loop || DKind == ACCD_loop_vector ||
         DKind == ACCD_parallel_loop || DKind == ACCD_parallel_loop_vector ||
         DKind == ACCD_taskloop || DKind == ACCD_taskloop_vector ||
         DKind == ACCD_distribute || DKind == ACCD_target_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop_vector ||
         DKind == ACCD_distribute_vector ||
         DKind == ACCD_target_parallel_loop_vector || DKind == ACCD_target_vector ||
         DKind == ACCD_gang_distribute ||
         DKind == ACCD_gang_distribute_vector ||
         DKind == ACCD_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute ||
         DKind == ACCD_target_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_vector;
}

bool clang::isOpenACCWorksharingDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_loop || DKind == ACCD_loop_vector ||
         DKind == ACCD_sections || DKind == ACCD_section ||
         DKind == ACCD_single || DKind == ACCD_parallel_loop ||
         DKind == ACCD_parallel_loop_vector || DKind == ACCD_parallel_sections ||
         DKind == ACCD_target_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop_vector ||
         DKind == ACCD_target_parallel_loop_vector ||
         DKind == ACCD_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector;
}

bool clang::isOpenACCTaskLoopDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_taskloop || DKind == ACCD_taskloop_vector;
}

bool clang::isOpenACCParallelDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_parallel || DKind == ACCD_parallel_loop ||
         DKind == ACCD_parallel_loop_vector || DKind == ACCD_parallel_sections ||
         DKind == ACCD_target_parallel || DKind == ACCD_target_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop ||
         DKind == ACCD_distribute_parallel_loop_vector ||
         DKind == ACCD_target_parallel_loop_vector ||
         DKind == ACCD_gang_distribute_parallel_loop ||
         DKind == ACCD_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector;
}

bool clang::isOpenACCTargetExecutionDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_target || DKind == ACCD_target_parallel ||
         DKind == ACCD_target_parallel_loop ||
         DKind == ACCD_target_parallel_loop_vector || DKind == ACCD_target_vector ||
         DKind == ACCD_target_gang || DKind == ACCD_target_gang_distribute ||
         DKind == ACCD_target_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_vector;
}

bool clang::isOpenACCDataManagementDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_data || DKind == ACCD_enter_data ||
         DKind == ACCD_exit_data || DKind == ACCD_target_update;
}

bool clang::isOpenACCNestingTeamsDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_gang || DKind == ACCD_gang_distribute ||
         DKind == ACCD_gang_distribute_vector ||
         DKind == ACCD_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_gang_distribute_parallel_loop;
}

bool clang::isOpenACCGangDirective(OpenACCDirectiveKind DKind) {
  return isOpenACCNestingTeamsDirective(DKind) ||
         DKind == ACCD_target_gang || DKind == ACCD_target_gang_distribute ||
         DKind == ACCD_target_gang_distribute_parallel_loop ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_vector;
}

bool clang::isOpenACCVectorDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_vector || DKind == ACCD_loop_vector ||
         DKind == ACCD_parallel_loop_vector || DKind == ACCD_taskloop_vector ||
         DKind == ACCD_distribute_parallel_loop_vector ||
         DKind == ACCD_distribute_vector || DKind == ACCD_target_vector ||
         DKind == ACCD_gang_distribute_vector ||
         DKind == ACCD_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_parallel_loop_vector ||
         DKind == ACCD_target_gang_distribute_vector ||
         DKind == ACCD_target_parallel_loop_vector;
}

bool clang::isOpenACCNestingDistributeDirective(OpenACCDirectiveKind Kind) {
  return Kind == ACCD_distribute || Kind == ACCD_distribute_parallel_loop ||
         Kind == ACCD_distribute_parallel_loop_vector ||
         Kind == ACCD_distribute_vector;
  // TODO add next directives.
}

bool clang::isOpenACCDistributeDirective(OpenACCDirectiveKind Kind) {
  return isOpenACCNestingDistributeDirective(Kind) ||
         Kind == ACCD_gang_distribute || Kind == ACCD_gang_distribute_vector ||
         Kind == ACCD_gang_distribute_parallel_loop_vector ||
         Kind == ACCD_gang_distribute_parallel_loop ||
         Kind == ACCD_target_gang_distribute ||
         Kind == ACCD_target_gang_distribute_parallel_loop ||
         Kind == ACCD_target_gang_distribute_parallel_loop_vector ||
         Kind == ACCD_target_gang_distribute_vector;
}

bool clang::isOpenACCPrivate(OpenACCClauseKind Kind) {
  return Kind == ACCC_private || Kind == ACCC_firstprivate ||
         Kind == ACCC_lastprivate || Kind == ACCC_linear ||
         Kind == ACCC_reduction || Kind == ACCC_task_reduction ||
         Kind == ACCC_in_reduction; // TODO add next clauses like 'reduction'.
}

bool clang::isOpenACCThreadPrivate(OpenACCClauseKind Kind) {
  return Kind == ACCC_threadprivate || Kind == ACCC_copyin;
}

bool clang::isOpenACCTaskingDirective(OpenACCDirectiveKind Kind) {
  return Kind == ACCD_task || isOpenACCTaskLoopDirective(Kind);
}

bool clang::isOpenACCLoopBoundSharingDirective(OpenACCDirectiveKind Kind) {
  return Kind == ACCD_distribute_parallel_loop ||
         Kind == ACCD_distribute_parallel_loop_vector ||
         Kind == ACCD_gang_distribute_parallel_loop_vector ||
         Kind == ACCD_gang_distribute_parallel_loop ||
         Kind == ACCD_target_gang_distribute_parallel_loop ||
         Kind == ACCD_target_gang_distribute_parallel_loop_vector;
}

void clang::getOpenACCCaptureRegions(
    SmallVectorImpl<OpenACCDirectiveKind> &CaptureRegions,
    OpenACCDirectiveKind DKind) {
  assert(DKind <= ACCD_unknown);
  switch (DKind) {
  case ACCD_parallel:
  // LUIS
  case ACCD_parallel_loop:
  case ACCD_parallel_loop_vector:
  case ACCD_parallel_sections:
  case ACCD_distribute_parallel_loop:
  case ACCD_distribute_parallel_loop_vector:
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_target_gang:
  case ACCD_target_gang_distribute:
  case ACCD_target_gang_distribute_vector:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_gang);
    break;
  case ACCD_gang:
  case ACCD_gang_distribute:
  case ACCD_gang_distribute_vector:
    CaptureRegions.push_back(ACCD_gang);
    break;
  case ACCD_target:
  case ACCD_target_vector:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    break;
  case ACCD_gang_distribute_parallel_loop:
  case ACCD_gang_distribute_parallel_loop_vector:
    CaptureRegions.push_back(ACCD_gang);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_target_parallel:
  case ACCD_target_parallel_loop:
  case ACCD_target_parallel_loop_vector:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_task:
  case ACCD_enter_data:
  case ACCD_exit_data:
  case ACCD_target_update:
    CaptureRegions.push_back(ACCD_task);
    break;
  case ACCD_taskloop:
  case ACCD_taskloop_vector:
    CaptureRegions.push_back(ACCD_taskloop);
    break;
  case ACCD_target_gang_distribute_parallel_loop:
  case ACCD_target_gang_distribute_parallel_loop_vector:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_gang);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_vector:
  case ACCD_loop:
  case ACCD_loop_vector:
  case ACCD_sections:
  case ACCD_section:
  case ACCD_single:
  case ACCD_master:
  case ACCD_critical:
  case ACCD_taskgroup:
  case ACCD_distribute:
  case ACCD_ordered:
  case ACCD_atomic:
  case ACCD_data:
  case ACCD_distribute_vector:
    CaptureRegions.push_back(ACCD_unknown);
    break;
  case ACCD_threadprivate:
  case ACCD_taskyield:
  case ACCD_barrier:
  case ACCD_taskwait:
  case ACCD_cancellation_point:
  case ACCD_cancel:
  case ACCD_flush:
  case ACCD_declare_reduction:
  case ACCD_declare_vector:
  case ACCD_declare_target:
  case ACCD_end_declare_target:
    llvm_unreachable("OpenACC Directive is not allowed");
  case ACCD_unknown:
    llvm_unreachable("Unknown OpenACC directive");
  }
}
