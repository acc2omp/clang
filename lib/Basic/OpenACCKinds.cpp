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
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_shared:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_aligned:
  case ACCC_copyin:
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
  case ACCC_simd:
  case ACCC_num_teams:
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
    llvm_unreachable("Invalid OpenACC 'map' clause type");
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
  case ACCC_simdlen:
  case ACCC_collapse:
  case ACCC_private:
  case ACCC_firstprivate:
  case ACCC_lastprivate:
  case ACCC_shared:
  case ACCC_reduction:
  case ACCC_task_reduction:
  case ACCC_in_reduction:
  case ACCC_aligned:
  case ACCC_copyin:
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
  case ACCC_simd:
  case ACCC_num_teams:
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
  case ACCD_simd:
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
  case ACCD_for_simd:
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
  case ACCD_parallel_for_simd:
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
  case ACCD_target_data:
    switch (CKind) {
#define OPENACC_TARGET_DATA_CLAUSE(Name)                                        \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_enter_data:
    switch (CKind) {
#define OPENACC_TARGET_ENTER_DATA_CLAUSE(Name)                                  \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_exit_data:
    switch (CKind) {
#define OPENACC_TARGET_EXIT_DATA_CLAUSE(Name)                                   \
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
  case ACCD_target_parallel_for:
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
  case ACCD_teams:
    switch (CKind) {
#define OPENACC_TEAMS_CLAUSE(Name)                                              \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_declare_simd:
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
  case ACCD_taskloop_simd:
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
  case ACCD_distribute_parallel_for:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)                            \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute_parallel_for_simd:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_distribute_simd:
    switch (CKind) {
#define OPENACC_DISTRIBUTE_SIMD_CLAUSE(Name)                                    \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_parallel_for_simd:
    switch (CKind) {
#define OPENACC_TARGET_PARALLEL_LOOP_SIMD_CLAUSE(Name)                           \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_simd:
    switch (CKind) {
#define OPENACC_TARGET_SIMD_CLAUSE(Name)                                        \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_teams_distribute:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_CLAUSE(Name)                                   \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_teams_distribute_simd:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_SIMD_CLAUSE(Name)                              \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_teams_distribute_parallel_for_simd:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)                 \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_teams_distribute_parallel_for:
    switch (CKind) {
#define OPENACC_TEAMS_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)                      \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_teams:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_CLAUSE(Name)                                       \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_teams_distribute:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_DISTRIBUTE_CLAUSE(Name)                            \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_teams_distribute_parallel_for:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_DISTRIBUTE_PARALLEL_LOOP_CLAUSE(Name)               \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_teams_distribute_parallel_for_simd:
    switch (CKind) {
#define OPENACC_TARGET_TEAMS_DISTRIBUTE_PARALLEL_LOOP_SIMD_CLAUSE(Name)          \
  case ACCC_##Name:                                                            \
    return true;
#include "clang/Basic/OpenACCKinds.def"
    default:
      break;
    }
    break;
  case ACCD_target_teams_distribute_simd:
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
  return DKind == ACCD_simd || DKind == ACCD_loop || DKind == ACCD_for_simd ||
         DKind == ACCD_parallel_loop || DKind == ACCD_parallel_for_simd ||
         DKind == ACCD_taskloop || DKind == ACCD_taskloop_simd ||
         DKind == ACCD_distribute || DKind == ACCD_target_parallel_for ||
         DKind == ACCD_distribute_parallel_for ||
         DKind == ACCD_distribute_parallel_for_simd ||
         DKind == ACCD_distribute_simd ||
         DKind == ACCD_target_parallel_for_simd || DKind == ACCD_target_simd ||
         DKind == ACCD_teams_distribute ||
         DKind == ACCD_teams_distribute_simd ||
         DKind == ACCD_teams_distribute_parallel_for_simd ||
         DKind == ACCD_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute ||
         DKind == ACCD_target_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_simd;
}

bool clang::isOpenACCWorksharingDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_loop || DKind == ACCD_for_simd ||
         DKind == ACCD_sections || DKind == ACCD_section ||
         DKind == ACCD_single || DKind == ACCD_parallel_loop ||
         DKind == ACCD_parallel_for_simd || DKind == ACCD_parallel_sections ||
         DKind == ACCD_target_parallel_for ||
         DKind == ACCD_distribute_parallel_for ||
         DKind == ACCD_distribute_parallel_for_simd ||
         DKind == ACCD_target_parallel_for_simd ||
         DKind == ACCD_teams_distribute_parallel_for_simd ||
         DKind == ACCD_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd;
}

bool clang::isOpenACCTaskLoopDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_taskloop || DKind == ACCD_taskloop_simd;
}

bool clang::isOpenACCParallelDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_parallel || DKind == ACCD_parallel_loop ||
         DKind == ACCD_parallel_for_simd || DKind == ACCD_parallel_sections ||
         DKind == ACCD_target_parallel || DKind == ACCD_target_parallel_for ||
         DKind == ACCD_distribute_parallel_for ||
         DKind == ACCD_distribute_parallel_for_simd ||
         DKind == ACCD_target_parallel_for_simd ||
         DKind == ACCD_teams_distribute_parallel_for ||
         DKind == ACCD_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd;
}

bool clang::isOpenACCTargetExecutionDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_target || DKind == ACCD_target_parallel ||
         DKind == ACCD_target_parallel_for ||
         DKind == ACCD_target_parallel_for_simd || DKind == ACCD_target_simd ||
         DKind == ACCD_target_teams || DKind == ACCD_target_teams_distribute ||
         DKind == ACCD_target_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_simd;
}

bool clang::isOpenACCTargetDataManagementDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_target_data || DKind == ACCD_target_enter_data ||
         DKind == ACCD_target_exit_data || DKind == ACCD_target_update;
}

bool clang::isOpenACCNestingTeamsDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_teams || DKind == ACCD_teams_distribute ||
         DKind == ACCD_teams_distribute_simd ||
         DKind == ACCD_teams_distribute_parallel_for_simd ||
         DKind == ACCD_teams_distribute_parallel_for;
}

bool clang::isOpenACCTeamsDirective(OpenACCDirectiveKind DKind) {
  return isOpenACCNestingTeamsDirective(DKind) ||
         DKind == ACCD_target_teams || DKind == ACCD_target_teams_distribute ||
         DKind == ACCD_target_teams_distribute_parallel_for ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_simd;
}

bool clang::isOpenACCSimdDirective(OpenACCDirectiveKind DKind) {
  return DKind == ACCD_simd || DKind == ACCD_for_simd ||
         DKind == ACCD_parallel_for_simd || DKind == ACCD_taskloop_simd ||
         DKind == ACCD_distribute_parallel_for_simd ||
         DKind == ACCD_distribute_simd || DKind == ACCD_target_simd ||
         DKind == ACCD_teams_distribute_simd ||
         DKind == ACCD_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_parallel_for_simd ||
         DKind == ACCD_target_teams_distribute_simd ||
         DKind == ACCD_target_parallel_for_simd;
}

bool clang::isOpenACCNestingDistributeDirective(OpenACCDirectiveKind Kind) {
  return Kind == ACCD_distribute || Kind == ACCD_distribute_parallel_for ||
         Kind == ACCD_distribute_parallel_for_simd ||
         Kind == ACCD_distribute_simd;
  // TODO add next directives.
}

bool clang::isOpenACCDistributeDirective(OpenACCDirectiveKind Kind) {
  return isOpenACCNestingDistributeDirective(Kind) ||
         Kind == ACCD_teams_distribute || Kind == ACCD_teams_distribute_simd ||
         Kind == ACCD_teams_distribute_parallel_for_simd ||
         Kind == ACCD_teams_distribute_parallel_for ||
         Kind == ACCD_target_teams_distribute ||
         Kind == ACCD_target_teams_distribute_parallel_for ||
         Kind == ACCD_target_teams_distribute_parallel_for_simd ||
         Kind == ACCD_target_teams_distribute_simd;
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
  return Kind == ACCD_distribute_parallel_for ||
         Kind == ACCD_distribute_parallel_for_simd ||
         Kind == ACCD_teams_distribute_parallel_for_simd ||
         Kind == ACCD_teams_distribute_parallel_for ||
         Kind == ACCD_target_teams_distribute_parallel_for ||
         Kind == ACCD_target_teams_distribute_parallel_for_simd;
}

void clang::getOpenACCCaptureRegions(
    SmallVectorImpl<OpenACCDirectiveKind> &CaptureRegions,
    OpenACCDirectiveKind DKind) {
  assert(DKind <= ACCD_unknown);
  switch (DKind) {
  case ACCD_parallel:
  // LUIS
  case ACCD_parallel_loop:
  case ACCD_parallel_for_simd:
  case ACCD_parallel_sections:
  case ACCD_distribute_parallel_for:
  case ACCD_distribute_parallel_for_simd:
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_target_teams:
  case ACCD_target_teams_distribute:
  case ACCD_target_teams_distribute_simd:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_teams);
    break;
  case ACCD_teams:
  case ACCD_teams_distribute:
  case ACCD_teams_distribute_simd:
    CaptureRegions.push_back(ACCD_teams);
    break;
  case ACCD_target:
  case ACCD_target_simd:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    break;
  case ACCD_teams_distribute_parallel_for:
  case ACCD_teams_distribute_parallel_for_simd:
    CaptureRegions.push_back(ACCD_teams);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_target_parallel:
  case ACCD_target_parallel_for:
  case ACCD_target_parallel_for_simd:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_task:
  case ACCD_target_enter_data:
  case ACCD_target_exit_data:
  case ACCD_target_update:
    CaptureRegions.push_back(ACCD_task);
    break;
  case ACCD_taskloop:
  case ACCD_taskloop_simd:
    CaptureRegions.push_back(ACCD_taskloop);
    break;
  case ACCD_target_teams_distribute_parallel_for:
  case ACCD_target_teams_distribute_parallel_for_simd:
    CaptureRegions.push_back(ACCD_task);
    CaptureRegions.push_back(ACCD_target);
    CaptureRegions.push_back(ACCD_teams);
    CaptureRegions.push_back(ACCD_parallel);
    break;
  case ACCD_simd:
  case ACCD_loop:
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
  case ACCD_target_data:
  case ACCD_distribute_simd:
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
  case ACCD_declare_simd:
  case ACCD_declare_target:
  case ACCD_end_declare_target:
    llvm_unreachable("OpenACC Directive is not allowed");
  case ACCD_unknown:
    llvm_unreachable("Unknown OpenACC directive");
  }
}
