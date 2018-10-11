//===--- OpenACCKinds.h - OpenACC enums ---------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief Defines some OpenACC-specific enums and functions.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_BASIC_OPENACCKINDS_H
#define LLVM_CLANG_BASIC_OPENACCKINDS_H

#include "llvm/ADT/StringRef.h"

namespace clang {

/// \brief OpenACC directives.
enum OpenACCDirectiveKind {
#define OPENACC_DIRECTIVE(Name) \
  ACCD_##Name,
#define OPENACC_DIRECTIVE_EXT(Name, Str) \
  ACCD_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCD_unknown
};

/// \brief OpenACC clauses.
enum OpenACCClauseKind {
#define OPENACC_CLAUSE(Name, Class) \
  ACCC_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_threadprivate,
  ACCC_uniform,
  ACCC_unknown
};

/// \brief OpenACC attributes for 'default' clause.
enum OpenACCDefaultClauseKind {
#define OPENACC_DEFAULT_KIND(Name) \
  ACCC_DEFAULT_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_DEFAULT_unknown
};

/// \brief OpenACC attributes for 'proc_bind' clause.
enum OpenACCProcBindClauseKind {
#define OPENACC_PROC_BIND_KIND(Name) \
  ACCC_PROC_BIND_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_PROC_BIND_unknown
};

/// \brief OpenACC attributes for 'schedule' clause.
enum OpenACCScheduleClauseKind {
#define OPENACC_SCHEDULE_KIND(Name) \
  ACCC_SCHEDULE_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_SCHEDULE_unknown
};

/// \brief OpenACC modifiers for 'schedule' clause.
enum OpenACCScheduleClauseModifier {
  ACCC_SCHEDULE_MODIFIER_unknown = ACCC_SCHEDULE_unknown,
#define OPENACC_SCHEDULE_MODIFIER(Name) \
  ACCC_SCHEDULE_MODIFIER_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_SCHEDULE_MODIFIER_last
};

/// \brief OpenACC attributes for 'depend' clause.
enum OpenACCDependClauseKind {
#define OPENACC_DEPEND_KIND(Name) \
  ACCC_DEPEND_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_DEPEND_unknown
};

/// \brief OpenACC attributes for 'linear' clause.
enum OpenACCLinearClauseKind {
#define OPENACC_LINEAR_KIND(Name) \
  ACCC_LINEAR_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_LINEAR_unknown
};

/// \brief OpenACC mapping kind for 'map' clause.
enum OpenACCMapClauseKind {
#define OPENACC_MAP_KIND(Name) \
  ACCC_MAP_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_MAP_unknown
};

/// \brief OpenACC attributes for 'dist_schedule' clause.
enum OpenACCDistScheduleClauseKind {
#define OPENACC_DIST_SCHEDULE_KIND(Name) ACCC_DIST_SCHEDULE_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_DIST_SCHEDULE_unknown
};

/// \brief OpenACC attributes for 'defaultmap' clause.
enum OpenACCDefaultmapClauseKind {
#define OPENACC_DEFAULTMAP_KIND(Name) \
  ACCC_DEFAULTMAP_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_DEFAULTMAP_unknown
};

/// \brief OpenACC modifiers for 'defaultmap' clause.
enum OpenACCDefaultmapClauseModifier {
  ACCC_DEFAULTMAP_MODIFIER_unknown = ACCC_DEFAULTMAP_unknown,
#define OPENACC_DEFAULTMAP_MODIFIER(Name) \
  ACCC_DEFAULTMAP_MODIFIER_##Name,
#include "clang/Basic/OpenACCKinds.def"
  ACCC_DEFAULTMAP_MODIFIER_last
};

/// Scheduling data for loop-based OpenACC directives.
struct OpenACCScheduleTy final {
  OpenACCScheduleClauseKind Schedule = ACCC_SCHEDULE_unknown;
  OpenACCScheduleClauseModifier M1 = ACCC_SCHEDULE_MODIFIER_unknown;
  OpenACCScheduleClauseModifier M2 = ACCC_SCHEDULE_MODIFIER_unknown;
};

OpenACCDirectiveKind getOpenACCDirectiveKind(llvm::StringRef Str);
const char *getOpenACCDirectiveName(OpenACCDirectiveKind Kind);

OpenACCClauseKind getOpenACCClauseKind(llvm::StringRef Str);
const char *getOpenACCClauseName(OpenACCClauseKind Kind);

unsigned getOpenACCSimpleClauseType(OpenACCClauseKind Kind, llvm::StringRef Str);
const char *getOpenACCSimpleClauseTypeName(OpenACCClauseKind Kind, unsigned Type);

bool isAllowedClauseForDirective(OpenACCDirectiveKind DKind,
                                 OpenACCClauseKind CKind);

/// \brief Checks if the specified directive is a directive with an associated
/// loop construct.
/// \param DKind Specified directive.
/// \return true - the directive is a loop-associated directive like 'acc simd'
/// or 'acc for' directive, otherwise - false.
bool isOpenACCLoopLikeDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a worksharing directive.
/// \param DKind Specified directive.
/// \return true - the directive is a worksharing directive like 'acc for',
/// otherwise - false.
bool isOpenACCWorksharingDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a taskloop directive.
/// \param DKind Specified directive.
/// \return true - the directive is a worksharing directive like 'acc taskloop',
/// otherwise - false.
bool isOpenACCTaskLoopDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a parallel-kind directive.
/// \param DKind Specified directive.
/// \return true - the directive is a parallel-like directive like 'acc
/// parallel', otherwise - false.
bool isOpenACCParallelDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a target code offload directive.
/// \param DKind Specified directive.
/// \return true - the directive is a target code offload directive like
/// 'acc target', 'acc target parallel', 'acc target xxx'
/// otherwise - false.
bool isOpenACCTargetExecutionDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a target data offload directive.
/// \param DKind Specified directive.
/// \return true - the directive is a target data offload directive like
/// 'acc target data', 'acc target update', 'acc target enter data',
/// 'acc target exit data'
/// otherwise - false.
bool isOpenACCDataManagementDirective(OpenACCDirectiveKind DKind);

/// Checks if the specified composite/combined directive constitutes a teams
/// directive in the outermost nest.  For example
/// 'acc teams distribute' or 'acc teams distribute parallel for'.
/// \param DKind Specified directive.
/// \return true - the directive has teams on the outermost nest, otherwise -
/// false.
bool isOpenACCNestingTeamsDirective(OpenACCDirectiveKind DKind);

/// Checks if the specified directive is a teams-kind directive.  For example,
/// 'acc teams distribute' or 'acc target teams'.
/// \param DKind Specified directive.
/// \return true - the directive is a teams-like directive, otherwise - false.
bool isOpenACCGangDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a simd directive.
/// \param DKind Specified directive.
/// \return true - the directive is a simd directive like 'acc simd',
/// otherwise - false.
bool isOpenACCVectorDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified directive is a distribute directive.
/// \param DKind Specified directive.
/// \return true - the directive is a distribute-directive like 'acc
/// distribute',
/// otherwise - false.
bool isOpenACCDistributeDirective(OpenACCDirectiveKind DKind);

/// Checks if the specified composite/combined directive constitutes a
/// distribute directive in the outermost nest.  For example,
/// 'acc distribute parallel for' or 'acc distribute'.
/// \param DKind Specified directive.
/// \return true - the directive has distribute on the outermost nest.
/// otherwise - false.
bool isOpenACCNestingDistributeDirective(OpenACCDirectiveKind DKind);

/// \brief Checks if the specified clause is one of private clauses like
/// 'private', 'firstprivate', 'reduction' etc..
/// \param Kind Clause kind.
/// \return true - the clause is a private clause, otherwise - false.
bool isOpenACCPrivate(OpenACCClauseKind Kind);

/// \brief Checks if the specified clause is one of threadprivate clauses like
/// 'threadprivate', 'copyin' or 'copyprivate'.
/// \param Kind Clause kind.
/// \return true - the clause is a threadprivate clause, otherwise - false.
bool isOpenACCThreadPrivate(OpenACCClauseKind Kind);

/// Checks if the specified directive kind is one of tasking directives - task,
/// taskloop or taksloop simd.
bool isOpenACCTaskingDirective(OpenACCDirectiveKind Kind);

/// Checks if the specified directive kind is one of the composite or combined
/// directives that need loop bound sharing across loops outlined in nested
/// functions
bool isOpenACCLoopBoundSharingDirective(OpenACCDirectiveKind Kind);

/// Return the captured regions of an OpenACC directive.
void getOpenACCCaptureRegions(
    llvm::SmallVectorImpl<OpenACCDirectiveKind> &CaptureRegions,
    OpenACCDirectiveKind DKind);
}

#endif

