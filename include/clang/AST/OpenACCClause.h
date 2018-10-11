//===- OpenACCClause.h - Classes for OpenACC clauses --------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file
/// \brief This file defines OpenACC AST classes for clauses.
/// There are clauses for executable directives, clauses for declarative
/// directives and clauses which can be used in both kinds of directives.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_OPENACCCLAUSE_H
#define LLVM_CLANG_AST_OPENACCCLAUSE_H

#include "clang/AST/Decl.h"
#include "clang/AST/DeclarationName.h"
#include "clang/AST/Expr.h"
#include "clang/AST/NestedNameSpecifier.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtIterator.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/OpenACCKinds.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/iterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/TrailingObjects.h"
#include <cassert>
#include <cstddef>
#include <iterator>
#include <utility>

namespace clang {

class ASTContext;

//===----------------------------------------------------------------------===//
// AST classes for clauses.
//===----------------------------------------------------------------------===//

/// \brief This is a basic class for representing single OpenACC clause.
class ACCClause {
  /// \brief Starting location of the clause (the clause keyword).
  SourceLocation StartLoc;

  /// \brief Ending location of the clause.
  SourceLocation EndLoc;

  /// \brief Kind of the clause.
  OpenACCClauseKind Kind;

protected:
  ACCClause(OpenACCClauseKind K, SourceLocation StartLoc, SourceLocation EndLoc)
      : StartLoc(StartLoc), EndLoc(EndLoc), Kind(K) {}

public:
  /// \brief Returns the starting location of the clause.
  SourceLocation getLocStart() const { return StartLoc; }

  /// \brief Returns the ending location of the clause.
  SourceLocation getLocEnd() const { return EndLoc; }

  /// \brief Sets the starting location of the clause.
  void setLocStart(SourceLocation Loc) { StartLoc = Loc; }

  /// \brief Sets the ending location of the clause.
  void setLocEnd(SourceLocation Loc) { EndLoc = Loc; }

  /// \brief Returns kind of OpenACC clause (private, shared, reduction, etc.).
  OpenACCClauseKind getClauseKind() const { return Kind; }

  bool isImplicit() const { return StartLoc.isInvalid(); }

  using child_iterator = StmtIterator;
  using const_child_iterator = ConstStmtIterator;
  using child_range = llvm::iterator_range<child_iterator>;
  using const_child_range = llvm::iterator_range<const_child_iterator>;

  child_range children();
  const_child_range children() const {
    auto Children = const_cast<ACCClause *>(this)->children();
    return const_child_range(Children.begin(), Children.end());
  }

  static bool classof(const ACCClause *) { return true; }
};

/// Class that handles pre-initialization statement for some clauses, like
/// 'shedule', 'firstprivate' etc.
class ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// Pre-initialization statement for the clause.
  Stmt *PreInit = nullptr;

  /// Region that captures the associated stmt.
  OpenACCDirectiveKind CaptureRegion = ACCD_unknown;

protected:
  ACCClauseWithPreInit(const ACCClause *This) {
    assert(get(This) && "get is not tuned for pre-init.");
  }

  /// Set pre-initialization statement for the clause.
  void setPreInitStmt(Stmt *S, OpenACCDirectiveKind ThisRegion = ACCD_unknown) {
    PreInit = S;
    CaptureRegion = ThisRegion;
  }

public:
  /// Get pre-initialization statement for the clause.
  const Stmt *getPreInitStmt() const { return PreInit; }

  /// Get pre-initialization statement for the clause.
  Stmt *getPreInitStmt() { return PreInit; }

  /// Get capture region for the stmt in the clause.
  OpenACCDirectiveKind getCaptureRegion() { return CaptureRegion; }

  static ACCClauseWithPreInit *get(ACCClause *C);
  static const ACCClauseWithPreInit *get(const ACCClause *C);
};

/// Class that handles post-update expression for some clauses, like
/// 'lastprivate', 'reduction' etc.
class ACCClauseWithPostUpdate : public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// Post-update expression for the clause.
  Expr *PostUpdate = nullptr;

protected:
  ACCClauseWithPostUpdate(const ACCClause *This) : ACCClauseWithPreInit(This) {
    assert(get(This) && "get is not tuned for post-update.");
  }

  /// Set pre-initialization statement for the clause.
  void setPostUpdateExpr(Expr *S) { PostUpdate = S; }

public:
  /// Get post-update expression for the clause.
  const Expr *getPostUpdateExpr() const { return PostUpdate; }

  /// Get post-update expression for the clause.
  Expr *getPostUpdateExpr() { return PostUpdate; }

  static ACCClauseWithPostUpdate *get(ACCClause *C);
  static const ACCClauseWithPostUpdate *get(const ACCClause *C);
};

/// \brief This represents clauses with the list of variables like 'private',
/// 'firstprivate', 'copyin', 'shared', or 'reduction' clauses in the
/// '#pragma acc ...' directives.
template <class T> class ACCVarListClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Number of variables in the list.
  unsigned NumVars;

protected:
  /// \brief Build a clause with \a N variables
  ///
  /// \param K Kind of the clause.
  /// \param StartLoc Starting location of the clause (the clause keyword).
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCVarListClause(OpenACCClauseKind K, SourceLocation StartLoc,
                   SourceLocation LParenLoc, SourceLocation EndLoc, unsigned N)
      : ACCClause(K, StartLoc, EndLoc), LParenLoc(LParenLoc), NumVars(N) {}

  /// \brief Fetches list of variables associated with this clause.
  MutableArrayRef<Expr *> getVarRefs() {
    return MutableArrayRef<Expr *>(
        static_cast<T *>(this)->template getTrailingObjects<Expr *>(), NumVars);
  }

  /// \brief Sets the list of variables for this clause.
  void setVarRefs(ArrayRef<Expr *> VL) {
    assert(VL.size() == NumVars &&
           "Number of variables is not the same as the preallocated buffer");
    std::copy(VL.begin(), VL.end(),
              static_cast<T *>(this)->template getTrailingObjects<Expr *>());
  }

public:
  using varlist_iterator = MutableArrayRef<Expr *>::iterator;
  using varlist_const_iterator = ArrayRef<const Expr *>::iterator;
  using varlist_range = llvm::iterator_range<varlist_iterator>;
  using varlist_const_range = llvm::iterator_range<varlist_const_iterator>;

  unsigned varlist_size() const { return NumVars; }
  bool varlist_empty() const { return NumVars == 0; }

  varlist_range varlists() {
    return varlist_range(varlist_begin(), varlist_end());
  }
  varlist_const_range varlists() const {
    return varlist_const_range(varlist_begin(), varlist_end());
  }

  varlist_iterator varlist_begin() { return getVarRefs().begin(); }
  varlist_iterator varlist_end() { return getVarRefs().end(); }
  varlist_const_iterator varlist_begin() const { return getVarRefs().begin(); }
  varlist_const_iterator varlist_end() const { return getVarRefs().end(); }

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Fetches list of all variables in the clause.
  ArrayRef<const Expr *> getVarRefs() const {
    return llvm::makeArrayRef(
        static_cast<const T *>(this)->template getTrailingObjects<Expr *>(),
        NumVars);
  }
};

/// \brief This represents 'if' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc parallel if(parallel:a > 5)
/// \endcode
/// In this example directive '#pragma acc parallel' has simple 'if' clause with
/// condition 'a > 5' and directive name modifier 'parallel'.
class ACCIfClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Condition of the 'if' clause.
  Stmt *Condition = nullptr;

  /// \brief Location of ':' (if any).
  SourceLocation ColonLoc;

  /// \brief Directive name modifier for the clause.
  OpenACCDirectiveKind NameModifier = ACCD_unknown;

  /// \brief Name modifier location.
  SourceLocation NameModifierLoc;

  /// \brief Set condition.
  void setCondition(Expr *Cond) { Condition = Cond; }

  /// \brief Set directive name modifier for the clause.
  void setNameModifier(OpenACCDirectiveKind NM) { NameModifier = NM; }

  /// \brief Set location of directive name modifier for the clause.
  void setNameModifierLoc(SourceLocation Loc) { NameModifierLoc = Loc; }

  /// \brief Set location of ':'.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Build 'if' clause with condition \a Cond.
  ///
  /// \param NameModifier [OpenACC 4.1] Directive name modifier of clause.
  /// \param Cond Condition of the clause.
  /// \param HelperCond Helper condition for the clause.
  /// \param CaptureRegion Innermost OpenACC region where expressions in this
  /// clause must be captured.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param NameModifierLoc Location of directive name modifier.
  /// \param ColonLoc [OpenACC 4.1] Location of ':'.
  /// \param EndLoc Ending location of the clause.
  ACCIfClause(OpenACCDirectiveKind NameModifier, Expr *Cond, Stmt *HelperCond,
              OpenACCDirectiveKind CaptureRegion, SourceLocation StartLoc,
              SourceLocation LParenLoc, SourceLocation NameModifierLoc,
              SourceLocation ColonLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_if, StartLoc, EndLoc), ACCClauseWithPreInit(this),
        LParenLoc(LParenLoc), Condition(Cond), ColonLoc(ColonLoc),
        NameModifier(NameModifier), NameModifierLoc(NameModifierLoc) {
    setPreInitStmt(HelperCond, CaptureRegion);
  }

  /// \brief Build an empty clause.
  ACCIfClause()
      : ACCClause(ACCC_if, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return the location of ':'.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// \brief Returns condition.
  Expr *getCondition() const { return cast_or_null<Expr>(Condition); }

  /// \brief Return directive name modifier associated with the clause.
  OpenACCDirectiveKind getNameModifier() const { return NameModifier; }

  /// \brief Return the location of directive name modifier.
  SourceLocation getNameModifierLoc() const { return NameModifierLoc; }

  child_range children() { return child_range(&Condition, &Condition + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_if;
  }
};

/// \brief This represents 'final' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc task final(a > 5)
/// \endcode
/// In this example directive '#pragma acc task' has simple 'final'
/// clause with condition 'a > 5'.
class ACCFinalClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Condition of the 'if' clause.
  Stmt *Condition = nullptr;

  /// \brief Set condition.
  void setCondition(Expr *Cond) { Condition = Cond; }

public:
  /// \brief Build 'final' clause with condition \a Cond.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param Cond Condition of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCFinalClause(Expr *Cond, SourceLocation StartLoc, SourceLocation LParenLoc,
                 SourceLocation EndLoc)
      : ACCClause(ACCC_final, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Condition(Cond) {}

  /// \brief Build an empty clause.
  ACCFinalClause()
      : ACCClause(ACCC_final, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Returns condition.
  Expr *getCondition() const { return cast_or_null<Expr>(Condition); }

  child_range children() { return child_range(&Condition, &Condition + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_final;
  }
};

/// \brief This represents 'num_threads' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc parallel num_threads(6)
/// \endcode
/// In this example directive '#pragma acc parallel' has simple 'num_threads'
/// clause with number of threads '6'.
class ACCNumThreadsClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Condition of the 'num_threads' clause.
  Stmt *NumThreads = nullptr;

  /// \brief Set condition.
  void setNumThreads(Expr *NThreads) { NumThreads = NThreads; }

public:
  /// \brief Build 'num_threads' clause with condition \a NumThreads.
  ///
  /// \param NumThreads Number of threads for the construct.
  /// \param HelperNumThreads Helper Number of threads for the construct.
  /// \param CaptureRegion Innermost OpenACC region where expressions in this
  /// clause must be captured.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCNumThreadsClause(Expr *NumThreads, Stmt *HelperNumThreads,
                      OpenACCDirectiveKind CaptureRegion,
                      SourceLocation StartLoc, SourceLocation LParenLoc,
                      SourceLocation EndLoc)
      : ACCClause(ACCC_num_threads, StartLoc, EndLoc),
        ACCClauseWithPreInit(this), LParenLoc(LParenLoc),
        NumThreads(NumThreads) {
    setPreInitStmt(HelperNumThreads, CaptureRegion);
  }

  /// \brief Build an empty clause.
  ACCNumThreadsClause()
      : ACCClause(ACCC_num_threads, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Returns number of threads.
  Expr *getNumThreads() const { return cast_or_null<Expr>(NumThreads); }

  child_range children() { return child_range(&NumThreads, &NumThreads + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_num_threads;
  }
};

/// \brief This represents 'safelen' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc vector safelen(4)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'safelen'
/// with single expression '4'.
/// If the safelen clause is used then no two iterations executed
/// concurrently with vector instructions can have a greater distance
/// in the logical iteration space than its value. The parameter of
/// the safelen clause must be a constant positive integer expression.
class ACCSafelenClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Safe iteration space distance.
  Stmt *Safelen = nullptr;

  /// \brief Set safelen.
  void setSafelen(Expr *Len) { Safelen = Len; }

public:
  /// \brief Build 'safelen' clause.
  ///
  /// \param Len Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCSafelenClause(Expr *Len, SourceLocation StartLoc, SourceLocation LParenLoc,
                   SourceLocation EndLoc)
      : ACCClause(ACCC_safelen, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Safelen(Len) {}

  /// \brief Build an empty clause.
  explicit ACCSafelenClause()
      : ACCClause(ACCC_safelen, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return safe iteration space distance.
  Expr *getSafelen() const { return cast_or_null<Expr>(Safelen); }

  child_range children() { return child_range(&Safelen, &Safelen + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_safelen;
  }
};

/// \brief This represents 'vectorlen' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc vector vectorlen(4)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'vectorlen'
/// with single expression '4'.
/// If the 'vectorlen' clause is used then it specifies the preferred number of
/// iterations to be executed concurrently. The parameter of the 'vectorlen'
/// clause must be a constant positive integer expression.
class ACCVectorlenClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Safe iteration space distance.
  Stmt *Vectorlen = nullptr;

  /// \brief Set vectorlen.
  void setVectorlen(Expr *Len) { Vectorlen = Len; }

public:
  /// \brief Build 'vectorlen' clause.
  ///
  /// \param Len Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCVectorlenClause(Expr *Len, SourceLocation StartLoc, SourceLocation LParenLoc,
                   SourceLocation EndLoc)
      : ACCClause(ACCC_vectorlen, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Vectorlen(Len) {}

  /// \brief Build an empty clause.
  explicit ACCVectorlenClause()
      : ACCClause(ACCC_vectorlen, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return safe iteration space distance.
  Expr *getVectorlen() const { return cast_or_null<Expr>(Vectorlen); }

  child_range children() { return child_range(&Vectorlen, &Vectorlen + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_vectorlen;
  }
};

/// \brief This represents 'collapse' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc vector collapse(3)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'collapse'
/// with single expression '3'.
/// The parameter must be a constant positive integer expression, it specifies
/// the number of nested loops that should be collapsed into a single iteration
/// space.
class ACCCollapseClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Number of for-loops.
  Stmt *NumForLoops = nullptr;

  /// \brief Set the number of associated for-loops.
  void setNumForLoops(Expr *Num) { NumForLoops = Num; }

public:
  /// \brief Build 'collapse' clause.
  ///
  /// \param Num Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCCollapseClause(Expr *Num, SourceLocation StartLoc,
                    SourceLocation LParenLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_collapse, StartLoc, EndLoc), LParenLoc(LParenLoc),
        NumForLoops(Num) {}

  /// \brief Build an empty clause.
  explicit ACCCollapseClause()
      : ACCClause(ACCC_collapse, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return the number of associated for-loops.
  Expr *getNumForLoops() const { return cast_or_null<Expr>(NumForLoops); }

  child_range children() { return child_range(&NumForLoops, &NumForLoops + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_collapse;
  }
};

/// \brief This represents 'default' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc parallel default(shared)
/// \endcode
/// In this example directive '#pragma acc parallel' has simple 'default'
/// clause with kind 'shared'.
class ACCDefaultClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief A kind of the 'default' clause.
  OpenACCDefaultClauseKind Kind = ACCC_DEFAULT_unknown;

  /// \brief Start location of the kind in source code.
  SourceLocation KindKwLoc;

  /// \brief Set kind of the clauses.
  ///
  /// \param K Argument of clause.
  void setDefaultKind(OpenACCDefaultClauseKind K) { Kind = K; }

  /// \brief Set argument location.
  ///
  /// \param KLoc Argument location.
  void setDefaultKindKwLoc(SourceLocation KLoc) { KindKwLoc = KLoc; }

public:
  /// \brief Build 'default' clause with argument \a A ('none' or 'shared').
  ///
  /// \param A Argument of the clause ('none' or 'shared').
  /// \param ALoc Starting location of the argument.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCDefaultClause(OpenACCDefaultClauseKind A, SourceLocation ALoc,
                   SourceLocation StartLoc, SourceLocation LParenLoc,
                   SourceLocation EndLoc)
      : ACCClause(ACCC_default, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Kind(A), KindKwLoc(ALoc) {}

  /// \brief Build an empty clause.
  ACCDefaultClause()
      : ACCClause(ACCC_default, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Returns kind of the clause.
  OpenACCDefaultClauseKind getDefaultKind() const { return Kind; }

  /// \brief Returns location of clause kind.
  SourceLocation getDefaultKindKwLoc() const { return KindKwLoc; }

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_default;
  }
};

/// \brief This represents 'proc_bind' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc parallel proc_bind(master)
/// \endcode
/// In this example directive '#pragma acc parallel' has simple 'proc_bind'
/// clause with kind 'master'.
class ACCProcBindClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief A kind of the 'proc_bind' clause.
  OpenACCProcBindClauseKind Kind = ACCC_PROC_BIND_unknown;

  /// \brief Start location of the kind in source code.
  SourceLocation KindKwLoc;

  /// \brief Set kind of the clause.
  ///
  /// \param K Kind of clause.
  void setProcBindKind(OpenACCProcBindClauseKind K) { Kind = K; }

  /// \brief Set clause kind location.
  ///
  /// \param KLoc Kind location.
  void setProcBindKindKwLoc(SourceLocation KLoc) { KindKwLoc = KLoc; }

public:
  /// \brief Build 'proc_bind' clause with argument \a A ('master', 'close' or
  ///        'spread').
  ///
  /// \param A Argument of the clause ('master', 'close' or 'spread').
  /// \param ALoc Starting location of the argument.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCProcBindClause(OpenACCProcBindClauseKind A, SourceLocation ALoc,
                    SourceLocation StartLoc, SourceLocation LParenLoc,
                    SourceLocation EndLoc)
      : ACCClause(ACCC_proc_bind, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Kind(A), KindKwLoc(ALoc) {}

  /// \brief Build an empty clause.
  ACCProcBindClause()
      : ACCClause(ACCC_proc_bind, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Returns kind of the clause.
  OpenACCProcBindClauseKind getProcBindKind() const { return Kind; }

  /// \brief Returns location of clause kind.
  SourceLocation getProcBindKindKwLoc() const { return KindKwLoc; }

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_proc_bind;
  }
};

/// \brief This represents 'schedule' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc for schedule(static, 3)
/// \endcode
/// In this example directive '#pragma acc for' has 'schedule' clause with
/// arguments 'static' and '3'.
class ACCScheduleClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief A kind of the 'schedule' clause.
  OpenACCScheduleClauseKind Kind = ACCC_SCHEDULE_unknown;

  /// \brief Modifiers for 'schedule' clause.
  enum {FIRST, SECOND, NUM_MODIFIERS};
  OpenACCScheduleClauseModifier Modifiers[NUM_MODIFIERS];

  /// \brief Locations of modifiers.
  SourceLocation ModifiersLoc[NUM_MODIFIERS];

  /// \brief Start location of the schedule ind in source code.
  SourceLocation KindLoc;

  /// \brief Location of ',' (if any).
  SourceLocation CommaLoc;

  /// \brief Chunk size.
  Expr *ChunkSize = nullptr;

  /// \brief Set schedule kind.
  ///
  /// \param K Schedule kind.
  void setScheduleKind(OpenACCScheduleClauseKind K) { Kind = K; }

  /// \brief Set the first schedule modifier.
  ///
  /// \param M Schedule modifier.
  void setFirstScheduleModifier(OpenACCScheduleClauseModifier M) {
    Modifiers[FIRST] = M;
  }

  /// \brief Set the second schedule modifier.
  ///
  /// \param M Schedule modifier.
  void setSecondScheduleModifier(OpenACCScheduleClauseModifier M) {
    Modifiers[SECOND] = M;
  }

  /// \brief Set location of the first schedule modifier.
  void setFirstScheduleModifierLoc(SourceLocation Loc) {
    ModifiersLoc[FIRST] = Loc;
  }

  /// \brief Set location of the second schedule modifier.
  void setSecondScheduleModifierLoc(SourceLocation Loc) {
    ModifiersLoc[SECOND] = Loc;
  }

  /// \brief Set schedule modifier location.
  ///
  /// \param M Schedule modifier location.
  void setScheduleModifer(OpenACCScheduleClauseModifier M) {
    if (Modifiers[FIRST] == ACCC_SCHEDULE_MODIFIER_unknown)
      Modifiers[FIRST] = M;
    else {
      assert(Modifiers[SECOND] == ACCC_SCHEDULE_MODIFIER_unknown);
      Modifiers[SECOND] = M;
    }
  }

  /// \brief Sets the location of '('.
  ///
  /// \param Loc Location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Set schedule kind start location.
  ///
  /// \param KLoc Schedule kind location.
  void setScheduleKindLoc(SourceLocation KLoc) { KindLoc = KLoc; }

  /// \brief Set location of ','.
  ///
  /// \param Loc Location of ','.
  void setCommaLoc(SourceLocation Loc) { CommaLoc = Loc; }

  /// \brief Set chunk size.
  ///
  /// \param E Chunk size.
  void setChunkSize(Expr *E) { ChunkSize = E; }

public:
  /// \brief Build 'schedule' clause with schedule kind \a Kind and chunk size
  /// expression \a ChunkSize.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param KLoc Starting location of the argument.
  /// \param CommaLoc Location of ','.
  /// \param EndLoc Ending location of the clause.
  /// \param Kind Schedule kind.
  /// \param ChunkSize Chunk size.
  /// \param HelperChunkSize Helper chunk size for combined directives.
  /// \param M1 The first modifier applied to 'schedule' clause.
  /// \param M1Loc Location of the first modifier
  /// \param M2 The second modifier applied to 'schedule' clause.
  /// \param M2Loc Location of the second modifier
  ACCScheduleClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                    SourceLocation KLoc, SourceLocation CommaLoc,
                    SourceLocation EndLoc, OpenACCScheduleClauseKind Kind,
                    Expr *ChunkSize, Stmt *HelperChunkSize,
                    OpenACCScheduleClauseModifier M1, SourceLocation M1Loc,
                    OpenACCScheduleClauseModifier M2, SourceLocation M2Loc)
      : ACCClause(ACCC_schedule, StartLoc, EndLoc), ACCClauseWithPreInit(this),
        LParenLoc(LParenLoc), Kind(Kind), KindLoc(KLoc), CommaLoc(CommaLoc),
        ChunkSize(ChunkSize) {
    setPreInitStmt(HelperChunkSize);
    Modifiers[FIRST] = M1;
    Modifiers[SECOND] = M2;
    ModifiersLoc[FIRST] = M1Loc;
    ModifiersLoc[SECOND] = M2Loc;
  }

  /// \brief Build an empty clause.
  explicit ACCScheduleClause()
      : ACCClause(ACCC_schedule, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {
    Modifiers[FIRST] = ACCC_SCHEDULE_MODIFIER_unknown;
    Modifiers[SECOND] = ACCC_SCHEDULE_MODIFIER_unknown;
  }

  /// \brief Get kind of the clause.
  OpenACCScheduleClauseKind getScheduleKind() const { return Kind; }

  /// \brief Get the first modifier of the clause.
  OpenACCScheduleClauseModifier getFirstScheduleModifier() const {
    return Modifiers[FIRST];
  }

  /// \brief Get the second modifier of the clause.
  OpenACCScheduleClauseModifier getSecondScheduleModifier() const {
    return Modifiers[SECOND];
  }

  /// \brief Get location of '('.
  SourceLocation getLParenLoc() { return LParenLoc; }

  /// \brief Get kind location.
  SourceLocation getScheduleKindLoc() { return KindLoc; }

  /// \brief Get the first modifier location.
  SourceLocation getFirstScheduleModifierLoc() const {
    return ModifiersLoc[FIRST];
  }

  /// \brief Get the second modifier location.
  SourceLocation getSecondScheduleModifierLoc() const {
    return ModifiersLoc[SECOND];
  }

  /// \brief Get location of ','.
  SourceLocation getCommaLoc() { return CommaLoc; }

  /// \brief Get chunk size.
  Expr *getChunkSize() { return ChunkSize; }

  /// \brief Get chunk size.
  const Expr *getChunkSize() const { return ChunkSize; }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(&ChunkSize),
                       reinterpret_cast<Stmt **>(&ChunkSize) + 1);
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_schedule;
  }
};

/// \brief This represents 'ordered' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc for ordered (2)
/// \endcode
/// In this example directive '#pragma acc for' has 'ordered' clause with
/// parameter 2.
class ACCOrderedClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Number of for-loops.
  Stmt *NumForLoops = nullptr;

  /// \brief Set the number of associated for-loops.
  void setNumForLoops(Expr *Num) { NumForLoops = Num; }

public:
  /// \brief Build 'ordered' clause.
  ///
  /// \param Num Expression, possibly associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCOrderedClause(Expr *Num, SourceLocation StartLoc,
                    SourceLocation LParenLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_ordered, StartLoc, EndLoc), LParenLoc(LParenLoc),
        NumForLoops(Num) {}

  /// \brief Build an empty clause.
  explicit ACCOrderedClause()
      : ACCClause(ACCC_ordered, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return the number of associated for-loops.
  Expr *getNumForLoops() const { return cast_or_null<Expr>(NumForLoops); }

  child_range children() { return child_range(&NumForLoops, &NumForLoops + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_ordered;
  }
};

/// \brief This represents 'nowait' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc for nowait
/// \endcode
/// In this example directive '#pragma acc for' has 'nowait' clause.
class ACCNowaitClause : public ACCClause {
public:
  /// \brief Build 'nowait' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCNowaitClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_nowait, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCNowaitClause()
      : ACCClause(ACCC_nowait, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_nowait;
  }
};

/// \brief This represents 'untied' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc task untied
/// \endcode
/// In this example directive '#pragma acc task' has 'untied' clause.
class ACCUntiedClause : public ACCClause {
public:
  /// \brief Build 'untied' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCUntiedClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_untied, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCUntiedClause()
      : ACCClause(ACCC_untied, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_untied;
  }
};

/// \brief This represents 'mergeable' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc task mergeable
/// \endcode
/// In this example directive '#pragma acc task' has 'mergeable' clause.
class ACCMergeableClause : public ACCClause {
public:
  /// \brief Build 'mergeable' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCMergeableClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_mergeable, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCMergeableClause()
      : ACCClause(ACCC_mergeable, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_mergeable;
  }
};

/// \brief This represents 'read' clause in the '#pragma acc atomic' directive.
///
/// \code
/// #pragma acc atomic read
/// \endcode
/// In this example directive '#pragma acc atomic' has 'read' clause.
class ACCReadClause : public ACCClause {
public:
  /// \brief Build 'read' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCReadClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_read, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCReadClause() : ACCClause(ACCC_read, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_read;
  }
};

/// \brief This represents 'write' clause in the '#pragma acc atomic' directive.
///
/// \code
/// #pragma acc atomic write
/// \endcode
/// In this example directive '#pragma acc atomic' has 'write' clause.
class ACCWriteClause : public ACCClause {
public:
  /// \brief Build 'write' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCWriteClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_write, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCWriteClause()
      : ACCClause(ACCC_write, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_write;
  }
};

/// \brief This represents 'update' clause in the '#pragma acc atomic'
/// directive.
///
/// \code
/// #pragma acc atomic update
/// \endcode
/// In this example directive '#pragma acc atomic' has 'update' clause.
class ACCUpdateClause : public ACCClause {
public:
  /// \brief Build 'update' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCUpdateClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_update, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCUpdateClause()
      : ACCClause(ACCC_update, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_update;
  }
};

/// \brief This represents 'capture' clause in the '#pragma acc atomic'
/// directive.
///
/// \code
/// #pragma acc atomic capture
/// \endcode
/// In this example directive '#pragma acc atomic' has 'capture' clause.
class ACCCaptureClause : public ACCClause {
public:
  /// \brief Build 'capture' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCCaptureClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_capture, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCCaptureClause()
      : ACCClause(ACCC_capture, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_capture;
  }
};

/// \brief This represents 'seq_cst' clause in the '#pragma acc atomic'
/// directive.
///
/// \code
/// #pragma acc atomic seq_cst
/// \endcode
/// In this example directive '#pragma acc atomic' has 'seq_cst' clause.
class ACCSeqCstClause : public ACCClause {
public:
  /// \brief Build 'seq_cst' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCSeqCstClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_seq_cst, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCSeqCstClause()
      : ACCClause(ACCC_seq_cst, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_seq_cst;
  }
};

/// \brief This represents clause 'private' in the '#pragma acc ...' directives.
///
/// \code
/// #pragma acc parallel private(a,b)
/// \endcode
/// In this example directive '#pragma acc parallel' has clause 'private'
/// with the variables 'a' and 'b'.
class ACCPrivateClause final
    : public ACCVarListClause<ACCPrivateClause>,
      private llvm::TrailingObjects<ACCPrivateClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCPrivateClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                   SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCPrivateClause>(ACCC_private, StartLoc, LParenLoc,
                                           EndLoc, N) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCPrivateClause(unsigned N)
      : ACCVarListClause<ACCPrivateClause>(ACCC_private, SourceLocation(),
                                           SourceLocation(), SourceLocation(),
                                           N) {}

  /// \brief Sets the list of references to private copies with initializers for
  /// new private variables.
  /// \param VL List of references.
  void setPrivateCopies(ArrayRef<Expr *> VL);

  /// \brief Gets the list of references to private copies with initializers for
  /// new private variables.
  MutableArrayRef<Expr *> getPrivateCopies() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivateCopies() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  /// \param PrivateVL List of references to private copies with initializers.
  static ACCPrivateClause *Create(const ASTContext &C, SourceLocation StartLoc,
                                  SourceLocation LParenLoc,
                                  SourceLocation EndLoc, ArrayRef<Expr *> VL,
                                  ArrayRef<Expr *> PrivateVL);

  /// \brief Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCPrivateClause *CreateEmpty(const ASTContext &C, unsigned N);

  using private_copies_iterator = MutableArrayRef<Expr *>::iterator;
  using private_copies_const_iterator = ArrayRef<const Expr *>::iterator;
  using private_copies_range = llvm::iterator_range<private_copies_iterator>;
  using private_copies_const_range =
      llvm::iterator_range<private_copies_const_iterator>;

  private_copies_range private_copies() {
    return private_copies_range(getPrivateCopies().begin(),
                                getPrivateCopies().end());
  }

  private_copies_const_range private_copies() const {
    return private_copies_const_range(getPrivateCopies().begin(),
                                      getPrivateCopies().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_private;
  }
};

/// \brief This represents clause 'firstprivate' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc parallel firstprivate(a,b)
/// \endcode
/// In this example directive '#pragma acc parallel' has clause 'firstprivate'
/// with the variables 'a' and 'b'.
class ACCFirstprivateClause final
    : public ACCVarListClause<ACCFirstprivateClause>,
      public ACCClauseWithPreInit,
      private llvm::TrailingObjects<ACCFirstprivateClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCFirstprivateClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                        SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCFirstprivateClause>(ACCC_firstprivate, StartLoc,
                                                LParenLoc, EndLoc, N),
        ACCClauseWithPreInit(this) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCFirstprivateClause(unsigned N)
      : ACCVarListClause<ACCFirstprivateClause>(
            ACCC_firstprivate, SourceLocation(), SourceLocation(),
            SourceLocation(), N),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the list of references to private copies with initializers for
  /// new private variables.
  /// \param VL List of references.
  void setPrivateCopies(ArrayRef<Expr *> VL);

  /// \brief Gets the list of references to private copies with initializers for
  /// new private variables.
  MutableArrayRef<Expr *> getPrivateCopies() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivateCopies() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// \brief Sets the list of references to initializer variables for new
  /// private variables.
  /// \param VL List of references.
  void setInits(ArrayRef<Expr *> VL);

  /// \brief Gets the list of references to initializer variables for new
  /// private variables.
  MutableArrayRef<Expr *> getInits() {
    return MutableArrayRef<Expr *>(getPrivateCopies().end(), varlist_size());
  }
  ArrayRef<const Expr *> getInits() const {
    return llvm::makeArrayRef(getPrivateCopies().end(), varlist_size());
  }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the original variables.
  /// \param PrivateVL List of references to private copies with initializers.
  /// \param InitVL List of references to auto generated variables used for
  /// initialization of a single array element. Used if firstprivate variable is
  /// of array type.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  static ACCFirstprivateClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> PrivateVL,
         ArrayRef<Expr *> InitVL, Stmt *PreInit);

  /// \brief Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCFirstprivateClause *CreateEmpty(const ASTContext &C, unsigned N);

  using private_copies_iterator = MutableArrayRef<Expr *>::iterator;
  using private_copies_const_iterator = ArrayRef<const Expr *>::iterator;
  using private_copies_range = llvm::iterator_range<private_copies_iterator>;
  using private_copies_const_range =
      llvm::iterator_range<private_copies_const_iterator>;

  private_copies_range private_copies() {
    return private_copies_range(getPrivateCopies().begin(),
                                getPrivateCopies().end());
  }
  private_copies_const_range private_copies() const {
    return private_copies_const_range(getPrivateCopies().begin(),
                                      getPrivateCopies().end());
  }

  using inits_iterator = MutableArrayRef<Expr *>::iterator;
  using inits_const_iterator = ArrayRef<const Expr *>::iterator;
  using inits_range = llvm::iterator_range<inits_iterator>;
  using inits_const_range = llvm::iterator_range<inits_const_iterator>;

  inits_range inits() {
    return inits_range(getInits().begin(), getInits().end());
  }
  inits_const_range inits() const {
    return inits_const_range(getInits().begin(), getInits().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_firstprivate;
  }
};

/// \brief This represents clause 'lastprivate' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc vector lastprivate(a,b)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'lastprivate'
/// with the variables 'a' and 'b'.
class ACCLastprivateClause final
    : public ACCVarListClause<ACCLastprivateClause>,
      public ACCClauseWithPostUpdate,
      private llvm::TrailingObjects<ACCLastprivateClause, Expr *> {
  // There are 4 additional tail-allocated arrays at the end of the class:
  // 1. Contains list of pseudo variables with the default initialization for
  // each non-firstprivate variables. Used in codegen for initialization of
  // lastprivate copies.
  // 2. List of helper expressions for proper generation of assignment operation
  // required for lastprivate clause. This list represents private variables
  // (for arrays, single array element).
  // 3. List of helper expressions for proper generation of assignment operation
  // required for lastprivate clause. This list represents original variables
  // (for arrays, single array element).
  // 4. List of helper expressions that represents assignment operation:
  // \code
  // DstExprs = SrcExprs;
  // \endcode
  // Required for proper codegen of final assignment performed by the
  // lastprivate clause.
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCLastprivateClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                       SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCLastprivateClause>(ACCC_lastprivate, StartLoc,
                                               LParenLoc, EndLoc, N),
        ACCClauseWithPostUpdate(this) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCLastprivateClause(unsigned N)
      : ACCVarListClause<ACCLastprivateClause>(
            ACCC_lastprivate, SourceLocation(), SourceLocation(),
            SourceLocation(), N),
        ACCClauseWithPostUpdate(this) {}

  /// \brief Get the list of helper expressions for initialization of private
  /// copies for lastprivate variables.
  MutableArrayRef<Expr *> getPrivateCopies() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivateCopies() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent private variables (for arrays, single
  /// array element) in the final assignment statement performed by the
  /// lastprivate clause.
  void setSourceExprs(ArrayRef<Expr *> SrcExprs);

  /// \brief Get the list of helper source expressions.
  MutableArrayRef<Expr *> getSourceExprs() {
    return MutableArrayRef<Expr *>(getPrivateCopies().end(), varlist_size());
  }
  ArrayRef<const Expr *> getSourceExprs() const {
    return llvm::makeArrayRef(getPrivateCopies().end(), varlist_size());
  }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent original variables (for arrays, single
  /// array element) in the final assignment statement performed by the
  /// lastprivate clause.
  void setDestinationExprs(ArrayRef<Expr *> DstExprs);

  /// \brief Get the list of helper destination expressions.
  MutableArrayRef<Expr *> getDestinationExprs() {
    return MutableArrayRef<Expr *>(getSourceExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getDestinationExprs() const {
    return llvm::makeArrayRef(getSourceExprs().end(), varlist_size());
  }

  /// \brief Set list of helper assignment expressions, required for proper
  /// codegen of the clause. These expressions are assignment expressions that
  /// assign private copy of the variable to original variable.
  void setAssignmentOps(ArrayRef<Expr *> AssignmentOps);

  /// \brief Get the list of helper assignment expressions.
  MutableArrayRef<Expr *> getAssignmentOps() {
    return MutableArrayRef<Expr *>(getDestinationExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getAssignmentOps() const {
    return llvm::makeArrayRef(getDestinationExprs().end(), varlist_size());
  }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  /// \param SrcExprs List of helper expressions for proper generation of
  /// assignment operation required for lastprivate clause. This list represents
  /// private variables (for arrays, single array element).
  /// \param DstExprs List of helper expressions for proper generation of
  /// assignment operation required for lastprivate clause. This list represents
  /// original variables (for arrays, single array element).
  /// \param AssignmentOps List of helper expressions that represents assignment
  /// operation:
  /// \code
  /// DstExprs = SrcExprs;
  /// \endcode
  /// Required for proper codegen of final assignment performed by the
  /// lastprivate clause.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  /// \param PostUpdate Expression that must be executed after exit from the
  /// OpenACC region with this clause.
  static ACCLastprivateClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> SrcExprs,
         ArrayRef<Expr *> DstExprs, ArrayRef<Expr *> AssignmentOps,
         Stmt *PreInit, Expr *PostUpdate);

  /// \brief Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCLastprivateClause *CreateEmpty(const ASTContext &C, unsigned N);

  using helper_expr_iterator = MutableArrayRef<Expr *>::iterator;
  using helper_expr_const_iterator = ArrayRef<const Expr *>::iterator;
  using helper_expr_range = llvm::iterator_range<helper_expr_iterator>;
  using helper_expr_const_range =
      llvm::iterator_range<helper_expr_const_iterator>;

  /// \brief Set list of helper expressions, required for generation of private
  /// copies of original lastprivate variables.
  void setPrivateCopies(ArrayRef<Expr *> PrivateCopies);

  helper_expr_const_range private_copies() const {
    return helper_expr_const_range(getPrivateCopies().begin(),
                                   getPrivateCopies().end());
  }

  helper_expr_range private_copies() {
    return helper_expr_range(getPrivateCopies().begin(),
                             getPrivateCopies().end());
  }

  helper_expr_const_range source_exprs() const {
    return helper_expr_const_range(getSourceExprs().begin(),
                                   getSourceExprs().end());
  }

  helper_expr_range source_exprs() {
    return helper_expr_range(getSourceExprs().begin(), getSourceExprs().end());
  }

  helper_expr_const_range destination_exprs() const {
    return helper_expr_const_range(getDestinationExprs().begin(),
                                   getDestinationExprs().end());
  }

  helper_expr_range destination_exprs() {
    return helper_expr_range(getDestinationExprs().begin(),
                             getDestinationExprs().end());
  }

  helper_expr_const_range assignment_ops() const {
    return helper_expr_const_range(getAssignmentOps().begin(),
                                   getAssignmentOps().end());
  }

  helper_expr_range assignment_ops() {
    return helper_expr_range(getAssignmentOps().begin(),
                             getAssignmentOps().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_lastprivate;
  }
};

/// \brief This represents clause 'shared' in the '#pragma acc ...' directives.
///
/// \code
/// #pragma acc parallel shared(a,b)
/// \endcode
/// In this example directive '#pragma acc parallel' has clause 'shared'
/// with the variables 'a' and 'b'.
class ACCSharedClause final
    : public ACCVarListClause<ACCSharedClause>,
      private llvm::TrailingObjects<ACCSharedClause, Expr *> {
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCSharedClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                  SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCSharedClause>(ACCC_shared, StartLoc, LParenLoc,
                                          EndLoc, N) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCSharedClause(unsigned N)
      : ACCVarListClause<ACCSharedClause>(ACCC_shared, SourceLocation(),
                                          SourceLocation(), SourceLocation(),
                                          N) {}

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  static ACCSharedClause *Create(const ASTContext &C, SourceLocation StartLoc,
                                 SourceLocation LParenLoc,
                                 SourceLocation EndLoc, ArrayRef<Expr *> VL);

  /// \brief Creates an empty clause with \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCSharedClause *CreateEmpty(const ASTContext &C, unsigned N);

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_shared;
  }
};

/// \brief This represents clause 'reduction' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc parallel reduction(+:a,b)
/// \endcode
/// In this example directive '#pragma acc parallel' has clause 'reduction'
/// with operator '+' and the variables 'a' and 'b'.
class ACCReductionClause final
    : public ACCVarListClause<ACCReductionClause>,
      public ACCClauseWithPostUpdate,
      private llvm::TrailingObjects<ACCReductionClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Location of ':'.
  SourceLocation ColonLoc;

  /// \brief Nested name specifier for C++.
  NestedNameSpecifierLoc QualifierLoc;

  /// \brief Name of custom operator.
  DeclarationNameInfo NameInfo;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param ColonLoc Location of ':'.
  /// \param N Number of the variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  ACCReductionClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                     SourceLocation ColonLoc, SourceLocation EndLoc, unsigned N,
                     NestedNameSpecifierLoc QualifierLoc,
                     const DeclarationNameInfo &NameInfo)
      : ACCVarListClause<ACCReductionClause>(ACCC_reduction, StartLoc,
                                             LParenLoc, EndLoc, N),
        ACCClauseWithPostUpdate(this), ColonLoc(ColonLoc),
        QualifierLoc(QualifierLoc), NameInfo(NameInfo) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCReductionClause(unsigned N)
      : ACCVarListClause<ACCReductionClause>(ACCC_reduction, SourceLocation(),
                                             SourceLocation(), SourceLocation(),
                                             N),
        ACCClauseWithPostUpdate(this) {}

  /// \brief Sets location of ':' symbol in clause.
  void setColonLoc(SourceLocation CL) { ColonLoc = CL; }

  /// \brief Sets the name info for specified reduction identifier.
  void setNameInfo(DeclarationNameInfo DNI) { NameInfo = DNI; }

  /// \brief Sets the nested name specifier.
  void setQualifierLoc(NestedNameSpecifierLoc NSL) { QualifierLoc = NSL; }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent private copy of the reduction
  /// variable.
  void setPrivates(ArrayRef<Expr *> Privates);

  /// \brief Get the list of helper privates.
  MutableArrayRef<Expr *> getPrivates() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivates() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent LHS expression in the final
  /// reduction expression performed by the reduction clause.
  void setLHSExprs(ArrayRef<Expr *> LHSExprs);

  /// \brief Get the list of helper LHS expressions.
  MutableArrayRef<Expr *> getLHSExprs() {
    return MutableArrayRef<Expr *>(getPrivates().end(), varlist_size());
  }
  ArrayRef<const Expr *> getLHSExprs() const {
    return llvm::makeArrayRef(getPrivates().end(), varlist_size());
  }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent RHS expression in the final
  /// reduction expression performed by the reduction clause.
  /// Also, variables in these expressions are used for proper initialization of
  /// reduction copies.
  void setRHSExprs(ArrayRef<Expr *> RHSExprs);

  /// \brief Get the list of helper destination expressions.
  MutableArrayRef<Expr *> getRHSExprs() {
    return MutableArrayRef<Expr *>(getLHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getRHSExprs() const {
    return llvm::makeArrayRef(getLHSExprs().end(), varlist_size());
  }

  /// \brief Set list of helper reduction expressions, required for proper
  /// codegen of the clause. These expressions are binary expressions or
  /// operator/custom reduction call that calculates new value from source
  /// helper expressions to destination helper expressions.
  void setReductionOps(ArrayRef<Expr *> ReductionOps);

  /// \brief Get the list of helper reduction expressions.
  MutableArrayRef<Expr *> getReductionOps() {
    return MutableArrayRef<Expr *>(getRHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getReductionOps() const {
    return llvm::makeArrayRef(getRHSExprs().end(), varlist_size());
  }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param VL The variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  /// \param Privates List of helper expressions for proper generation of
  /// private copies.
  /// \param LHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// LHSs of the reduction expressions.
  /// \param RHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// RHSs of the reduction expressions.
  /// Also, variables in these expressions are used for proper initialization of
  /// reduction copies.
  /// \param ReductionOps List of helper expressions that represents reduction
  /// expressions:
  /// \code
  /// LHSExprs binop RHSExprs;
  /// operator binop(LHSExpr, RHSExpr);
  /// <CutomReduction>(LHSExpr, RHSExpr);
  /// \endcode
  /// Required for proper codegen of final reduction operation performed by the
  /// reduction clause.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  /// \param PostUpdate Expression that must be executed after exit from the
  /// OpenACC region with this clause.
  static ACCReductionClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation ColonLoc, SourceLocation EndLoc, ArrayRef<Expr *> VL,
         NestedNameSpecifierLoc QualifierLoc,
         const DeclarationNameInfo &NameInfo, ArrayRef<Expr *> Privates,
         ArrayRef<Expr *> LHSExprs, ArrayRef<Expr *> RHSExprs,
         ArrayRef<Expr *> ReductionOps, Stmt *PreInit, Expr *PostUpdate);

  /// \brief Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCReductionClause *CreateEmpty(const ASTContext &C, unsigned N);

  /// \brief Gets location of ':' symbol in clause.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// \brief Gets the name info for specified reduction identifier.
  const DeclarationNameInfo &getNameInfo() const { return NameInfo; }

  /// \brief Gets the nested name specifier.
  NestedNameSpecifierLoc getQualifierLoc() const { return QualifierLoc; }

  using helper_expr_iterator = MutableArrayRef<Expr *>::iterator;
  using helper_expr_const_iterator = ArrayRef<const Expr *>::iterator;
  using helper_expr_range = llvm::iterator_range<helper_expr_iterator>;
  using helper_expr_const_range =
      llvm::iterator_range<helper_expr_const_iterator>;

  helper_expr_const_range privates() const {
    return helper_expr_const_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_range privates() {
    return helper_expr_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_const_range lhs_exprs() const {
    return helper_expr_const_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_range lhs_exprs() {
    return helper_expr_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_const_range rhs_exprs() const {
    return helper_expr_const_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_range rhs_exprs() {
    return helper_expr_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_const_range reduction_ops() const {
    return helper_expr_const_range(getReductionOps().begin(),
                                   getReductionOps().end());
  }

  helper_expr_range reduction_ops() {
    return helper_expr_range(getReductionOps().begin(),
                             getReductionOps().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_reduction;
  }
};

/// This represents clause 'task_reduction' in the '#pragma acc taskgroup'
/// directives.
///
/// \code
/// #pragma acc taskgroup task_reduction(+:a,b)
/// \endcode
/// In this example directive '#pragma acc taskgroup' has clause
/// 'task_reduction' with operator '+' and the variables 'a' and 'b'.
class ACCTaskReductionClause final
    : public ACCVarListClause<ACCTaskReductionClause>,
      public ACCClauseWithPostUpdate,
      private llvm::TrailingObjects<ACCTaskReductionClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Location of ':'.
  SourceLocation ColonLoc;

  /// Nested name specifier for C++.
  NestedNameSpecifierLoc QualifierLoc;

  /// Name of custom operator.
  DeclarationNameInfo NameInfo;

  /// Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param ColonLoc Location of ':'.
  /// \param N Number of the variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  ACCTaskReductionClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                         SourceLocation ColonLoc, SourceLocation EndLoc,
                         unsigned N, NestedNameSpecifierLoc QualifierLoc,
                         const DeclarationNameInfo &NameInfo)
      : ACCVarListClause<ACCTaskReductionClause>(ACCC_task_reduction, StartLoc,
                                                 LParenLoc, EndLoc, N),
        ACCClauseWithPostUpdate(this), ColonLoc(ColonLoc),
        QualifierLoc(QualifierLoc), NameInfo(NameInfo) {}

  /// Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCTaskReductionClause(unsigned N)
      : ACCVarListClause<ACCTaskReductionClause>(
            ACCC_task_reduction, SourceLocation(), SourceLocation(),
            SourceLocation(), N),
        ACCClauseWithPostUpdate(this) {}

  /// Sets location of ':' symbol in clause.
  void setColonLoc(SourceLocation CL) { ColonLoc = CL; }

  /// Sets the name info for specified reduction identifier.
  void setNameInfo(DeclarationNameInfo DNI) { NameInfo = DNI; }

  /// Sets the nested name specifier.
  void setQualifierLoc(NestedNameSpecifierLoc NSL) { QualifierLoc = NSL; }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent private copy of the reduction variable.
  void setPrivates(ArrayRef<Expr *> Privates);

  /// Get the list of helper privates.
  MutableArrayRef<Expr *> getPrivates() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivates() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent LHS expression in the final reduction
  /// expression performed by the reduction clause.
  void setLHSExprs(ArrayRef<Expr *> LHSExprs);

  /// Get the list of helper LHS expressions.
  MutableArrayRef<Expr *> getLHSExprs() {
    return MutableArrayRef<Expr *>(getPrivates().end(), varlist_size());
  }
  ArrayRef<const Expr *> getLHSExprs() const {
    return llvm::makeArrayRef(getPrivates().end(), varlist_size());
  }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent RHS expression in the final reduction
  /// expression performed by the reduction clause. Also, variables in these
  /// expressions are used for proper initialization of reduction copies.
  void setRHSExprs(ArrayRef<Expr *> RHSExprs);

  ///  Get the list of helper destination expressions.
  MutableArrayRef<Expr *> getRHSExprs() {
    return MutableArrayRef<Expr *>(getLHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getRHSExprs() const {
    return llvm::makeArrayRef(getLHSExprs().end(), varlist_size());
  }

  /// Set list of helper reduction expressions, required for proper
  /// codegen of the clause. These expressions are binary expressions or
  /// operator/custom reduction call that calculates new value from source
  /// helper expressions to destination helper expressions.
  void setReductionOps(ArrayRef<Expr *> ReductionOps);

  ///  Get the list of helper reduction expressions.
  MutableArrayRef<Expr *> getReductionOps() {
    return MutableArrayRef<Expr *>(getRHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getReductionOps() const {
    return llvm::makeArrayRef(getRHSExprs().end(), varlist_size());
  }

public:
  /// Creates clause with a list of variables \a VL.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param VL The variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  /// \param Privates List of helper expressions for proper generation of
  /// private copies.
  /// \param LHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// LHSs of the reduction expressions.
  /// \param RHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// RHSs of the reduction expressions.
  /// Also, variables in these expressions are used for proper initialization of
  /// reduction copies.
  /// \param ReductionOps List of helper expressions that represents reduction
  /// expressions:
  /// \code
  /// LHSExprs binop RHSExprs;
  /// operator binop(LHSExpr, RHSExpr);
  /// <CutomReduction>(LHSExpr, RHSExpr);
  /// \endcode
  /// Required for proper codegen of final reduction operation performed by the
  /// reduction clause.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  /// \param PostUpdate Expression that must be executed after exit from the
  /// OpenACC region with this clause.
  static ACCTaskReductionClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation ColonLoc, SourceLocation EndLoc, ArrayRef<Expr *> VL,
         NestedNameSpecifierLoc QualifierLoc,
         const DeclarationNameInfo &NameInfo, ArrayRef<Expr *> Privates,
         ArrayRef<Expr *> LHSExprs, ArrayRef<Expr *> RHSExprs,
         ArrayRef<Expr *> ReductionOps, Stmt *PreInit, Expr *PostUpdate);

  /// Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCTaskReductionClause *CreateEmpty(const ASTContext &C, unsigned N);

  /// Gets location of ':' symbol in clause.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// Gets the name info for specified reduction identifier.
  const DeclarationNameInfo &getNameInfo() const { return NameInfo; }

  /// Gets the nested name specifier.
  NestedNameSpecifierLoc getQualifierLoc() const { return QualifierLoc; }

  using helper_expr_iterator = MutableArrayRef<Expr *>::iterator;
  using helper_expr_const_iterator = ArrayRef<const Expr *>::iterator;
  using helper_expr_range = llvm::iterator_range<helper_expr_iterator>;
  using helper_expr_const_range =
      llvm::iterator_range<helper_expr_const_iterator>;

  helper_expr_const_range privates() const {
    return helper_expr_const_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_range privates() {
    return helper_expr_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_const_range lhs_exprs() const {
    return helper_expr_const_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_range lhs_exprs() {
    return helper_expr_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_const_range rhs_exprs() const {
    return helper_expr_const_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_range rhs_exprs() {
    return helper_expr_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_const_range reduction_ops() const {
    return helper_expr_const_range(getReductionOps().begin(),
                                   getReductionOps().end());
  }

  helper_expr_range reduction_ops() {
    return helper_expr_range(getReductionOps().begin(),
                             getReductionOps().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_task_reduction;
  }
};

/// This represents clause 'in_reduction' in the '#pragma acc task' directives.
///
/// \code
/// #pragma acc task in_reduction(+:a,b)
/// \endcode
/// In this example directive '#pragma acc task' has clause 'in_reduction' with
/// operator '+' and the variables 'a' and 'b'.
class ACCInReductionClause final
    : public ACCVarListClause<ACCInReductionClause>,
      public ACCClauseWithPostUpdate,
      private llvm::TrailingObjects<ACCInReductionClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Location of ':'.
  SourceLocation ColonLoc;

  /// Nested name specifier for C++.
  NestedNameSpecifierLoc QualifierLoc;

  /// Name of custom operator.
  DeclarationNameInfo NameInfo;

  /// Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param ColonLoc Location of ':'.
  /// \param N Number of the variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  ACCInReductionClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                       SourceLocation ColonLoc, SourceLocation EndLoc,
                       unsigned N, NestedNameSpecifierLoc QualifierLoc,
                       const DeclarationNameInfo &NameInfo)
      : ACCVarListClause<ACCInReductionClause>(ACCC_in_reduction, StartLoc,
                                               LParenLoc, EndLoc, N),
        ACCClauseWithPostUpdate(this), ColonLoc(ColonLoc),
        QualifierLoc(QualifierLoc), NameInfo(NameInfo) {}

  /// Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCInReductionClause(unsigned N)
      : ACCVarListClause<ACCInReductionClause>(
            ACCC_in_reduction, SourceLocation(), SourceLocation(),
            SourceLocation(), N),
        ACCClauseWithPostUpdate(this) {}

  /// Sets location of ':' symbol in clause.
  void setColonLoc(SourceLocation CL) { ColonLoc = CL; }

  /// Sets the name info for specified reduction identifier.
  void setNameInfo(DeclarationNameInfo DNI) { NameInfo = DNI; }

  /// Sets the nested name specifier.
  void setQualifierLoc(NestedNameSpecifierLoc NSL) { QualifierLoc = NSL; }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent private copy of the reduction variable.
  void setPrivates(ArrayRef<Expr *> Privates);

  /// Get the list of helper privates.
  MutableArrayRef<Expr *> getPrivates() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivates() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent LHS expression in the final reduction
  /// expression performed by the reduction clause.
  void setLHSExprs(ArrayRef<Expr *> LHSExprs);

  /// Get the list of helper LHS expressions.
  MutableArrayRef<Expr *> getLHSExprs() {
    return MutableArrayRef<Expr *>(getPrivates().end(), varlist_size());
  }
  ArrayRef<const Expr *> getLHSExprs() const {
    return llvm::makeArrayRef(getPrivates().end(), varlist_size());
  }

  /// Set list of helper expressions, required for proper codegen of the clause.
  /// These expressions represent RHS expression in the final reduction
  /// expression performed by the reduction clause. Also, variables in these
  /// expressions are used for proper initialization of reduction copies.
  void setRHSExprs(ArrayRef<Expr *> RHSExprs);

  ///  Get the list of helper destination expressions.
  MutableArrayRef<Expr *> getRHSExprs() {
    return MutableArrayRef<Expr *>(getLHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getRHSExprs() const {
    return llvm::makeArrayRef(getLHSExprs().end(), varlist_size());
  }

  /// Set list of helper reduction expressions, required for proper
  /// codegen of the clause. These expressions are binary expressions or
  /// operator/custom reduction call that calculates new value from source
  /// helper expressions to destination helper expressions.
  void setReductionOps(ArrayRef<Expr *> ReductionOps);

  ///  Get the list of helper reduction expressions.
  MutableArrayRef<Expr *> getReductionOps() {
    return MutableArrayRef<Expr *>(getRHSExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getReductionOps() const {
    return llvm::makeArrayRef(getRHSExprs().end(), varlist_size());
  }

  /// Set list of helper reduction taskgroup descriptors.
  void setTaskgroupDescriptors(ArrayRef<Expr *> ReductionOps);

  ///  Get the list of helper reduction taskgroup descriptors.
  MutableArrayRef<Expr *> getTaskgroupDescriptors() {
    return MutableArrayRef<Expr *>(getReductionOps().end(), varlist_size());
  }
  ArrayRef<const Expr *> getTaskgroupDescriptors() const {
    return llvm::makeArrayRef(getReductionOps().end(), varlist_size());
  }

public:
  /// Creates clause with a list of variables \a VL.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param VL The variables in the clause.
  /// \param QualifierLoc The nested-name qualifier with location information
  /// \param NameInfo The full name info for reduction identifier.
  /// \param Privates List of helper expressions for proper generation of
  /// private copies.
  /// \param LHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// LHSs of the reduction expressions.
  /// \param RHSExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// RHSs of the reduction expressions.
  /// Also, variables in these expressions are used for proper initialization of
  /// reduction copies.
  /// \param ReductionOps List of helper expressions that represents reduction
  /// expressions:
  /// \code
  /// LHSExprs binop RHSExprs;
  /// operator binop(LHSExpr, RHSExpr);
  /// <CutomReduction>(LHSExpr, RHSExpr);
  /// \endcode
  /// Required for proper codegen of final reduction operation performed by the
  /// reduction clause.
  /// \param TaskgroupDescriptors List of helper taskgroup descriptors for
  /// corresponding items in parent taskgroup task_reduction clause.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  /// \param PostUpdate Expression that must be executed after exit from the
  /// OpenACC region with this clause.
  static ACCInReductionClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation ColonLoc, SourceLocation EndLoc, ArrayRef<Expr *> VL,
         NestedNameSpecifierLoc QualifierLoc,
         const DeclarationNameInfo &NameInfo, ArrayRef<Expr *> Privates,
         ArrayRef<Expr *> LHSExprs, ArrayRef<Expr *> RHSExprs,
         ArrayRef<Expr *> ReductionOps, ArrayRef<Expr *> TaskgroupDescriptors,
         Stmt *PreInit, Expr *PostUpdate);

  /// Creates an empty clause with the place for \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCInReductionClause *CreateEmpty(const ASTContext &C, unsigned N);

  /// Gets location of ':' symbol in clause.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// Gets the name info for specified reduction identifier.
  const DeclarationNameInfo &getNameInfo() const { return NameInfo; }

  /// Gets the nested name specifier.
  NestedNameSpecifierLoc getQualifierLoc() const { return QualifierLoc; }

  using helper_expr_iterator = MutableArrayRef<Expr *>::iterator;
  using helper_expr_const_iterator = ArrayRef<const Expr *>::iterator;
  using helper_expr_range = llvm::iterator_range<helper_expr_iterator>;
  using helper_expr_const_range =
      llvm::iterator_range<helper_expr_const_iterator>;

  helper_expr_const_range privates() const {
    return helper_expr_const_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_range privates() {
    return helper_expr_range(getPrivates().begin(), getPrivates().end());
  }

  helper_expr_const_range lhs_exprs() const {
    return helper_expr_const_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_range lhs_exprs() {
    return helper_expr_range(getLHSExprs().begin(), getLHSExprs().end());
  }

  helper_expr_const_range rhs_exprs() const {
    return helper_expr_const_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_range rhs_exprs() {
    return helper_expr_range(getRHSExprs().begin(), getRHSExprs().end());
  }

  helper_expr_const_range reduction_ops() const {
    return helper_expr_const_range(getReductionOps().begin(),
                                   getReductionOps().end());
  }

  helper_expr_range reduction_ops() {
    return helper_expr_range(getReductionOps().begin(),
                             getReductionOps().end());
  }

  helper_expr_const_range taskgroup_descriptors() const {
    return helper_expr_const_range(getTaskgroupDescriptors().begin(),
                                   getTaskgroupDescriptors().end());
  }

  helper_expr_range taskgroup_descriptors() {
    return helper_expr_range(getTaskgroupDescriptors().begin(),
                             getTaskgroupDescriptors().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_in_reduction;
  }
};

/// \brief This represents clause 'linear' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc vector linear(a,b : 2)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'linear'
/// with variables 'a', 'b' and linear step '2'.
class ACCLinearClause final
    : public ACCVarListClause<ACCLinearClause>,
      public ACCClauseWithPostUpdate,
      private llvm::TrailingObjects<ACCLinearClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Modifier of 'linear' clause.
  OpenACCLinearClauseKind Modifier = ACCC_LINEAR_val;

  /// \brief Location of linear modifier if any.
  SourceLocation ModifierLoc;

  /// \brief Location of ':'.
  SourceLocation ColonLoc;

  /// \brief Sets the linear step for clause.
  void setStep(Expr *Step) { *(getFinals().end()) = Step; }

  /// \brief Sets the expression to calculate linear step for clause.
  void setCalcStep(Expr *CalcStep) { *(getFinals().end() + 1) = CalcStep; }

  /// \brief Build 'linear' clause with given number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of variables.
  ACCLinearClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                  OpenACCLinearClauseKind Modifier, SourceLocation ModifierLoc,
                  SourceLocation ColonLoc, SourceLocation EndLoc,
                  unsigned NumVars)
      : ACCVarListClause<ACCLinearClause>(ACCC_linear, StartLoc, LParenLoc,
                                          EndLoc, NumVars),
        ACCClauseWithPostUpdate(this), Modifier(Modifier),
        ModifierLoc(ModifierLoc), ColonLoc(ColonLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of variables.
  explicit ACCLinearClause(unsigned NumVars)
      : ACCVarListClause<ACCLinearClause>(ACCC_linear, SourceLocation(),
                                          SourceLocation(), SourceLocation(),
                                          NumVars),
        ACCClauseWithPostUpdate(this) {}

  /// \brief Gets the list of initial values for linear variables.
  ///
  /// There are NumVars expressions with initial values allocated after the
  /// varlist, they are followed by NumVars update expressions (used to update
  /// the linear variable's value on current iteration) and they are followed by
  /// NumVars final expressions (used to calculate the linear variable's
  /// value after the loop body). After these lists, there are 2 helper
  /// expressions - linear step and a helper to calculate it before the
  /// loop body (used when the linear step is not constant):
  ///
  /// { Vars[] /* in ACCVarListClause */; Privates[]; Inits[]; Updates[];
  /// Finals[]; Step; CalcStep; }
  MutableArrayRef<Expr *> getPrivates() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivates() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  MutableArrayRef<Expr *> getInits() {
    return MutableArrayRef<Expr *>(getPrivates().end(), varlist_size());
  }
  ArrayRef<const Expr *> getInits() const {
    return llvm::makeArrayRef(getPrivates().end(), varlist_size());
  }

  /// \brief Sets the list of update expressions for linear variables.
  MutableArrayRef<Expr *> getUpdates() {
    return MutableArrayRef<Expr *>(getInits().end(), varlist_size());
  }
  ArrayRef<const Expr *> getUpdates() const {
    return llvm::makeArrayRef(getInits().end(), varlist_size());
  }

  /// \brief Sets the list of final update expressions for linear variables.
  MutableArrayRef<Expr *> getFinals() {
    return MutableArrayRef<Expr *>(getUpdates().end(), varlist_size());
  }
  ArrayRef<const Expr *> getFinals() const {
    return llvm::makeArrayRef(getUpdates().end(), varlist_size());
  }

  /// \brief Sets the list of the copies of original linear variables.
  /// \param PL List of expressions.
  void setPrivates(ArrayRef<Expr *> PL);

  /// \brief Sets the list of the initial values for linear variables.
  /// \param IL List of expressions.
  void setInits(ArrayRef<Expr *> IL);

public:
  /// \brief Creates clause with a list of variables \a VL and a linear step
  /// \a Step.
  ///
  /// \param C AST Context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param Modifier Modifier of 'linear' clause.
  /// \param ModifierLoc Modifier location.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  /// \param PL List of private copies of original variables.
  /// \param IL List of initial values for the variables.
  /// \param Step Linear step.
  /// \param CalcStep Calculation of the linear step.
  /// \param PreInit Statement that must be executed before entering the OpenACC
  /// region with this clause.
  /// \param PostUpdate Expression that must be executed after exit from the
  /// OpenACC region with this clause.
  static ACCLinearClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         OpenACCLinearClauseKind Modifier, SourceLocation ModifierLoc,
         SourceLocation ColonLoc, SourceLocation EndLoc, ArrayRef<Expr *> VL,
         ArrayRef<Expr *> PL, ArrayRef<Expr *> IL, Expr *Step, Expr *CalcStep,
         Stmt *PreInit, Expr *PostUpdate);

  /// \brief Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of variables.
  static ACCLinearClause *CreateEmpty(const ASTContext &C, unsigned NumVars);

  /// \brief Set modifier.
  void setModifier(OpenACCLinearClauseKind Kind) { Modifier = Kind; }

  /// \brief Return modifier.
  OpenACCLinearClauseKind getModifier() const { return Modifier; }

  /// \brief Set modifier location.
  void setModifierLoc(SourceLocation Loc) { ModifierLoc = Loc; }

  /// \brief Return modifier location.
  SourceLocation getModifierLoc() const { return ModifierLoc; }

  /// \brief Sets the location of ':'.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

  /// \brief Returns the location of ':'.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// \brief Returns linear step.
  Expr *getStep() { return *(getFinals().end()); }

  /// \brief Returns linear step.
  const Expr *getStep() const { return *(getFinals().end()); }

  /// \brief Returns expression to calculate linear step.
  Expr *getCalcStep() { return *(getFinals().end() + 1); }

  /// \brief Returns expression to calculate linear step.
  const Expr *getCalcStep() const { return *(getFinals().end() + 1); }

  /// \brief Sets the list of update expressions for linear variables.
  /// \param UL List of expressions.
  void setUpdates(ArrayRef<Expr *> UL);

  /// \brief Sets the list of final update expressions for linear variables.
  /// \param FL List of expressions.
  void setFinals(ArrayRef<Expr *> FL);

  using privates_iterator = MutableArrayRef<Expr *>::iterator;
  using privates_const_iterator = ArrayRef<const Expr *>::iterator;
  using privates_range = llvm::iterator_range<privates_iterator>;
  using privates_const_range = llvm::iterator_range<privates_const_iterator>;

  privates_range privates() {
    return privates_range(getPrivates().begin(), getPrivates().end());
  }

  privates_const_range privates() const {
    return privates_const_range(getPrivates().begin(), getPrivates().end());
  }

  using inits_iterator = MutableArrayRef<Expr *>::iterator;
  using inits_const_iterator = ArrayRef<const Expr *>::iterator;
  using inits_range = llvm::iterator_range<inits_iterator>;
  using inits_const_range = llvm::iterator_range<inits_const_iterator>;

  inits_range inits() {
    return inits_range(getInits().begin(), getInits().end());
  }

  inits_const_range inits() const {
    return inits_const_range(getInits().begin(), getInits().end());
  }

  using updates_iterator = MutableArrayRef<Expr *>::iterator;
  using updates_const_iterator = ArrayRef<const Expr *>::iterator;
  using updates_range = llvm::iterator_range<updates_iterator>;
  using updates_const_range = llvm::iterator_range<updates_const_iterator>;

  updates_range updates() {
    return updates_range(getUpdates().begin(), getUpdates().end());
  }

  updates_const_range updates() const {
    return updates_const_range(getUpdates().begin(), getUpdates().end());
  }

  using finals_iterator = MutableArrayRef<Expr *>::iterator;
  using finals_const_iterator = ArrayRef<const Expr *>::iterator;
  using finals_range = llvm::iterator_range<finals_iterator>;
  using finals_const_range = llvm::iterator_range<finals_const_iterator>;

  finals_range finals() {
    return finals_range(getFinals().begin(), getFinals().end());
  }

  finals_const_range finals() const {
    return finals_const_range(getFinals().begin(), getFinals().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_linear;
  }
};

/// \brief This represents clause 'aligned' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc vector aligned(a,b : 8)
/// \endcode
/// In this example directive '#pragma acc vector' has clause 'aligned'
/// with variables 'a', 'b' and alignment '8'.
class ACCAlignedClause final
    : public ACCVarListClause<ACCAlignedClause>,
      private llvm::TrailingObjects<ACCAlignedClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Location of ':'.
  SourceLocation ColonLoc;

  /// \brief Sets the alignment for clause.
  void setAlignment(Expr *A) { *varlist_end() = A; }

  /// \brief Build 'aligned' clause with given number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of variables.
  ACCAlignedClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                   SourceLocation ColonLoc, SourceLocation EndLoc,
                   unsigned NumVars)
      : ACCVarListClause<ACCAlignedClause>(ACCC_aligned, StartLoc, LParenLoc,
                                           EndLoc, NumVars),
        ColonLoc(ColonLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of variables.
  explicit ACCAlignedClause(unsigned NumVars)
      : ACCVarListClause<ACCAlignedClause>(ACCC_aligned, SourceLocation(),
                                           SourceLocation(), SourceLocation(),
                                           NumVars) {}

public:
  /// \brief Creates clause with a list of variables \a VL and alignment \a A.
  ///
  /// \param C AST Context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param ColonLoc Location of ':'.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  /// \param A Alignment.
  static ACCAlignedClause *Create(const ASTContext &C, SourceLocation StartLoc,
                                  SourceLocation LParenLoc,
                                  SourceLocation ColonLoc,
                                  SourceLocation EndLoc, ArrayRef<Expr *> VL,
                                  Expr *A);

  /// \brief Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of variables.
  static ACCAlignedClause *CreateEmpty(const ASTContext &C, unsigned NumVars);

  /// \brief Sets the location of ':'.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

  /// \brief Returns the location of ':'.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// \brief Returns alignment.
  Expr *getAlignment() { return *varlist_end(); }

  /// \brief Returns alignment.
  const Expr *getAlignment() const { return *varlist_end(); }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_aligned;
  }
};

/// \brief This represents clause 'copyprivate' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc single copyprivate(a,b)
/// \endcode
/// In this example directive '#pragma acc single' has clause 'copyprivate'
/// with the variables 'a' and 'b'.
class ACCCopyprivateClause final
    : public ACCVarListClause<ACCCopyprivateClause>,
      private llvm::TrailingObjects<ACCCopyprivateClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCCopyprivateClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                       SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCCopyprivateClause>(ACCC_copyprivate, StartLoc,
                                               LParenLoc, EndLoc, N) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCCopyprivateClause(unsigned N)
      : ACCVarListClause<ACCCopyprivateClause>(
            ACCC_copyprivate, SourceLocation(), SourceLocation(),
            SourceLocation(), N) {}

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent source expression in the final
  /// assignment statement performed by the copyprivate clause.
  void setSourceExprs(ArrayRef<Expr *> SrcExprs);

  /// \brief Get the list of helper source expressions.
  MutableArrayRef<Expr *> getSourceExprs() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getSourceExprs() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// \brief Set list of helper expressions, required for proper codegen of the
  /// clause. These expressions represent destination expression in the final
  /// assignment statement performed by the copyprivate clause.
  void setDestinationExprs(ArrayRef<Expr *> DstExprs);

  /// \brief Get the list of helper destination expressions.
  MutableArrayRef<Expr *> getDestinationExprs() {
    return MutableArrayRef<Expr *>(getSourceExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getDestinationExprs() const {
    return llvm::makeArrayRef(getSourceExprs().end(), varlist_size());
  }

  /// \brief Set list of helper assignment expressions, required for proper
  /// codegen of the clause. These expressions are assignment expressions that
  /// assign source helper expressions to destination helper expressions
  /// correspondingly.
  void setAssignmentOps(ArrayRef<Expr *> AssignmentOps);

  /// \brief Get the list of helper assignment expressions.
  MutableArrayRef<Expr *> getAssignmentOps() {
    return MutableArrayRef<Expr *>(getDestinationExprs().end(), varlist_size());
  }
  ArrayRef<const Expr *> getAssignmentOps() const {
    return llvm::makeArrayRef(getDestinationExprs().end(), varlist_size());
  }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  /// \param SrcExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// sources.
  /// \param DstExprs List of helper expressions for proper generation of
  /// assignment operation required for copyprivate clause. This list represents
  /// destinations.
  /// \param AssignmentOps List of helper expressions that represents assignment
  /// operation:
  /// \code
  /// DstExprs = SrcExprs;
  /// \endcode
  /// Required for proper codegen of final assignment performed by the
  /// copyprivate clause.
  static ACCCopyprivateClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, ArrayRef<Expr *> VL, ArrayRef<Expr *> SrcExprs,
         ArrayRef<Expr *> DstExprs, ArrayRef<Expr *> AssignmentOps);

  /// \brief Creates an empty clause with \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCCopyprivateClause *CreateEmpty(const ASTContext &C, unsigned N);

  using helper_expr_iterator = MutableArrayRef<Expr *>::iterator;
  using helper_expr_const_iterator = ArrayRef<const Expr *>::iterator;
  using helper_expr_range = llvm::iterator_range<helper_expr_iterator>;
  using helper_expr_const_range =
      llvm::iterator_range<helper_expr_const_iterator>;

  helper_expr_const_range source_exprs() const {
    return helper_expr_const_range(getSourceExprs().begin(),
                                   getSourceExprs().end());
  }

  helper_expr_range source_exprs() {
    return helper_expr_range(getSourceExprs().begin(), getSourceExprs().end());
  }

  helper_expr_const_range destination_exprs() const {
    return helper_expr_const_range(getDestinationExprs().begin(),
                                   getDestinationExprs().end());
  }

  helper_expr_range destination_exprs() {
    return helper_expr_range(getDestinationExprs().begin(),
                             getDestinationExprs().end());
  }

  helper_expr_const_range assignment_ops() const {
    return helper_expr_const_range(getAssignmentOps().begin(),
                                   getAssignmentOps().end());
  }

  helper_expr_range assignment_ops() {
    return helper_expr_range(getAssignmentOps().begin(),
                             getAssignmentOps().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_copyprivate;
  }
};

/// \brief This represents implicit clause 'flush' for the '#pragma acc flush'
/// directive.
/// This clause does not exist by itself, it can be only as a part of 'acc
/// flush' directive. This clause is introduced to keep the original structure
/// of \a ACCExecutableDirective class and its derivatives and to use the
/// existing infrastructure of clauses with the list of variables.
///
/// \code
/// #pragma acc flush(a,b)
/// \endcode
/// In this example directive '#pragma acc flush' has implicit clause 'flush'
/// with the variables 'a' and 'b'.
class ACCFlushClause final
    : public ACCVarListClause<ACCFlushClause>,
      private llvm::TrailingObjects<ACCFlushClause, Expr *> {
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCFlushClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                 SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCFlushClause>(ACCC_flush, StartLoc, LParenLoc,
                                         EndLoc, N) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCFlushClause(unsigned N)
      : ACCVarListClause<ACCFlushClause>(ACCC_flush, SourceLocation(),
                                         SourceLocation(), SourceLocation(),
                                         N) {}

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param VL List of references to the variables.
  static ACCFlushClause *Create(const ASTContext &C, SourceLocation StartLoc,
                                SourceLocation LParenLoc, SourceLocation EndLoc,
                                ArrayRef<Expr *> VL);

  /// \brief Creates an empty clause with \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCFlushClause *CreateEmpty(const ASTContext &C, unsigned N);

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_flush;
  }
};

/// \brief This represents implicit clause 'depend' for the '#pragma acc task'
/// directive.
///
/// \code
/// #pragma acc task depend(in:a,b)
/// \endcode
/// In this example directive '#pragma acc task' with clause 'depend' with the
/// variables 'a' and 'b' with dependency 'in'.
class ACCDependClause final
    : public ACCVarListClause<ACCDependClause>,
      private llvm::TrailingObjects<ACCDependClause, Expr *> {
  friend class ACCClauseReader;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Dependency type (one of in, out, inout).
  OpenACCDependClauseKind DepKind = ACCC_DEPEND_unknown;

  /// \brief Dependency type location.
  SourceLocation DepLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build clause with number of variables \a N.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param N Number of the variables in the clause.
  ACCDependClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                  SourceLocation EndLoc, unsigned N)
      : ACCVarListClause<ACCDependClause>(ACCC_depend, StartLoc, LParenLoc,
                                          EndLoc, N) {}

  /// \brief Build an empty clause.
  ///
  /// \param N Number of variables.
  explicit ACCDependClause(unsigned N)
      : ACCVarListClause<ACCDependClause>(ACCC_depend, SourceLocation(),
                                          SourceLocation(), SourceLocation(),
                                          N) {}

  /// \brief Set dependency kind.
  void setDependencyKind(OpenACCDependClauseKind K) { DepKind = K; }

  /// \brief Set dependency kind and its location.
  void setDependencyLoc(SourceLocation Loc) { DepLoc = Loc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param DepKind Dependency type.
  /// \param DepLoc Location of the dependency type.
  /// \param ColonLoc Colon location.
  /// \param VL List of references to the variables.
  static ACCDependClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, OpenACCDependClauseKind DepKind,
         SourceLocation DepLoc, SourceLocation ColonLoc, ArrayRef<Expr *> VL);

  /// \brief Creates an empty clause with \a N variables.
  ///
  /// \param C AST context.
  /// \param N The number of variables.
  static ACCDependClause *CreateEmpty(const ASTContext &C, unsigned N);

  /// \brief Get dependency type.
  OpenACCDependClauseKind getDependencyKind() const { return DepKind; }

  /// \brief Get dependency type location.
  SourceLocation getDependencyLoc() const { return DepLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  /// Set the loop counter value for the depend clauses with 'sink|source' kind
  /// of dependency. Required for codegen.
  void setCounterValue(Expr *V);

  /// Get the loop counter value.
  Expr *getCounterValue();

  /// Get the loop counter value.
  const Expr *getCounterValue() const;

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_depend;
  }
};

/// \brief This represents 'device' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc target device(a)
/// \endcode
/// In this example directive '#pragma acc target' has clause 'device'
/// with single expression 'a'.
class ACCDeviceClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Device number.
  Stmt *Device = nullptr;

  /// \brief Set the device number.
  ///
  /// \param E Device number.
  void setDevice(Expr *E) { Device = E; }

public:
  /// \brief Build 'device' clause.
  ///
  /// \param E Expression associated with this clause.
  /// \param CaptureRegion Innermost OpenACC region where expressions in this
  /// clause must be captured.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCDeviceClause(Expr *E, Stmt *HelperE, OpenACCDirectiveKind CaptureRegion,
                  SourceLocation StartLoc, SourceLocation LParenLoc,
                  SourceLocation EndLoc)
      : ACCClause(ACCC_device, StartLoc, EndLoc), ACCClauseWithPreInit(this),
        LParenLoc(LParenLoc), Device(E) {
    setPreInitStmt(HelperE, CaptureRegion);
  }

  /// \brief Build an empty clause.
  ACCDeviceClause()
      : ACCClause(ACCC_device, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return device number.
  Expr *getDevice() { return cast<Expr>(Device); }

  /// \brief Return device number.
  Expr *getDevice() const { return cast<Expr>(Device); }

  child_range children() { return child_range(&Device, &Device + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_device;
  }
};

/// \brief This represents 'threads' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc ordered threads
/// \endcode
/// In this example directive '#pragma acc ordered' has simple 'threads' clause.
class ACCThreadsClause : public ACCClause {
public:
  /// \brief Build 'threads' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCThreadsClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_threads, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCThreadsClause()
      : ACCClause(ACCC_threads, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_threads;
  }
};

/// \brief This represents 'vector' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc ordered vector
/// \endcode
/// In this example directive '#pragma acc ordered' has simple 'vector' clause.
class ACCVectorClause : public ACCClause {
public:
  /// \brief Build 'vector' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCVectorClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_vector, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCVectorClause() : ACCClause(ACCC_vector, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_vector;
  }
};

/// \brief Struct that defines common infrastructure to handle mappable
/// expressions used in OpenACC clauses.
class ACCClauseMappableExprCommon {
public:
  // \brief Class that represents a component of a mappable expression. E.g.
  // for an expression S.a, the first component is a declaration reference
  // expression associated with 'S' and the second is a member expression
  // associated with the field declaration 'a'. If the expression is an array
  // subscript it may not have any associated declaration. In that case the
  // associated declaration is set to nullptr.
  class MappableComponent {
    // \brief Expression associated with the component.
    Expr *AssociatedExpression = nullptr;

    // \brief Declaration associated with the declaration. If the component does
    // not have a declaration (e.g. array subscripts or section), this is set to
    // nullptr.
    ValueDecl *AssociatedDeclaration = nullptr;

  public:
    explicit MappableComponent() = default;
    explicit MappableComponent(Expr *AssociatedExpression,
                               ValueDecl *AssociatedDeclaration)
        : AssociatedExpression(AssociatedExpression),
          AssociatedDeclaration(
              AssociatedDeclaration
                  ? cast<ValueDecl>(AssociatedDeclaration->getCanonicalDecl())
                  : nullptr) {}

    Expr *getAssociatedExpression() const { return AssociatedExpression; }

    ValueDecl *getAssociatedDeclaration() const {
      return AssociatedDeclaration;
    }
  };

  // \brief List of components of an expression. This first one is the whole
  // expression and the last one is the base expression.
  using MappableExprComponentList = SmallVector<MappableComponent, 8>;
  using MappableExprComponentListRef = ArrayRef<MappableComponent>;

  // \brief List of all component lists associated to the same base declaration.
  // E.g. if both 'S.a' and 'S.b' are a mappable expressions, each will have
  // their component list but the same base declaration 'S'.
  using MappableExprComponentLists = SmallVector<MappableExprComponentList, 8>;
  using MappableExprComponentListsRef = ArrayRef<MappableExprComponentList>;

protected:
  // \brief Return the total number of elements in a list of component lists.
  static unsigned
  getComponentsTotalNumber(MappableExprComponentListsRef ComponentLists);

  // \brief Return the total number of elements in a list of declarations. All
  // declarations are expected to be canonical.
  static unsigned
  getUniqueDeclarationsTotalNumber(ArrayRef<ValueDecl *> Declarations);
};

/// \brief This represents clauses with a list of expressions that are mappable.
/// Examples of these clauses are 'map' in
/// '#pragma acc target [enter|exit] [data]...' directives, and  'to' and 'from
/// in '#pragma acc target update...' directives.
template <class T>
class ACCMappableExprListClause : public ACCVarListClause<T>,
                                  public ACCClauseMappableExprCommon {
  friend class ACCClauseReader;

  /// \brief Number of unique declarations in this clause.
  unsigned NumUniqueDeclarations;

  /// \brief Number of component lists in this clause.
  unsigned NumComponentLists;

  /// \brief Total number of components in this clause.
  unsigned NumComponents;

protected:
  /// \brief Build a clause for \a NumUniqueDeclarations declarations, \a
  /// NumComponentLists total component lists, and \a NumComponents total
  /// components.
  ///
  /// \param K Kind of the clause.
  /// \param StartLoc Starting location of the clause (the clause keyword).
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause - one
  /// list for each expression in the clause.
  /// \param NumComponents Total number of expression components in the clause.
  ACCMappableExprListClause(OpenACCClauseKind K, SourceLocation StartLoc,
                            SourceLocation LParenLoc, SourceLocation EndLoc,
                            unsigned NumVars, unsigned NumUniqueDeclarations,
                            unsigned NumComponentLists, unsigned NumComponents)
      : ACCVarListClause<T>(K, StartLoc, LParenLoc, EndLoc, NumVars),
        NumUniqueDeclarations(NumUniqueDeclarations),
        NumComponentLists(NumComponentLists), NumComponents(NumComponents) {}

  /// \brief Get the unique declarations that are in the trailing objects of the
  /// class.
  MutableArrayRef<ValueDecl *> getUniqueDeclsRef() {
    return MutableArrayRef<ValueDecl *>(
        static_cast<T *>(this)->template getTrailingObjects<ValueDecl *>(),
        NumUniqueDeclarations);
  }

  /// \brief Get the unique declarations that are in the trailing objects of the
  /// class.
  ArrayRef<ValueDecl *> getUniqueDeclsRef() const {
    return ArrayRef<ValueDecl *>(
        static_cast<const T *>(this)
            ->template getTrailingObjects<ValueDecl *>(),
        NumUniqueDeclarations);
  }

  /// \brief Set the unique declarations that are in the trailing objects of the
  /// class.
  void setUniqueDecls(ArrayRef<ValueDecl *> UDs) {
    assert(UDs.size() == NumUniqueDeclarations &&
           "Unexpected amount of unique declarations.");
    std::copy(UDs.begin(), UDs.end(), getUniqueDeclsRef().begin());
  }

  /// \brief Get the number of lists per declaration that are in the trailing
  /// objects of the class.
  MutableArrayRef<unsigned> getDeclNumListsRef() {
    return MutableArrayRef<unsigned>(
        static_cast<T *>(this)->template getTrailingObjects<unsigned>(),
        NumUniqueDeclarations);
  }

  /// \brief Get the number of lists per declaration that are in the trailing
  /// objects of the class.
  ArrayRef<unsigned> getDeclNumListsRef() const {
    return ArrayRef<unsigned>(
        static_cast<const T *>(this)->template getTrailingObjects<unsigned>(),
        NumUniqueDeclarations);
  }

  /// \brief Set the number of lists per declaration that are in the trailing
  /// objects of the class.
  void setDeclNumLists(ArrayRef<unsigned> DNLs) {
    assert(DNLs.size() == NumUniqueDeclarations &&
           "Unexpected amount of list numbers.");
    std::copy(DNLs.begin(), DNLs.end(), getDeclNumListsRef().begin());
  }

  /// \brief Get the cumulative component lists sizes that are in the trailing
  /// objects of the class. They are appended after the number of lists.
  MutableArrayRef<unsigned> getComponentListSizesRef() {
    return MutableArrayRef<unsigned>(
        static_cast<T *>(this)->template getTrailingObjects<unsigned>() +
            NumUniqueDeclarations,
        NumComponentLists);
  }

  /// \brief Get the cumulative component lists sizes that are in the trailing
  /// objects of the class. They are appended after the number of lists.
  ArrayRef<unsigned> getComponentListSizesRef() const {
    return ArrayRef<unsigned>(
        static_cast<const T *>(this)->template getTrailingObjects<unsigned>() +
            NumUniqueDeclarations,
        NumComponentLists);
  }

  /// \brief Set the cumulative component lists sizes that are in the trailing
  /// objects of the class.
  void setComponentListSizes(ArrayRef<unsigned> CLSs) {
    assert(CLSs.size() == NumComponentLists &&
           "Unexpected amount of component lists.");
    std::copy(CLSs.begin(), CLSs.end(), getComponentListSizesRef().begin());
  }

  /// \brief Get the components that are in the trailing objects of the class.
  MutableArrayRef<MappableComponent> getComponentsRef() {
    return MutableArrayRef<MappableComponent>(
        static_cast<T *>(this)
            ->template getTrailingObjects<MappableComponent>(),
        NumComponents);
  }

  /// \brief Get the components that are in the trailing objects of the class.
  ArrayRef<MappableComponent> getComponentsRef() const {
    return ArrayRef<MappableComponent>(
        static_cast<const T *>(this)
            ->template getTrailingObjects<MappableComponent>(),
        NumComponents);
  }

  /// \brief Set the components that are in the trailing objects of the class.
  /// This requires the list sizes so that it can also fill the original
  /// expressions, which are the first component of each list.
  void setComponents(ArrayRef<MappableComponent> Components,
                     ArrayRef<unsigned> CLSs) {
    assert(Components.size() == NumComponents &&
           "Unexpected amount of component lists.");
    assert(CLSs.size() == NumComponentLists &&
           "Unexpected amount of list sizes.");
    std::copy(Components.begin(), Components.end(), getComponentsRef().begin());
  }

  /// \brief Fill the clause information from the list of declarations and
  /// associated component lists.
  void setClauseInfo(ArrayRef<ValueDecl *> Declarations,
                     MappableExprComponentListsRef ComponentLists) {
    // Perform some checks to make sure the data sizes are consistent with the
    // information available when the clause was created.
    assert(getUniqueDeclarationsTotalNumber(Declarations) ==
               NumUniqueDeclarations &&
           "Unexpected number of mappable expression info entries!");
    assert(getComponentsTotalNumber(ComponentLists) == NumComponents &&
           "Unexpected total number of components!");
    assert(Declarations.size() == ComponentLists.size() &&
           "Declaration and component lists size is not consistent!");
    assert(Declarations.size() == NumComponentLists &&
           "Unexpected declaration and component lists size!");

    // Organize the components by declaration and retrieve the original
    // expression. Original expressions are always the first component of the
    // mappable component list.
    llvm::MapVector<ValueDecl *, SmallVector<MappableExprComponentListRef, 8>>
        ComponentListMap;
    {
      auto CI = ComponentLists.begin();
      for (auto DI = Declarations.begin(), DE = Declarations.end(); DI != DE;
           ++DI, ++CI) {
        assert(!CI->empty() && "Invalid component list!");
        ComponentListMap[*DI].push_back(*CI);
      }
    }

    // Iterators of the target storage.
    auto UniqueDeclarations = getUniqueDeclsRef();
    auto UDI = UniqueDeclarations.begin();

    auto DeclNumLists = getDeclNumListsRef();
    auto DNLI = DeclNumLists.begin();

    auto ComponentListSizes = getComponentListSizesRef();
    auto CLSI = ComponentListSizes.begin();

    auto Components = getComponentsRef();
    auto CI = Components.begin();

    // Variable to compute the accumulation of the number of components.
    unsigned PrevSize = 0u;

    // Scan all the declarations and associated component lists.
    for (auto &M : ComponentListMap) {
      // The declaration.
      auto *D = M.first;
      // The component lists.
      auto CL = M.second;

      // Initialize the entry.
      *UDI = D;
      ++UDI;

      *DNLI = CL.size();
      ++DNLI;

      // Obtain the cumulative sizes and concatenate all the components in the
      // reserved storage.
      for (auto C : CL) {
        // Accumulate with the previous size.
        PrevSize += C.size();

        // Save the size.
        *CLSI = PrevSize;
        ++CLSI;

        // Append components after the current components iterator.
        CI = std::copy(C.begin(), C.end(), CI);
      }
    }
  }

public:
  /// \brief Return the number of unique base declarations in this clause.
  unsigned getUniqueDeclarationsNum() const { return NumUniqueDeclarations; }

  /// \brief Return the number of lists derived from the clause expressions.
  unsigned getTotalComponentListNum() const { return NumComponentLists; }

  /// \brief Return the total number of components in all lists derived from the
  /// clause.
  unsigned getTotalComponentsNum() const { return NumComponents; }

  /// \brief Iterator that browse the components by lists. It also allows
  /// browsing components of a single declaration.
  class const_component_lists_iterator
      : public llvm::iterator_adaptor_base<
            const_component_lists_iterator,
            MappableExprComponentListRef::const_iterator,
            std::forward_iterator_tag, MappableComponent, ptrdiff_t,
            MappableComponent, MappableComponent> {
    // The declaration the iterator currently refers to.
    ArrayRef<ValueDecl *>::iterator DeclCur;

    // The list number associated with the current declaration.
    ArrayRef<unsigned>::iterator NumListsCur;

    // Remaining lists for the current declaration.
    unsigned RemainingLists = 0;

    // The cumulative size of the previous list, or zero if there is no previous
    // list.
    unsigned PrevListSize = 0;

    // The cumulative sizes of the current list - it will delimit the remaining
    // range of interest.
    ArrayRef<unsigned>::const_iterator ListSizeCur;
    ArrayRef<unsigned>::const_iterator ListSizeEnd;

    // Iterator to the end of the components storage.
    MappableExprComponentListRef::const_iterator End;

  public:
    /// \brief Construct an iterator that scans all lists.
    explicit const_component_lists_iterator(
        ArrayRef<ValueDecl *> UniqueDecls, ArrayRef<unsigned> DeclsListNum,
        ArrayRef<unsigned> CumulativeListSizes,
        MappableExprComponentListRef Components)
        : const_component_lists_iterator::iterator_adaptor_base(
              Components.begin()),
          DeclCur(UniqueDecls.begin()), NumListsCur(DeclsListNum.begin()),
          ListSizeCur(CumulativeListSizes.begin()),
          ListSizeEnd(CumulativeListSizes.end()), End(Components.end()) {
      assert(UniqueDecls.size() == DeclsListNum.size() &&
             "Inconsistent number of declarations and list sizes!");
      if (!DeclsListNum.empty())
        RemainingLists = *NumListsCur;
    }

    /// \brief Construct an iterator that scan lists for a given declaration \a
    /// Declaration.
    explicit const_component_lists_iterator(
        const ValueDecl *Declaration, ArrayRef<ValueDecl *> UniqueDecls,
        ArrayRef<unsigned> DeclsListNum, ArrayRef<unsigned> CumulativeListSizes,
        MappableExprComponentListRef Components)
        : const_component_lists_iterator(UniqueDecls, DeclsListNum,
                                         CumulativeListSizes, Components) {
      // Look for the desired declaration. While we are looking for it, we
      // update the state so that we know the component where a given list
      // starts.
      for (; DeclCur != UniqueDecls.end(); ++DeclCur, ++NumListsCur) {
        if (*DeclCur == Declaration)
          break;

        assert(*NumListsCur > 0 && "No lists associated with declaration??");

        // Skip the lists associated with the current declaration, but save the
        // last list size that was skipped.
        std::advance(ListSizeCur, *NumListsCur - 1);
        PrevListSize = *ListSizeCur;
        ++ListSizeCur;
      }

      // If we didn't find any declaration, advance the iterator to after the
      // last component and set remaining lists to zero.
      if (ListSizeCur == CumulativeListSizes.end()) {
        this->I = End;
        RemainingLists = 0u;
        return;
      }

      // Set the remaining lists with the total number of lists of the current
      // declaration.
      RemainingLists = *NumListsCur;

      // Adjust the list size end iterator to the end of the relevant range.
      ListSizeEnd = ListSizeCur;
      std::advance(ListSizeEnd, RemainingLists);

      // Given that the list sizes are cumulative, the index of the component
      // that start the list is the size of the previous list.
      std::advance(this->I, PrevListSize);
    }

    // Return the array with the current list. The sizes are cumulative, so the
    // array size is the difference between the current size and previous one.
    std::pair<const ValueDecl *, MappableExprComponentListRef>
    operator*() const {
      assert(ListSizeCur != ListSizeEnd && "Invalid iterator!");
      return std::make_pair(
          *DeclCur,
          MappableExprComponentListRef(&*this->I, *ListSizeCur - PrevListSize));
    }
    std::pair<const ValueDecl *, MappableExprComponentListRef>
    operator->() const {
      return **this;
    }

    // Skip the components of the current list.
    const_component_lists_iterator &operator++() {
      assert(ListSizeCur != ListSizeEnd && RemainingLists &&
             "Invalid iterator!");

      // If we don't have more lists just skip all the components. Otherwise,
      // advance the iterator by the number of components in the current list.
      if (std::next(ListSizeCur) == ListSizeEnd) {
        this->I = End;
        RemainingLists = 0;
      } else {
        std::advance(this->I, *ListSizeCur - PrevListSize);
        PrevListSize = *ListSizeCur;

        // We are done with a declaration, move to the next one.
        if (!(--RemainingLists)) {
          ++DeclCur;
          ++NumListsCur;
          RemainingLists = *NumListsCur;
          assert(RemainingLists && "No lists in the following declaration??");
        }
      }

      ++ListSizeCur;
      return *this;
    }
  };

  using const_component_lists_range =
      llvm::iterator_range<const_component_lists_iterator>;

  /// \brief Iterators for all component lists.
  const_component_lists_iterator component_lists_begin() const {
    return const_component_lists_iterator(
        getUniqueDeclsRef(), getDeclNumListsRef(), getComponentListSizesRef(),
        getComponentsRef());
  }
  const_component_lists_iterator component_lists_end() const {
    return const_component_lists_iterator(
        ArrayRef<ValueDecl *>(), ArrayRef<unsigned>(), ArrayRef<unsigned>(),
        MappableExprComponentListRef(getComponentsRef().end(),
                                     getComponentsRef().end()));
  }
  const_component_lists_range component_lists() const {
    return {component_lists_begin(), component_lists_end()};
  }

  /// \brief Iterators for component lists associated with the provided
  /// declaration.
  const_component_lists_iterator
  decl_component_lists_begin(const ValueDecl *VD) const {
    return const_component_lists_iterator(
        VD, getUniqueDeclsRef(), getDeclNumListsRef(),
        getComponentListSizesRef(), getComponentsRef());
  }
  const_component_lists_iterator decl_component_lists_end() const {
    return component_lists_end();
  }
  const_component_lists_range decl_component_lists(const ValueDecl *VD) const {
    return {decl_component_lists_begin(VD), decl_component_lists_end()};
  }

  /// Iterators to access all the declarations, number of lists, list sizes, and
  /// components.
  using const_all_decls_iterator = ArrayRef<ValueDecl *>::iterator;
  using const_all_decls_range = llvm::iterator_range<const_all_decls_iterator>;

  const_all_decls_range all_decls() const {
    auto A = getUniqueDeclsRef();
    return const_all_decls_range(A.begin(), A.end());
  }

  using const_all_num_lists_iterator = ArrayRef<unsigned>::iterator;
  using const_all_num_lists_range =
      llvm::iterator_range<const_all_num_lists_iterator>;

  const_all_num_lists_range all_num_lists() const {
    auto A = getDeclNumListsRef();
    return const_all_num_lists_range(A.begin(), A.end());
  }

  using const_all_lists_sizes_iterator = ArrayRef<unsigned>::iterator;
  using const_all_lists_sizes_range =
      llvm::iterator_range<const_all_lists_sizes_iterator>;

  const_all_lists_sizes_range all_lists_sizes() const {
    auto A = getComponentListSizesRef();
    return const_all_lists_sizes_range(A.begin(), A.end());
  }

  using const_all_components_iterator = ArrayRef<MappableComponent>::iterator;
  using const_all_components_range =
      llvm::iterator_range<const_all_components_iterator>;

  const_all_components_range all_components() const {
    auto A = getComponentsRef();
    return const_all_components_range(A.begin(), A.end());
  }
};

/// \brief This represents clause 'map' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc target map(a,b)
/// \endcode
/// In this example directive '#pragma acc target' has clause 'map'
/// with the variables 'a' and 'b'.
class ACCMapClause final : public ACCMappableExprListClause<ACCMapClause>,
                           private llvm::TrailingObjects<
                               ACCMapClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCMapClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCMapClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCMapClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCMapClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};

/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Create
/// \brief This represents clause 'create' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc data create(a,b)
/// \endcode
/// In this example directive '#pragma acc data' has clause 'create'
/// with the variables 'a' and 'b'.
class ACCCreateClause final : public ACCMappableExprListClause<ACCCreateClause>,
                           private llvm::TrailingObjects<
                               ACCCreateClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  // TODO acc2mp modify infrastructure for copy. Also make copy(:) = map (tofrom:)
  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCreateClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCreateClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCCreateClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCCreateClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};

/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copy
/// \brief This represents clause 'copy' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc data copy(a,b)
/// \endcode
/// In this example directive '#pragma acc data' has clause 'copy'
/// with the variables 'a' and 'b'.
class ACCCopyClause final : public ACCMappableExprListClause<ACCCopyClause>,
                           private llvm::TrailingObjects<
                               ACCCopyClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  // TODO acc2mp modify infrastructure for copy. Also make copy(:) = map (tofrom:)
  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCCopyClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCCopyClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};
/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copyin
/// \brief This represents clause 'copyin' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc data copyin(a,b)
/// \endcode
/// In this example directive '#pragma acc data' has clause 'copyin'
/// with the variables 'a' and 'b'.
class ACCCopyinClause final : public ACCMappableExprListClause<ACCCopyinClause>,
                           private llvm::TrailingObjects<
                               ACCCopyinClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  // TODO acc2mp modify infrastructure for copyin. Also make copyin(:) = map (to:)
  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyinClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyinClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCCopyinClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCCopyinClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};
/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Copyout
/// \brief This represents clause 'copyout' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc data copyout(a,b)
/// \endcode
/// In this example directive '#pragma acc data' has clause 'copyout'
/// with the variables 'a' and 'b'.
class ACCCopyoutClause final : public ACCMappableExprListClause<ACCCopyoutClause>,
                           private llvm::TrailingObjects<
                               ACCCopyoutClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  // TODO acc2mp modify infrastructure for copyout. Also make copyout(:) = map (from:)
  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyoutClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCCopyoutClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCCopyoutClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCCopyoutClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};
/// MYHEADER : Basing the next class on ACCMapClause
//  Clause Delete
/// \brief This represents clause 'delete' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc data delete(a,b)
/// \endcode
/// In this example directive '#pragma acc data' has clause 'delete'
/// with the variables 'a' and 'b'.
class ACCDeleteClause final : public ACCMappableExprListClause<ACCCopyClause>,
                           private llvm::TrailingObjects<
                               ACCDeleteClause, Expr *, ValueDecl *, unsigned,
                               ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  // TODO acc2mp modify infrastructure for copy. Also make copy(:) = map (tofrom:)
  /// \brief Map type modifier for the 'map' clause.
  OpenACCMapClauseKind MapTypeModifier = ACCC_MAP_unknown;

  /// \brief Map type for the 'map' clause.
  OpenACCMapClauseKind MapType = ACCC_MAP_unknown;

  /// \brief Is this an implicit map type or not.
  bool MapTypeIsImplicit = false;

  /// \brief Location of the map type.
  SourceLocation MapLoc;

  /// \brief Colon location.
  SourceLocation ColonLoc;

  /// \brief Build a clause for \a NumVars listed expressions, \a
  /// NumUniqueDeclarations declarations, \a NumComponentLists total component
  /// lists, and \a NumComponents total expression components.
  ///
  /// \param MapTypeModifier Map type modifier.
  /// \param MapType Map type.
  /// \param MapTypeIsImplicit Map type is inferred implicitly.
  /// \param MapLoc Location of the map type.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCDeleteClause(OpenACCMapClauseKind MapTypeModifier,
                        OpenACCMapClauseKind MapType, bool MapTypeIsImplicit,
                        SourceLocation MapLoc, SourceLocation StartLoc,
                        SourceLocation LParenLoc, SourceLocation EndLoc,
                        unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_map, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents),
        MapTypeModifier(MapTypeModifier), MapType(MapType),
        MapTypeIsImplicit(MapTypeIsImplicit), MapLoc(MapLoc) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCDeleteClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                        unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_map, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// \brief Set type modifier for the clause.
  ///
  /// \param T Type Modifier for the clause.
  void setMapTypeModifier(OpenACCMapClauseKind T) { MapTypeModifier = T; }

  /// \brief Set type for the clause.
  ///
  /// \param T Type for the clause.
  void setMapType(OpenACCMapClauseKind T) { MapType = T; }

  /// \brief Set type location.
  ///
  /// \param TLoc Type location.
  void setMapLoc(SourceLocation TLoc) { MapLoc = TLoc; }

  /// \brief Set colon location.
  void setColonLoc(SourceLocation Loc) { ColonLoc = Loc; }

public:
  /// \brief Creates clause with a list of variables \a VL.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  /// \param TypeModifier Map type modifier.
  /// \param Type Map type.
  /// \param TypeIsImplicit Map type is inferred implicitly.
  /// \param TypeLoc Location of the map type.
  static ACCDeleteClause *Create(const ASTContext &C, SourceLocation StartLoc,
                              SourceLocation LParenLoc, SourceLocation EndLoc,
                              ArrayRef<Expr *> Vars,
                              ArrayRef<ValueDecl *> Declarations,
                              MappableExprComponentListsRef ComponentLists,
                              OpenACCMapClauseKind TypeModifier,
                              OpenACCMapClauseKind Type, bool TypeIsImplicit,
                              SourceLocation TypeLoc);

  /// \brief Creates an empty clause with the place for \a NumVars original
  /// expressions, \a NumUniqueDeclarations declarations, \NumComponentLists
  /// lists, and \a NumComponents expression components.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCDeleteClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                   unsigned NumUniqueDeclarations,
                                   unsigned NumComponentLists,
                                   unsigned NumComponents);

  /// \brief Fetches mapping kind for the clause.
  OpenACCMapClauseKind getMapType() const LLVM_READONLY { return MapType; }

  /// \brief Is this an implicit map type?
  /// We have to capture 'IsMapTypeImplicit' from the parser for more
  /// informative error messages.  It helps distinguish map(r) from
  /// map(tofrom: r), which is important to print more helpful error
  /// messages for some target directives.
  bool isImplicitMapType() const LLVM_READONLY { return MapTypeIsImplicit; }

  /// \brief Fetches the map type modifier for the clause.
  OpenACCMapClauseKind getMapTypeModifier() const LLVM_READONLY {
    return MapTypeModifier;
  }

  /// \brief Fetches location of clause mapping kind.
  SourceLocation getMapLoc() const LLVM_READONLY { return MapLoc; }

  /// \brief Get colon location.
  SourceLocation getColonLoc() const { return ColonLoc; }

  child_range children() {
    return child_range(
        reinterpret_cast<Stmt **>(varlist_begin()),
        reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_map;
  }
};

/// \brief This represents 'num_teams' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc teams num_teams(n)
/// \endcode
/// In this example directive '#pragma acc teams' has clause 'num_teams'
/// with single expression 'n'.
class ACCNumGangClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief NumTeams number.
  Stmt *NumTeams = nullptr;

  /// \brief Set the NumTeams number.
  ///
  /// \param E NumTeams number.
  void setNumTeams(Expr *E) { NumTeams = E; }

public:
  /// \brief Build 'num_teams' clause.
  ///
  /// \param E Expression associated with this clause.
  /// \param HelperE Helper Expression associated with this clause.
  /// \param CaptureRegion Innermost OpenACC region where expressions in this
  /// clause must be captured.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCNumGangClause(Expr *E, Stmt *HelperE, OpenACCDirectiveKind CaptureRegion,
                    SourceLocation StartLoc, SourceLocation LParenLoc,
                    SourceLocation EndLoc)
      : ACCClause(ACCC_num_gangs, StartLoc, EndLoc), ACCClauseWithPreInit(this),
        LParenLoc(LParenLoc), NumTeams(E) {
    setPreInitStmt(HelperE, CaptureRegion);
  }

  /// \brief Build an empty clause.
  ACCNumGangClause()
      : ACCClause(ACCC_num_gangs, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return NumTeams number.
  Expr *getNumTeams() { return cast<Expr>(NumTeams); }

  /// \brief Return NumTeams number.
  Expr *getNumTeams() const { return cast<Expr>(NumTeams); }

  child_range children() { return child_range(&NumTeams, &NumTeams + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_num_gangs;
  }
};

/// \brief This represents 'thread_limit' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc teams thread_limit(n)
/// \endcode
/// In this example directive '#pragma acc teams' has clause 'thread_limit'
/// with single expression 'n'.
class ACCThreadLimitClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief ThreadLimit number.
  Stmt *ThreadLimit = nullptr;

  /// \brief Set the ThreadLimit number.
  ///
  /// \param E ThreadLimit number.
  void setThreadLimit(Expr *E) { ThreadLimit = E; }

public:
  /// \brief Build 'thread_limit' clause.
  ///
  /// \param E Expression associated with this clause.
  /// \param HelperE Helper Expression associated with this clause.
  /// \param CaptureRegion Innermost OpenACC region where expressions in this
  /// clause must be captured.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCThreadLimitClause(Expr *E, Stmt *HelperE,
                       OpenACCDirectiveKind CaptureRegion,
                       SourceLocation StartLoc, SourceLocation LParenLoc,
                       SourceLocation EndLoc)
      : ACCClause(ACCC_thread_limit, StartLoc, EndLoc),
        ACCClauseWithPreInit(this), LParenLoc(LParenLoc), ThreadLimit(E) {
    setPreInitStmt(HelperE, CaptureRegion);
  }

  /// \brief Build an empty clause.
  ACCThreadLimitClause()
      : ACCClause(ACCC_thread_limit, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return ThreadLimit number.
  Expr *getThreadLimit() { return cast<Expr>(ThreadLimit); }

  /// \brief Return ThreadLimit number.
  Expr *getThreadLimit() const { return cast<Expr>(ThreadLimit); }

  child_range children() { return child_range(&ThreadLimit, &ThreadLimit + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_thread_limit;
  }
};

/// \brief This represents 'priority' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc task priority(n)
/// \endcode
/// In this example directive '#pragma acc teams' has clause 'priority' with
/// single expression 'n'.
class ACCPriorityClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Priority number.
  Stmt *Priority = nullptr;

  /// \brief Set the Priority number.
  ///
  /// \param E Priority number.
  void setPriority(Expr *E) { Priority = E; }

public:
  /// \brief Build 'priority' clause.
  ///
  /// \param E Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCPriorityClause(Expr *E, SourceLocation StartLoc, SourceLocation LParenLoc,
                    SourceLocation EndLoc)
      : ACCClause(ACCC_priority, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Priority(E) {}

  /// \brief Build an empty clause.
  ACCPriorityClause()
      : ACCClause(ACCC_priority, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return Priority number.
  Expr *getPriority() { return cast<Expr>(Priority); }

  /// \brief Return Priority number.
  Expr *getPriority() const { return cast<Expr>(Priority); }

  child_range children() { return child_range(&Priority, &Priority + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_priority;
  }
};

/// \brief This represents 'grainsize' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc taskloop grainsize(4)
/// \endcode
/// In this example directive '#pragma acc taskloop' has clause 'grainsize'
/// with single expression '4'.
class ACCGrainsizeClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Safe iteration space distance.
  Stmt *Grainsize = nullptr;

  /// \brief Set safelen.
  void setGrainsize(Expr *Size) { Grainsize = Size; }

public:
  /// \brief Build 'grainsize' clause.
  ///
  /// \param Size Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCGrainsizeClause(Expr *Size, SourceLocation StartLoc,
                     SourceLocation LParenLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_grainsize, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Grainsize(Size) {}

  /// \brief Build an empty clause.
  explicit ACCGrainsizeClause()
      : ACCClause(ACCC_grainsize, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return safe iteration space distance.
  Expr *getGrainsize() const { return cast_or_null<Expr>(Grainsize); }

  child_range children() { return child_range(&Grainsize, &Grainsize + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_grainsize;
  }
};

/// \brief This represents 'nogroup' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc taskloop nogroup
/// \endcode
/// In this example directive '#pragma acc taskloop' has 'nogroup' clause.
class ACCNogroupClause : public ACCClause {
public:
  /// \brief Build 'nogroup' clause.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCNogroupClause(SourceLocation StartLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_nogroup, StartLoc, EndLoc) {}

  /// \brief Build an empty clause.
  ACCNogroupClause()
      : ACCClause(ACCC_nogroup, SourceLocation(), SourceLocation()) {}

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_nogroup;
  }
};

/// \brief This represents 'num_tasks' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc taskloop num_tasks(4)
/// \endcode
/// In this example directive '#pragma acc taskloop' has clause 'num_tasks'
/// with single expression '4'.
class ACCNumTasksClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Safe iteration space distance.
  Stmt *NumTasks = nullptr;

  /// \brief Set safelen.
  void setNumTasks(Expr *Size) { NumTasks = Size; }

public:
  /// \brief Build 'num_tasks' clause.
  ///
  /// \param Size Expression associated with this clause.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  ACCNumTasksClause(Expr *Size, SourceLocation StartLoc,
                    SourceLocation LParenLoc, SourceLocation EndLoc)
      : ACCClause(ACCC_num_tasks, StartLoc, EndLoc), LParenLoc(LParenLoc),
        NumTasks(Size) {}

  /// \brief Build an empty clause.
  explicit ACCNumTasksClause()
      : ACCClause(ACCC_num_tasks, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Return safe iteration space distance.
  Expr *getNumTasks() const { return cast_or_null<Expr>(NumTasks); }

  child_range children() { return child_range(&NumTasks, &NumTasks + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_num_tasks;
  }
};

/// \brief This represents 'hint' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc critical (name) hint(6)
/// \endcode
/// In this example directive '#pragma acc critical' has name 'name' and clause
/// 'hint' with argument '6'.
class ACCHintClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Hint expression of the 'hint' clause.
  Stmt *Hint = nullptr;

  /// \brief Set hint expression.
  void setHint(Expr *H) { Hint = H; }

public:
  /// \brief Build 'hint' clause with expression \a Hint.
  ///
  /// \param Hint Hint expression.
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param EndLoc Ending location of the clause.
  ACCHintClause(Expr *Hint, SourceLocation StartLoc, SourceLocation LParenLoc,
                SourceLocation EndLoc)
      : ACCClause(ACCC_hint, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Hint(Hint) {}

  /// \brief Build an empty clause.
  ACCHintClause() : ACCClause(ACCC_hint, SourceLocation(), SourceLocation()) {}

  /// \brief Sets the location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Returns the location of '('.
  SourceLocation getLParenLoc() const { return LParenLoc; }

  /// \brief Returns number of threads.
  Expr *getHint() const { return cast_or_null<Expr>(Hint); }

  child_range children() { return child_range(&Hint, &Hint + 1); }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_hint;
  }
};

/// \brief This represents 'dist_schedule' clause in the '#pragma acc ...'
/// directive.
///
/// \code
/// #pragma acc distribute dist_schedule(static, 3)
/// \endcode
/// In this example directive '#pragma acc distribute' has 'dist_schedule'
/// clause with arguments 'static' and '3'.
class ACCDistScheduleClause : public ACCClause, public ACCClauseWithPreInit {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief A kind of the 'schedule' clause.
  OpenACCDistScheduleClauseKind Kind = ACCC_DIST_SCHEDULE_unknown;

  /// \brief Start location of the schedule kind in source code.
  SourceLocation KindLoc;

  /// \brief Location of ',' (if any).
  SourceLocation CommaLoc;

  /// \brief Chunk size.
  Expr *ChunkSize = nullptr;

  /// \brief Set schedule kind.
  ///
  /// \param K Schedule kind.
  void setDistScheduleKind(OpenACCDistScheduleClauseKind K) { Kind = K; }

  /// \brief Sets the location of '('.
  ///
  /// \param Loc Location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Set schedule kind start location.
  ///
  /// \param KLoc Schedule kind location.
  void setDistScheduleKindLoc(SourceLocation KLoc) { KindLoc = KLoc; }

  /// \brief Set location of ','.
  ///
  /// \param Loc Location of ','.
  void setCommaLoc(SourceLocation Loc) { CommaLoc = Loc; }

  /// \brief Set chunk size.
  ///
  /// \param E Chunk size.
  void setChunkSize(Expr *E) { ChunkSize = E; }

public:
  /// \brief Build 'dist_schedule' clause with schedule kind \a Kind and chunk
  /// size expression \a ChunkSize.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param KLoc Starting location of the argument.
  /// \param CommaLoc Location of ','.
  /// \param EndLoc Ending location of the clause.
  /// \param Kind DistSchedule kind.
  /// \param ChunkSize Chunk size.
  /// \param HelperChunkSize Helper chunk size for combined directives.
  ACCDistScheduleClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                        SourceLocation KLoc, SourceLocation CommaLoc,
                        SourceLocation EndLoc,
                        OpenACCDistScheduleClauseKind Kind, Expr *ChunkSize,
                        Stmt *HelperChunkSize)
      : ACCClause(ACCC_dist_schedule, StartLoc, EndLoc),
        ACCClauseWithPreInit(this), LParenLoc(LParenLoc), Kind(Kind),
        KindLoc(KLoc), CommaLoc(CommaLoc), ChunkSize(ChunkSize) {
    setPreInitStmt(HelperChunkSize);
  }

  /// \brief Build an empty clause.
  explicit ACCDistScheduleClause()
      : ACCClause(ACCC_dist_schedule, SourceLocation(), SourceLocation()),
        ACCClauseWithPreInit(this) {}

  /// \brief Get kind of the clause.
  OpenACCDistScheduleClauseKind getDistScheduleKind() const { return Kind; }

  /// \brief Get location of '('.
  SourceLocation getLParenLoc() { return LParenLoc; }

  /// \brief Get kind location.
  SourceLocation getDistScheduleKindLoc() { return KindLoc; }

  /// \brief Get location of ','.
  SourceLocation getCommaLoc() { return CommaLoc; }

  /// \brief Get chunk size.
  Expr *getChunkSize() { return ChunkSize; }

  /// \brief Get chunk size.
  const Expr *getChunkSize() const { return ChunkSize; }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(&ChunkSize),
                       reinterpret_cast<Stmt **>(&ChunkSize) + 1);
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_dist_schedule;
  }
};

/// \brief This represents 'defaultmap' clause in the '#pragma acc ...' directive.
///
/// \code
/// #pragma acc target defaultmap(tofrom: scalar)
/// \endcode
/// In this example directive '#pragma acc target' has 'defaultmap' clause of kind
/// 'scalar' with modifier 'tofrom'.
class ACCDefaultmapClause : public ACCClause {
  friend class ACCClauseReader;

  /// \brief Location of '('.
  SourceLocation LParenLoc;

  /// \brief Modifiers for 'defaultmap' clause.
  OpenACCDefaultmapClauseModifier Modifier = ACCC_DEFAULTMAP_MODIFIER_unknown;

  /// \brief Locations of modifiers.
  SourceLocation ModifierLoc;

  /// \brief A kind of the 'defaultmap' clause.
  OpenACCDefaultmapClauseKind Kind = ACCC_DEFAULTMAP_unknown;

  /// \brief Start location of the defaultmap kind in source code.
  SourceLocation KindLoc;

  /// \brief Set defaultmap kind.
  ///
  /// \param K Defaultmap kind.
  void setDefaultmapKind(OpenACCDefaultmapClauseKind K) { Kind = K; }

  /// \brief Set the defaultmap modifier.
  ///
  /// \param M Defaultmap modifier.
  void setDefaultmapModifier(OpenACCDefaultmapClauseModifier M) {
    Modifier = M;
  }

  /// \brief Set location of the defaultmap modifier.
  void setDefaultmapModifierLoc(SourceLocation Loc) {
    ModifierLoc = Loc;
  }

  /// \brief Sets the location of '('.
  ///
  /// \param Loc Location of '('.
  void setLParenLoc(SourceLocation Loc) { LParenLoc = Loc; }

  /// \brief Set defaultmap kind start location.
  ///
  /// \param KLoc Defaultmap kind location.
  void setDefaultmapKindLoc(SourceLocation KLoc) { KindLoc = KLoc; }

public:
  /// \brief Build 'defaultmap' clause with defaultmap kind \a Kind
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param LParenLoc Location of '('.
  /// \param KLoc Starting location of the argument.
  /// \param EndLoc Ending location of the clause.
  /// \param Kind Defaultmap kind.
  /// \param M The modifier applied to 'defaultmap' clause.
  /// \param MLoc Location of the modifier
  ACCDefaultmapClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                      SourceLocation MLoc, SourceLocation KLoc,
                      SourceLocation EndLoc, OpenACCDefaultmapClauseKind Kind,
                      OpenACCDefaultmapClauseModifier M)
      : ACCClause(ACCC_defaultmap, StartLoc, EndLoc), LParenLoc(LParenLoc),
        Modifier(M), ModifierLoc(MLoc), Kind(Kind), KindLoc(KLoc) {}

  /// \brief Build an empty clause.
  explicit ACCDefaultmapClause()
      : ACCClause(ACCC_defaultmap, SourceLocation(), SourceLocation()) {}

  /// \brief Get kind of the clause.
  OpenACCDefaultmapClauseKind getDefaultmapKind() const { return Kind; }

  /// \brief Get the modifier of the clause.
  OpenACCDefaultmapClauseModifier getDefaultmapModifier() const {
    return Modifier;
  }

  /// \brief Get location of '('.
  SourceLocation getLParenLoc() { return LParenLoc; }

  /// \brief Get kind location.
  SourceLocation getDefaultmapKindLoc() { return KindLoc; }

  /// \brief Get the modifier location.
  SourceLocation getDefaultmapModifierLoc() const {
    return ModifierLoc;
  }

  child_range children() {
    return child_range(child_iterator(), child_iterator());
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_defaultmap;
  }
};

/// \brief This represents clause 'to' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc target update to(a,b)
/// \endcode
/// In this example directive '#pragma acc target update' has clause 'to'
/// with the variables 'a' and 'b'.
class ACCToClause final : public ACCMappableExprListClause<ACCToClause>,
                          private llvm::TrailingObjects<
                              ACCToClause, Expr *, ValueDecl *, unsigned,
                              ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCToClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                       SourceLocation EndLoc, unsigned NumVars,
                       unsigned NumUniqueDeclarations,
                       unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_to, StartLoc, LParenLoc, EndLoc, NumVars,
                                  NumUniqueDeclarations, NumComponentLists,
                                  NumComponents) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCToClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                       unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_to, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

public:
  /// \brief Creates clause with a list of variables \a Vars.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  static ACCToClause *Create(const ASTContext &C, SourceLocation StartLoc,
                             SourceLocation LParenLoc, SourceLocation EndLoc,
                             ArrayRef<Expr *> Vars,
                             ArrayRef<ValueDecl *> Declarations,
                             MappableExprComponentListsRef ComponentLists);

  /// \brief Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCToClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                  unsigned NumUniqueDeclarations,
                                  unsigned NumComponentLists,
                                  unsigned NumComponents);

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_to;
  }
};

/// \brief This represents clause 'from' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc target update from(a,b)
/// \endcode
/// In this example directive '#pragma acc target update' has clause 'from'
/// with the variables 'a' and 'b'.
class ACCFromClause final
    : public ACCMappableExprListClause<ACCFromClause>,
      private llvm::TrailingObjects<
          ACCFromClause, Expr *, ValueDecl *, unsigned,
          ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// \brief Build clause with number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCFromClause(SourceLocation StartLoc, SourceLocation LParenLoc,
                         SourceLocation EndLoc, unsigned NumVars,
                         unsigned NumUniqueDeclarations,
                         unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_from, StartLoc, LParenLoc, EndLoc,
                                  NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents) {}

  /// \brief Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCFromClause(unsigned NumVars, unsigned NumUniqueDeclarations,
                         unsigned NumComponentLists, unsigned NumComponents)
      : ACCMappableExprListClause(
            ACCC_from, SourceLocation(), SourceLocation(), SourceLocation(),
            NumVars, NumUniqueDeclarations, NumComponentLists, NumComponents) {}

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

public:
  /// \brief Creates clause with a list of variables \a Vars.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  static ACCFromClause *Create(const ASTContext &C, SourceLocation StartLoc,
                               SourceLocation LParenLoc, SourceLocation EndLoc,
                               ArrayRef<Expr *> Vars,
                               ArrayRef<ValueDecl *> Declarations,
                               MappableExprComponentListsRef ComponentLists);

  /// \brief Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCFromClause *CreateEmpty(const ASTContext &C, unsigned NumVars,
                                    unsigned NumUniqueDeclarations,
                                    unsigned NumComponentLists,
                                    unsigned NumComponents);

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_from;
  }
};

/// This represents clause 'use_device_ptr' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc target data use_device_ptr(a,b)
/// \endcode
/// In this example directive '#pragma acc target data' has clause
/// 'use_device_ptr' with the variables 'a' and 'b'.
class ACCUseDevicePtrClause final
    : public ACCMappableExprListClause<ACCUseDevicePtrClause>,
      private llvm::TrailingObjects<
          ACCUseDevicePtrClause, Expr *, ValueDecl *, unsigned,
          ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Build clause with number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCUseDevicePtrClause(SourceLocation StartLoc,
                                 SourceLocation LParenLoc,
                                 SourceLocation EndLoc, unsigned NumVars,
                                 unsigned NumUniqueDeclarations,
                                 unsigned NumComponentLists,
                                 unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_use_device_ptr, StartLoc, LParenLoc,
                                  EndLoc, NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents) {}

  /// Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCUseDevicePtrClause(unsigned NumVars,
                                 unsigned NumUniqueDeclarations,
                                 unsigned NumComponentLists,
                                 unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_use_device_ptr, SourceLocation(),
                                  SourceLocation(), SourceLocation(), NumVars,
                                  NumUniqueDeclarations, NumComponentLists,
                                  NumComponents) {}

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return 3 * varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

  /// Sets the list of references to private copies with initializers for new
  /// private variables.
  /// \param VL List of references.
  void setPrivateCopies(ArrayRef<Expr *> VL);

  /// Gets the list of references to private copies with initializers for new
  /// private variables.
  MutableArrayRef<Expr *> getPrivateCopies() {
    return MutableArrayRef<Expr *>(varlist_end(), varlist_size());
  }
  ArrayRef<const Expr *> getPrivateCopies() const {
    return llvm::makeArrayRef(varlist_end(), varlist_size());
  }

  /// Sets the list of references to initializer variables for new private
  /// variables.
  /// \param VL List of references.
  void setInits(ArrayRef<Expr *> VL);

  /// Gets the list of references to initializer variables for new private
  /// variables.
  MutableArrayRef<Expr *> getInits() {
    return MutableArrayRef<Expr *>(getPrivateCopies().end(), varlist_size());
  }
  ArrayRef<const Expr *> getInits() const {
    return llvm::makeArrayRef(getPrivateCopies().end(), varlist_size());
  }

public:
  /// Creates clause with a list of variables \a Vars.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param PrivateVars Expressions referring to private copies.
  /// \param Inits Expressions referring to private copy initializers.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  static ACCUseDevicePtrClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, ArrayRef<Expr *> Vars,
         ArrayRef<Expr *> PrivateVars, ArrayRef<Expr *> Inits,
         ArrayRef<ValueDecl *> Declarations,
         MappableExprComponentListsRef ComponentLists);

  /// Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCUseDevicePtrClause *CreateEmpty(const ASTContext &C,
                                            unsigned NumVars,
                                            unsigned NumUniqueDeclarations,
                                            unsigned NumComponentLists,
                                            unsigned NumComponents);

  using private_copies_iterator = MutableArrayRef<Expr *>::iterator;
  using private_copies_const_iterator = ArrayRef<const Expr *>::iterator;
  using private_copies_range = llvm::iterator_range<private_copies_iterator>;
  using private_copies_const_range =
      llvm::iterator_range<private_copies_const_iterator>;

  private_copies_range private_copies() {
    return private_copies_range(getPrivateCopies().begin(),
                                getPrivateCopies().end());
  }

  private_copies_const_range private_copies() const {
    return private_copies_const_range(getPrivateCopies().begin(),
                                      getPrivateCopies().end());
  }

  using inits_iterator = MutableArrayRef<Expr *>::iterator;
  using inits_const_iterator = ArrayRef<const Expr *>::iterator;
  using inits_range = llvm::iterator_range<inits_iterator>;
  using inits_const_range = llvm::iterator_range<inits_const_iterator>;

  inits_range inits() {
    return inits_range(getInits().begin(), getInits().end());
  }

  inits_const_range inits() const {
    return inits_const_range(getInits().begin(), getInits().end());
  }

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_use_device_ptr;
  }
};

/// This represents clause 'is_device_ptr' in the '#pragma acc ...'
/// directives.
///
/// \code
/// #pragma acc target is_device_ptr(a,b)
/// \endcode
/// In this example directive '#pragma acc target' has clause
/// 'is_device_ptr' with the variables 'a' and 'b'.
class ACCIsDevicePtrClause final
    : public ACCMappableExprListClause<ACCIsDevicePtrClause>,
      private llvm::TrailingObjects<
          ACCIsDevicePtrClause, Expr *, ValueDecl *, unsigned,
          ACCClauseMappableExprCommon::MappableComponent> {
  friend class ACCClauseReader;
  friend ACCMappableExprListClause;
  friend ACCVarListClause;
  friend TrailingObjects;

  /// Build clause with number of variables \a NumVars.
  ///
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCIsDevicePtrClause(SourceLocation StartLoc,
                                SourceLocation LParenLoc, SourceLocation EndLoc,
                                unsigned NumVars,
                                unsigned NumUniqueDeclarations,
                                unsigned NumComponentLists,
                                unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_is_device_ptr, StartLoc, LParenLoc,
                                  EndLoc, NumVars, NumUniqueDeclarations,
                                  NumComponentLists, NumComponents) {}

  /// Build an empty clause.
  ///
  /// \param NumVars Number of expressions listed in this clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of component lists in this clause.
  /// \param NumComponents Total number of expression components in the clause.
  explicit ACCIsDevicePtrClause(unsigned NumVars,
                                unsigned NumUniqueDeclarations,
                                unsigned NumComponentLists,
                                unsigned NumComponents)
      : ACCMappableExprListClause(ACCC_is_device_ptr, SourceLocation(),
                                  SourceLocation(), SourceLocation(), NumVars,
                                  NumUniqueDeclarations, NumComponentLists,
                                  NumComponents) {}

  /// Define the sizes of each trailing object array except the last one. This
  /// is required for TrailingObjects to work properly.
  size_t numTrailingObjects(OverloadToken<Expr *>) const {
    return varlist_size();
  }
  size_t numTrailingObjects(OverloadToken<ValueDecl *>) const {
    return getUniqueDeclarationsNum();
  }
  size_t numTrailingObjects(OverloadToken<unsigned>) const {
    return getUniqueDeclarationsNum() + getTotalComponentListNum();
  }

public:
  /// Creates clause with a list of variables \a Vars.
  ///
  /// \param C AST context.
  /// \param StartLoc Starting location of the clause.
  /// \param EndLoc Ending location of the clause.
  /// \param Vars The original expression used in the clause.
  /// \param Declarations Declarations used in the clause.
  /// \param ComponentLists Component lists used in the clause.
  static ACCIsDevicePtrClause *
  Create(const ASTContext &C, SourceLocation StartLoc, SourceLocation LParenLoc,
         SourceLocation EndLoc, ArrayRef<Expr *> Vars,
         ArrayRef<ValueDecl *> Declarations,
         MappableExprComponentListsRef ComponentLists);

  /// Creates an empty clause with the place for \a NumVars variables.
  ///
  /// \param C AST context.
  /// \param NumVars Number of expressions listed in the clause.
  /// \param NumUniqueDeclarations Number of unique base declarations in this
  /// clause.
  /// \param NumComponentLists Number of unique base declarations in this
  /// clause.
  /// \param NumComponents Total number of expression components in the clause.
  static ACCIsDevicePtrClause *CreateEmpty(const ASTContext &C,
                                           unsigned NumVars,
                                           unsigned NumUniqueDeclarations,
                                           unsigned NumComponentLists,
                                           unsigned NumComponents);

  child_range children() {
    return child_range(reinterpret_cast<Stmt **>(varlist_begin()),
                       reinterpret_cast<Stmt **>(varlist_end()));
  }

  static bool classof(const ACCClause *T) {
    return T->getClauseKind() == ACCC_is_device_ptr;
  }
};

} // namespace clang

#endif // LLVM_CLANG_AST_OPENACCCLAUSE_H
