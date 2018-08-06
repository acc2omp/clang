//===- DeclOpenACC.h - Classes for representing OpenACC directives -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief This file defines OpenACC nodes for declarative directives.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_DECLOPENACC_H
#define LLVM_CLANG_AST_DECLOPENACC_H

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExternalASTSource.h"
#include "clang/AST/Type.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/TrailingObjects.h"

namespace clang {

/// \brief This represents '#pragma acc threadprivate ...' directive.
/// For example, in the following, both 'a' and 'A::b' are threadprivate:
///
/// \code
/// int a;
/// #pragma acc threadprivate(a)
/// struct A {
///   static int b;
/// #pragma acc threadprivate(b)
/// };
/// \endcode
///
//
class ACCThreadPrivateDecl final
    : public Decl,
      private llvm::TrailingObjects<ACCThreadPrivateDecl, Expr *> {
  friend class ASTDeclReader;
  friend TrailingObjects;

  unsigned NumVars;

  virtual void anchor();

  ACCThreadPrivateDecl() : Decl(static_cast<Kind>(0), EmptyShell()) {
    llvm::errs() << "\n\n\n -------------- CONSTRUCTOR ACCTHREADPRIVATEDECL ---------------\n\n\n";
  }

  ACCThreadPrivateDecl(Kind DK, DeclContext *DC, SourceLocation L) :
    Decl(DK, DC, L), NumVars(0) {
    llvm::errs() << "\n\n\n -------------- CONSTRUCTOR ACCTHREADPRIVATEDECL ---------------\n\n\n";
    }

  ArrayRef<const Expr *> getVars() const {
    return llvm::makeArrayRef(getTrailingObjects<Expr *>(), NumVars);
  }

  MutableArrayRef<Expr *> getVars() {
    return MutableArrayRef<Expr *>(getTrailingObjects<Expr *>(), NumVars);
  }

  void setVars(ArrayRef<Expr *> VL);

public:
  static ACCThreadPrivateDecl *Create(ASTContext &C, DeclContext *DC,
                                      SourceLocation L,
                                      ArrayRef<Expr *> VL);
  static ACCThreadPrivateDecl *CreateDeserialized(ASTContext &C,
                                                  unsigned ID, unsigned N);

  typedef MutableArrayRef<Expr *>::iterator varlist_iterator;
  typedef ArrayRef<const Expr *>::iterator varlist_const_iterator;
  typedef llvm::iterator_range<varlist_iterator> varlist_range;
  typedef llvm::iterator_range<varlist_const_iterator> varlist_const_range;

  unsigned varlist_size() const { return NumVars; }
  bool varlist_empty() const { return NumVars == 0; }

  varlist_range varlists() {
    return varlist_range(varlist_begin(), varlist_end());
  }
  varlist_const_range varlists() const {
    return varlist_const_range(varlist_begin(), varlist_end());
  }
  varlist_iterator varlist_begin() { return getVars().begin(); }
  varlist_iterator varlist_end() { return getVars().end(); }
  varlist_const_iterator varlist_begin() const { return getVars().begin(); }
  varlist_const_iterator varlist_end() const { return getVars().end(); }

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == ACCThreadPrivate; }
};

/// \brief This represents '#pragma acc declare reduction ...' directive.
/// For example, in the following, declared reduction 'foo' for types 'int' and
/// 'float':
///
/// \code
/// #pragma acc declare reduction (foo : int,float : omp_out += omp_in) \
///                     initializer (omp_priv = 0)
/// \endcode
///
/// Here 'omp_out += omp_in' is a combiner and 'omp_priv = 0' is an initializer.
class ACCDeclareReductionDecl final : public ValueDecl, public DeclContext {
public:
  enum InitKind {
    CallInit,   // Initialized by function call.
    DirectInit, // omp_priv(<expr>)
    CopyInit    // omp_priv = <expr>
  };

private:
  friend class ASTDeclReader;
  /// \brief Combiner for declare reduction construct.
  Expr *Combiner;
  /// \brief Initializer for declare reduction construct.
  Expr *Initializer;
  /// Kind of initializer - function call or omp_priv<init_expr> initializtion.
  InitKind InitializerKind = CallInit;

  /// \brief Reference to the previous declare reduction construct in the same
  /// scope with the same name. Required for proper templates instantiation if
  /// the declare reduction construct is declared inside compound statement.
  LazyDeclPtr PrevDeclInScope;

  virtual void anchor();

  ACCDeclareReductionDecl(Kind DK, DeclContext *DC, SourceLocation L,
                          DeclarationName Name, QualType Ty,
                          ACCDeclareReductionDecl *PrevDeclInScope)
      : ValueDecl(DK, DC, L, Name, Ty), DeclContext(DK), Combiner(nullptr),
        Initializer(nullptr), InitializerKind(CallInit),
        PrevDeclInScope(PrevDeclInScope) {}

  void setPrevDeclInScope(ACCDeclareReductionDecl *Prev) {
    PrevDeclInScope = Prev;
  }

public:
  /// \brief Create declare reduction node.
  static ACCDeclareReductionDecl *
  Create(ASTContext &C, DeclContext *DC, SourceLocation L, DeclarationName Name,
         QualType T, ACCDeclareReductionDecl *PrevDeclInScope);
  /// \brief Create deserialized declare reduction node.
  static ACCDeclareReductionDecl *CreateDeserialized(ASTContext &C,
                                                     unsigned ID);

  /// \brief Get combiner expression of the declare reduction construct.
  Expr *getCombiner() { return Combiner; }
  const Expr *getCombiner() const { return Combiner; }
  /// \brief Set combiner expression for the declare reduction construct.
  void setCombiner(Expr *E) { Combiner = E; }

  /// \brief Get initializer expression (if specified) of the declare reduction
  /// construct.
  Expr *getInitializer() { return Initializer; }
  const Expr *getInitializer() const { return Initializer; }
  /// Get initializer kind.
  InitKind getInitializerKind() const { return InitializerKind; }
  /// \brief Set initializer expression for the declare reduction construct.
  void setInitializer(Expr *E, InitKind IK) {
    Initializer = E;
    InitializerKind = IK;
  }

  /// \brief Get reference to previous declare reduction construct in the same
  /// scope with the same name.
  ACCDeclareReductionDecl *getPrevDeclInScope();
  const ACCDeclareReductionDecl *getPrevDeclInScope() const;

  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == ACCDeclareReduction; }
  static DeclContext *castToDeclContext(const ACCDeclareReductionDecl *D) {
    return static_cast<DeclContext *>(const_cast<ACCDeclareReductionDecl *>(D));
  }
  static ACCDeclareReductionDecl *castFromDeclContext(const DeclContext *DC) {
    return static_cast<ACCDeclareReductionDecl *>(
        const_cast<DeclContext *>(DC));
  }
};

/// Pseudo declaration for capturing expressions. Also is used for capturing of
/// non-static data members in non-static member functions.
///
/// Clang supports capturing of variables only, but OpenACC 4.5 allows to
/// privatize non-static members of current class in non-static member
/// functions. This pseudo-declaration allows properly handle this kind of
/// capture by wrapping captured expression into a variable-like declaration.
class ACCCapturedExprDecl final : public VarDecl {
  friend class ASTDeclReader;
  void anchor() override;

  ACCCapturedExprDecl(ASTContext &C, DeclContext *DC, IdentifierInfo *Id,
                      QualType Type, SourceLocation StartLoc)
      : VarDecl(ACCCapturedExpr, C, DC, StartLoc, StartLoc, Id, Type, nullptr,
                SC_None) {
    setImplicit();
  }

public:
  static ACCCapturedExprDecl *Create(ASTContext &C, DeclContext *DC,
                                     IdentifierInfo *Id, QualType T,
                                     SourceLocation StartLoc);

  static ACCCapturedExprDecl *CreateDeserialized(ASTContext &C, unsigned ID);

  SourceRange getSourceRange() const override LLVM_READONLY;

  // Implement isa/cast/dyncast/etc.
  static bool classof(const Decl *D) { return classofKind(D->getKind()); }
  static bool classofKind(Kind K) { return K == ACCCapturedExpr; }
};

} // end namespace clang

#endif
