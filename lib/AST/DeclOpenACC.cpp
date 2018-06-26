//===--- DeclOpenACC.cpp - Declaration OpenACC AST Node Implementation ------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
/// \brief This file implements ACCThreadPrivateDecl, ACCCapturedExprDecl
/// classes.
///
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclBase.h"
#include "clang/AST/DeclOpenACC.h"
#include "clang/AST/Expr.h"

using namespace clang;

//===----------------------------------------------------------------------===//
// ACCThreadPrivateDecl Implementation.
//===----------------------------------------------------------------------===//

void ACCThreadPrivateDecl::anchor() { }

ACCThreadPrivateDecl *ACCThreadPrivateDecl::Create(ASTContext &C,
                                                   DeclContext *DC,
                                                   SourceLocation L,
                                                   ArrayRef<Expr *> VL) {
  llvm::outs() << "\n\n\n -------------- CREATING ACCTHREADPRIVATEDECL ---------------\n\n\n";
  ACCThreadPrivateDecl *D =
      new (C, DC, additionalSizeToAlloc<Expr *>(VL.size()))
          ACCThreadPrivateDecl(ACCThreadPrivate, DC, L);
  D->NumVars = VL.size();
  D->setVars(VL);
  return D;
}

ACCThreadPrivateDecl *ACCThreadPrivateDecl::CreateDeserialized(ASTContext &C,
                                                               unsigned ID,
                                                               unsigned N) {
  ACCThreadPrivateDecl *D = new (C, ID, additionalSizeToAlloc<Expr *>(N))
      ACCThreadPrivateDecl(ACCThreadPrivate, nullptr, SourceLocation());
  D->NumVars = N;
  return D;
}

void ACCThreadPrivateDecl::setVars(ArrayRef<Expr *> VL) {
  assert(VL.size() == NumVars &&
         "Number of variables is not the same as the preallocated buffer");
  std::uninitialized_copy(VL.begin(), VL.end(), getTrailingObjects<Expr *>());
}

//===----------------------------------------------------------------------===//
// ACCDeclareReductionDecl Implementation.
//===----------------------------------------------------------------------===//

void ACCDeclareReductionDecl::anchor() {}

ACCDeclareReductionDecl *ACCDeclareReductionDecl::Create(
    ASTContext &C, DeclContext *DC, SourceLocation L, DeclarationName Name,
    QualType T, ACCDeclareReductionDecl *PrevDeclInScope) {
  return new (C, DC) ACCDeclareReductionDecl(ACCDeclareReduction, DC, L, Name,
                                             T, PrevDeclInScope);
}

ACCDeclareReductionDecl *
ACCDeclareReductionDecl::CreateDeserialized(ASTContext &C, unsigned ID) {
  return new (C, ID) ACCDeclareReductionDecl(
      ACCDeclareReduction, /*DC=*/nullptr, SourceLocation(), DeclarationName(),
      QualType(), /*PrevDeclInScope=*/nullptr);
}

ACCDeclareReductionDecl *ACCDeclareReductionDecl::getPrevDeclInScope() {
  return cast_or_null<ACCDeclareReductionDecl>(
      PrevDeclInScope.get(getASTContext().getExternalSource()));
}
const ACCDeclareReductionDecl *
ACCDeclareReductionDecl::getPrevDeclInScope() const {
  return cast_or_null<ACCDeclareReductionDecl>(
      PrevDeclInScope.get(getASTContext().getExternalSource()));
}

//===----------------------------------------------------------------------===//
// ACCCapturedExprDecl Implementation.
//===----------------------------------------------------------------------===//

void ACCCapturedExprDecl::anchor() {}

ACCCapturedExprDecl *ACCCapturedExprDecl::Create(ASTContext &C, DeclContext *DC,
                                                 IdentifierInfo *Id, QualType T,
                                                 SourceLocation StartLoc) {
  return new (C, DC) ACCCapturedExprDecl(C, DC, Id, T, StartLoc);
}

ACCCapturedExprDecl *ACCCapturedExprDecl::CreateDeserialized(ASTContext &C,
                                                             unsigned ID) {
  return new (C, ID)
      ACCCapturedExprDecl(C, nullptr, nullptr, QualType(), SourceLocation());
}

SourceRange ACCCapturedExprDecl::getSourceRange() const {
  assert(hasInit());
  return SourceRange(getInit()->getLocStart(), getInit()->getLocEnd());
}
