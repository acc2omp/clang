//=== CGOpenRuntime.h - Interface to OpenMP and OpenACC Runtimes *- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This provides a class for common ground on OpenMP and OpenACC runtime
// code generation.
//
//===----------------------------------------------------------------------===//

#include "CGValue.h"
#include "clang/AST/Type.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/ValueHandle.h"


#ifndef LLVM_CLANG_LIB_CODEGEN_CGOPENRUNTIME_H
#define LLVM_CLANG_LIB_CODEGEN_CGOPENRUNTIME_H

namespace llvm {
class Type;
class Value;
} // namespace llvm

namespace clang {
class Expr;
class VarDecl;

namespace CodeGen {
class Address;
class CodeGenFunction;
class CodeGenModule;

/// A basic class for pre|post-action for advanced codegen sequence for OpenMP
/// region.
class PrePostActionTy {
public:
  explicit PrePostActionTy() {}
  virtual void Enter(CodeGenFunction &CGF) {}
  virtual void Exit(CodeGenFunction &CGF) {}
  virtual ~PrePostActionTy() {}
};

/// Class provides a way to call simple version of codegen for OpenMP region, or
/// an advanced with possible pre|post-actions in codegen.
class RegionCodeGenTy final {
  intptr_t CodeGen;
  typedef void (*CodeGenTy)(intptr_t, CodeGenFunction &, PrePostActionTy &);
  CodeGenTy Callback;
  mutable PrePostActionTy *PrePostAction;
  RegionCodeGenTy() = delete;
  RegionCodeGenTy &operator=(const RegionCodeGenTy &) = delete;
  template <typename Callable>
  static void CallbackFn(intptr_t CodeGen, CodeGenFunction &CGF,
                         PrePostActionTy &Action) {
    return (*reinterpret_cast<Callable *>(CodeGen))(CGF, Action);
  }

public:
  template <typename Callable>
  RegionCodeGenTy(
      Callable &&CodeGen,
      typename std::enable_if<
          !std::is_same<typename std::remove_reference<Callable>::type,
                        RegionCodeGenTy>::value>::type * = nullptr)
      : CodeGen(reinterpret_cast<intptr_t>(&CodeGen)),
        Callback(CallbackFn<typename std::remove_reference<Callable>::type>),
        PrePostAction(nullptr) {}
  void setAction(PrePostActionTy &Action) const { PrePostAction = &Action; }
  void operator()(CodeGenFunction &CGF) const;
};

class ReductionCodeGen {
private:
  /// Data required for codegen of reduction clauses.
  struct ReductionData {
    /// Reference to the original shared item.
    const Expr *Ref = nullptr;
    /// Helper expression for generation of private copy.
    const Expr *Private = nullptr;
    /// Helper expression for generation reduction operation.
    const Expr *ReductionOp = nullptr;
    ReductionData(const Expr *Ref, const Expr *Private, const Expr *ReductionOp)
        : Ref(Ref), Private(Private), ReductionOp(ReductionOp) {}
  };
  /// List of reduction-based clauses.
  SmallVector<ReductionData, 4> ClausesData;

  /// List of addresses of original shared variables/expressions.
  SmallVector<std::pair<LValue, LValue>, 4> SharedAddresses;
  /// Sizes of the reduction items in chars.
  SmallVector<std::pair<llvm::Value *, llvm::Value *>, 4> Sizes;
  /// Base declarations for the reduction items.
  SmallVector<const VarDecl *, 4> BaseDecls;

  /// Emits lvalue for shared expresion.
  LValue emitSharedLValue(CodeGenFunction &CGF, const Expr *E);
  /// Emits upper bound for shared expression (if array section).
  LValue emitSharedLValueUB(CodeGenFunction &CGF, const Expr *E);
  /// Performs aggregate initialization.
  /// \param N Number of reduction item in the common list.
  /// \param PrivateAddr Address of the corresponding private item.
  /// \param SharedLVal Address of the original shared variable.
  /// \param DRD Declare reduction construct used for reduction item.
  void emitAggregateInitialization(CodeGenFunction &CGF, unsigned N,
                                   Address PrivateAddr, LValue SharedLVal,
                                   const OMPDeclareReductionDecl *DRD);

public:
  ReductionCodeGen(ArrayRef<const Expr *> Shareds,
                   ArrayRef<const Expr *> Privates,
                   ArrayRef<const Expr *> ReductionOps);
  /// Emits lvalue for a reduction item.
  /// \param N Number of the reduction item.
  void emitSharedLValue(CodeGenFunction &CGF, unsigned N);
  /// Emits the code for the variable-modified type, if required.
  /// \param N Number of the reduction item.
  void emitAggregateType(CodeGenFunction &CGF, unsigned N);
  /// Emits the code for the variable-modified type, if required.
  /// \param N Number of the reduction item.
  /// \param Size Size of the type in chars.
  void emitAggregateType(CodeGenFunction &CGF, unsigned N, llvm::Value *Size);
  /// Performs initialization of the private copy for the reduction item.
  /// \param N Number of the reduction item.
  /// \param PrivateAddr Address of the corresponding private item.
  /// \param DefaultInit Default initialization sequence that should be
  /// performed if no reduction specific initialization is found.
  /// \param SharedLVal Address of the original shared variable.
  void
  emitInitialization(CodeGenFunction &CGF, unsigned N, Address PrivateAddr,
                     LValue SharedLVal,
                     llvm::function_ref<bool(CodeGenFunction &)> DefaultInit);
  /// Returns true if the private copy requires cleanups.
  bool needCleanups(unsigned N);
  /// Emits cleanup code for the reduction item.
  /// \param N Number of the reduction item.
  /// \param PrivateAddr Address of the corresponding private item.
  void emitCleanups(CodeGenFunction &CGF, unsigned N, Address PrivateAddr);
  /// Adjusts \p PrivatedAddr for using instead of the original variable
  /// address in normal operations.
  /// \param N Number of the reduction item.
  /// \param PrivateAddr Address of the corresponding private item.
  Address adjustPrivateAddress(CodeGenFunction &CGF, unsigned N,
                               Address PrivateAddr);
  /// Returns LValue for the reduction item.
  LValue getSharedLValue(unsigned N) const { return SharedAddresses[N].first; }
  /// Returns the size of the reduction item (in chars and total number of
  /// elements in the item), or nullptr, if the size is a constant.
  std::pair<llvm::Value *, llvm::Value *> getSizes(unsigned N) const {
    return Sizes[N];
  }
  /// Returns the base declaration of the reduction item.
  const VarDecl *getBaseDecl(unsigned N) const { return BaseDecls[N]; }
  /// Returns true if the initialization of the reduction item uses initializer
  /// from declare reduction construct.
  bool usesReductionInitializer(unsigned N) const;
};

} // namespace CodeGen
} // namespace clang

#endif
