#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/InitializePasses.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/Debug.h"
#define DEBUG_TYPE ""
#include "llvm/Transforms/Utils/InstructionWorklist.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/CommandLine.h"

#include <map>
#include <fstream>

using namespace llvm;
using namespace llvm::PatternMatch;

static llvm::cl::opt<std::string> ListFile("listfile",
    llvm::cl::desc("List of optimization indexes to include.\n"
                   "(default=empty-string)"),
    llvm::cl::init(""));

static llvm::cl::opt<int> Low("low",
    llvm::cl::desc("Low"),
    llvm::cl::init(-1));

static llvm::cl::opt<int> High("high",
    llvm::cl::desc("High"),
    llvm::cl::init(-1));


// TODO Match trees
// TODO Make the commutative operations work
// This is critical because commutative operations
// sometimes have the arguments inverted for canonicalization

namespace {

// Custom Creators

class IRBuilder : public llvm::IRBuilder<NoFolder> {
public:
  IRBuilder(llvm::LLVMContext &C) : llvm::IRBuilder<NoFolder>(C) {}

  llvm::Value *CreateLogB(llvm::Value *V) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      auto Result = Con->getValue().logBase2();
      return ConstantInt::get(Con->getType(), Result);
    } else {
      llvm_unreachable("Panic, has to be guarded in advance!");
    }
  }

  bool eqWD(llvm::Value *A, llvm::Value *B) {
    if (A && A->getType() && A->getType()->isIntegerTy() &&
        B && B->getType() && B->getType()->isIntegerTy()) {
      return A->getType()->getScalarSizeInBits() == B->getType()->getScalarSizeInBits();
    } else {
      return false; 
    }
  }

  // TODO Verify that these work, the mangling argument is weird
  llvm::Value *CreateFShl(llvm::Value *A, llvm::Value *B, llvm::Value *C) {
    if (!eqWD(A, B) || ~eqWD(B, C)) return nullptr;
    return CreateIntrinsic(Intrinsic::fshl, {A->getType()}, {A, B, C});
  }
  llvm::Value *CreateFShr(llvm::Value *A, llvm::Value *B, llvm::Value *C) {
    if (!eqWD(A, B) || ~eqWD(B, C)) return nullptr;
    return CreateIntrinsic(Intrinsic::fshr, {A->getType()}, {A, B, C});
  }
  llvm::Value *CreateBSwap(llvm::Value *A) {
    return CreateIntrinsic(Intrinsic::bswap, {A->getType()}, {A});
  }

  llvm::Value *CreateAShrExact(llvm::Value *A, llvm::Value *B) {
    return llvm::BinaryOperator::CreateExact(Instruction::AShr, A, B);
  }
  llvm::Value *CreateLShrExact(llvm::Value *A, llvm::Value *B) {
    return llvm::BinaryOperator::CreateExact(Instruction::LShr, A, B);
  }
  llvm::Value *CreateUDivExact(llvm::Value *A, llvm::Value *B) {
    return llvm::BinaryOperator::CreateExact(Instruction::UDiv, A, B);
  }
  llvm::Value *CreateSDivExact(llvm::Value *A, llvm::Value *B) {
    return llvm::BinaryOperator::CreateExact(Instruction::SDiv, A, B);
  }

  llvm::Value *CreateAddNW(llvm::Value *A, llvm::Value *B) {
    return llvm::IRBuilder<NoFolder>::CreateAdd(A, B, "", true, true);
  }

  llvm::Value *CreateSubNW(llvm::Value *A, llvm::Value *B) {
    return llvm::IRBuilder<NoFolder>::CreateSub(A, B, "", true, true);
  }

  llvm::Value *CreateAnd(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateAnd(A, B);
  }

  llvm::Value *CreateOr(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateOr(A, B);
  }

  llvm::Value *CreateXor(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateXor(A, B);
  }

  llvm::Value *CreateAdd(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateAdd(A, B);
  }

  llvm::Value *CreateSub(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateSub(A, B);
  }

  llvm::Value *CreateMul(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateMul(A, B);
  }

  llvm::Value *CreateShl(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateShl(A, B);
  }

  llvm::Value *CreateAShr(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateAShr(A, B);
  }

  llvm::Value *CreateLShr(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateLShr(A, B);
  }

  llvm::Value *CreateUDiv(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateUDiv(A, B);
  }

  llvm::Value *CreateSDiv(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateSDiv(A, B);
  }

  llvm::Value *CreateURem(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateURem(A, B);
  }

  llvm::Value *CreateSRem(llvm::Value *A, llvm::Value *B) {
    if (!A || !B || !eqWD(A, B)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateSRem(A, B);
  }

  llvm::Value *CreateCmp(llvm::CmpInst::Predicate Pred, llvm::Value *LHS, llvm::Value *RHS) {
    if (!LHS || !RHS || !eqWD(LHS, RHS)) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateCmp(Pred, LHS, RHS);
  }

  llvm::Value *CreateSExt(llvm::Value *A, llvm::Type *T) {
    if (!A || !A->getType() || !A->getType()->isIntegerTy() || 
         A->getType()->getScalarSizeInBits() >= T->getScalarSizeInBits()) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateSExt(A, T);
  }

  llvm::Value *CreateZExt(llvm::Value *A, llvm::Type *T) {
    if (!A || !A->getType() || !A->getType()->isIntegerTy() || 
         A->getType()->getScalarSizeInBits() >= T->getScalarSizeInBits()) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateZExt(A, T);
  }

  llvm::Value *CreateTrunc(llvm::Value *A, llvm::Type *T) {
    if (!A || !A->getType() || !A->getType()->isIntegerTy() || 
         A->getType()->getScalarSizeInBits() <= T->getScalarSizeInBits()) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateTrunc(A, T);
  }

  llvm::Value *CreateSelect(llvm::Value *A, llvm::Value *B, llvm::Value *C) {
    if (!A || !B || !C || !eqWD(B, C) || A->getType()->getScalarSizeInBits() != 1) return nullptr;
    return llvm::IRBuilder<NoFolder>::CreateSelect(A, B, C);
  }


};

// Custom Matchers

static constexpr auto NWFlag = OverflowingBinaryOperator::NoSignedWrap
    | OverflowingBinaryOperator::NoUnsignedWrap;
#define NWT(OP) OverflowingBinaryOp_match<LHS, RHS, Instruction::OP, NWFlag>
#define NWM(OP) \
template <typename LHS, typename RHS> NWT(OP) \
m_NW##OP(const LHS &L, const RHS &R) { \
  return NWT(OP)(L, R); \
}

NWM(Add)
NWM(Sub)
NWM(Mul)
NWM(Shl)

#undef NWM
#undef NWT

template <typename ...Args>
struct phi_match {
  phi_match(Args... args) : Matchers{args...} {};
  std::tuple<Args...> Matchers;

  // cpp weirdness for accessing specific tuple element in runtime
  template <class Func, class Tuple, size_t N = 0>
  void runtime_get(Func func, Tuple& tup, size_t idx) {
    if (N == idx) {
      std::invoke(func, std::get<N>(tup));
      return;
    }

    if constexpr (N + 1 < std::tuple_size_v<Tuple>) {
      return runtime_get<Func, Tuple, N + 1>(func, tup, idx);
    }
  }

  bool match_nth(size_t n, Value *V) {
    bool Ret = false;
    auto F = [&](auto M) {Ret = M.match(V);};
    runtime_get(F, Matchers, n);
    return Ret;
  }

  bool check(const Value *V) {
    if (auto Phi = dyn_cast<PHINode>(V)) {
      for (size_t i =0; i < Phi->getNumOperands(); ++i) {
        if (!match_nth(i, Phi->getOperand(i))) {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  template <typename I> bool match(I *V) {
    return check(V);
  }
};

template<typename ...Args>
phi_match<Args...> m_Phi(Args... args) {
  return phi_match<Args...>(args...);
}

template <typename LHS, typename RHS>
inline Exact_match<BinaryOp_match<LHS, RHS, Instruction::AShr>>
m_AShrExact(const LHS &L, const RHS &R) {
  return Exact_match<BinaryOp_match<LHS, RHS, Instruction::AShr>>(
    BinaryOp_match<LHS, RHS, Instruction::AShr>(L, R));
}

template <typename LHS, typename RHS>
inline Exact_match<BinaryOp_match<LHS, RHS, Instruction::LShr>>
m_LShrExact(const LHS &L, const RHS &R) {
  return Exact_match<BinaryOp_match<LHS, RHS, Instruction::LShr>>(
    BinaryOp_match<LHS, RHS, Instruction::LShr>(L, R));
}

template <typename LHS, typename RHS>
inline Exact_match<BinaryOp_match<LHS, RHS, Instruction::UDiv>>
m_UDivExact(const LHS &L, const RHS &R) {
  return Exact_match<BinaryOp_match<LHS, RHS, Instruction::UDiv>>(
    BinaryOp_match<LHS, RHS, Instruction::UDiv>(L, R));
}

template <typename LHS, typename RHS>
inline Exact_match<BinaryOp_match<LHS, RHS, Instruction::SDiv>>
m_SDivExact(const LHS &L, const RHS &R) {
  return Exact_match<BinaryOp_match<LHS, RHS, Instruction::SDiv>>(
    BinaryOp_match<LHS, RHS, Instruction::SDiv>(L, R));
}

struct bind_apint {
  APInt &VR;

  bind_apint(APInt &V) : VR(V) {}

  template <typename ITy> bool match(ITy *V) {
    if (const auto *CV = dyn_cast<ConstantInt>(V)) {
      VR = CV->getValue();
      return true;
    } else {
      return false;
    }
    return false;
  }
};

// struct width_specific_intval : public specific_intval<false> {
//   size_t Width;
//   width_specific_intval(llvm::APInt V, size_t W) : specific_intval<false>(V), Width(W) {}

//   template <typename ITy> bool match(ITy *V) {
//     if (V->getType()->getScalarSizeInBits() != Width) {
//       return false;
//     }
//     return specific_intval<false>::match(V);
//   }
// };

// inline width_specific_intval m_SpecificInt(size_t W, uint64_t V) {
//   return width_specific_intval(APInt(64, V), W);
// }

// inline width_specific_intval m_SpecificInt(size_t W, std::string S) {
//   return width_specific_intval(APInt(W, S, 10), W);
// }

struct specific_ext_intval {
  llvm::APInt Val;

  specific_ext_intval(std::string S, size_t W) : Val(llvm::APInt(W, S, 10)) {}

  template <typename ITy> bool match(ITy *V) {
    const auto *CI = dyn_cast<ConstantInt>(V);
    if (!CI && V->getType()->isVectorTy())
      if (const auto *C = dyn_cast<Constant>(V))
        CI = dyn_cast_or_null<ConstantInt>(C->getSplatValue(true));

    if (!CI)
      return false;

    auto TargetVal = CI->getValue();
    auto TargetWidth = TargetVal.getBitWidth();

    return llvm::APInt::isSameValue(TargetVal, Val.zextOrTrunc(TargetWidth)) ||
           llvm::APInt::isSameValue(TargetVal, Val.sextOrTrunc(TargetWidth));

  }
};

inline specific_ext_intval m_ExtInt(std::string S, size_t W) {
  return specific_ext_intval(S, W);
}

struct constant_matcher {
  llvm::Value** Captured;
  constant_matcher(llvm::Value** C) : Captured(C) {}
  template <typename OpTy> bool match(OpTy *V) {
    if (!V) {
      // FIXME : Should never happen.
      return false;
    }
    if (isa<ConstantInt>(V)) {
      *Captured = dyn_cast<ConstantInt>(V);
      return *Captured != nullptr;
    }
    return false;
  }
};

inline constant_matcher m_Constant(Value **V) {
  return constant_matcher(V);
}

// Tested, matches APInts
inline bind_apint m_APInt(APInt &V) { return bind_apint(V); }

// TODO: Match (arbitrarily) constrained APInts


template <typename Op_t, unsigned Opcode> struct CastClass_match_width {
  size_t Width;
  Op_t Op;

  CastClass_match_width(size_t W, const Op_t &OpMatch) : Width(W), Op(OpMatch) {}

  template <typename OpTy> bool match(OpTy *V) {
    if (V->getType()->getScalarSizeInBits() != Width) {
      return false;
    }
    if (auto *O = dyn_cast<Operator>(V))
      return O->getOpcode() == Opcode && Op.match(O->getOperand(0));
    return false;
  }
};

template<typename Matcher>
struct Capture {
  Value **Captured;
  Matcher M;

  template<typename ...CArgs>
  explicit Capture(Value **V, CArgs ...C) : Captured(V), M(C...) {}

  template <typename OpTy> bool match(OpTy *V) {
    if (!V || !Captured) {
      // FIXME: Should never happen
      return false;
    }
    if (M.match(V)) {
      *Captured = dyn_cast<Value>(V);
      if (!*Captured) {
        llvm::errs() << "Capture failed.\n";
        return false;
      }
      return true;
    } else {
      *Captured = nullptr;
      return false;
    }
  }
};

template<typename Matcher>
Capture<Matcher> Cap(Value **V, Matcher &&M) {
  return Capture<Matcher>(V, M);
}

// Equivalent to the Cap function
template <typename Matcher>
Capture<Matcher> operator<<=(Value **V, Matcher &&M) {
  return Capture<Matcher>(V, M);
}

// template <typename OpTy>
// inline CastClass_match_width<OpTy, Instruction::ZExt> m_ZExt(size_t W, const OpTy &Op) {
//   return CastClass_match_width<OpTy, Instruction::ZExt>(W, Op);
// }
//
// template <typename OpTy>
// inline CastClass_match_width<OpTy, Instruction::SExt> m_SExt(size_t W, const OpTy &Op) {
//   return CastClass_match_width<OpTy, Instruction::SExt>(W, Op);
// }
//
// template <typename OpTy>
// inline CastClass_match_width<OpTy, Instruction::Trunc> m_Trunc(size_t W, const OpTy &Op) {
//   return CastClass_match_width<OpTy, Instruction::Trunc>(W, Op);
// }

void m(llvm::APInt &A, llvm::APInt &B) {
  auto WA = A.getBitWidth(), WB = B.getBitWidth();
  if (WA == WB) {
    return;
  }
  if (WA < WB) {
    if (A.isSignBitSet()) {
      A = A.sext(WB);
    } else {
      A = A.zext(WB);
    }
  }

  if (WA > WB) {
    if (B.isSignBitSet()) {
      B = B.sext(WA);
    } else {
      B = B.zext(WA);
    }
  }

}

llvm::APInt flip(llvm::APInt A) {
  A.flipAllBits();
  return A;
}

llvm::APInt xor_(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A ^ B;
}

llvm::APInt and_(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A & B;
}

llvm::APInt or_(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A | B;
}

llvm::APInt add(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A + B;
}

llvm::APInt sub(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A - B;
}

llvm::APInt mul(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A * B;
}

llvm::APInt shl(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.shl(B);
}

llvm::APInt urem(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.urem(B);
}

llvm::APInt srem(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.srem(B);
}

llvm::APInt udiv(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.udiv(B);
}

llvm::APInt sdiv(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.sdiv(B);
}

bool slt(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.slt(B);
}

bool sle(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.sle(B);
}

bool ult(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.ult(B);
}

bool ule(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.ule(B);
}

bool eq(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.eq(B);
}

bool ne(llvm::APInt A, llvm::APInt B) {
  m(A, B);
  return A.ne(B);
}



namespace util {
  bool dc(llvm::DominatorTree *DT, llvm::Instruction *I, llvm::Value *V) {
    if (!I || !V) {
      return false;
    }
    if (auto Def = dyn_cast<Instruction>(V)) {
      if (I->getParent() == Def->getParent()) {
        return true;
      }
      return DT->dominates(Def, I->getParent());
    }
    return true;
  }

  bool check_width(llvm::Value *V, size_t W) {
    if (V && V->getType() && V->getType()->isIntegerTy()) {
      return V->getType()->getScalarSizeInBits() == W;
    } else {
      return false;
    }
  }

  bool check_width(llvm::Value *V, Instruction *I) {
    if (V && V->getType() && V->getType()->isIntegerTy() &&
        I && I->getType() && I->getType()->isIntegerTy()) {
      return V->getType()->getScalarSizeInBits() == I->getType()->getScalarSizeInBits();
    } else {
      return false;
    }
  }

  template<typename Out, typename FT, typename ...Args>
  bool check_related(Out Result, FT F, Args... args) {
    return Result == F(args...);
  }

  bool pow2(llvm::Value *V) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      if (Con->getValue().isPowerOf2()) {
        return true;
      }
    }
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      return llvm::isKnownToBeAPowerOfTwo(V, DL);
    }
    return false;
  }

  bool KnownBitImplies(llvm::APInt Big, llvm::APInt Small) {

    if (Big.getBitWidth() != Small.getBitWidth()) {
      return false;
    }

//    auto P = [](llvm::APInt A, auto S) {
//      llvm::SmallVector<char> Foo;
//      A.toString(Foo, 2, false);
//      llvm::errs() << "\n" <<  Foo << " <--" << S << "\n";
//    };
//
//    auto Val = (~Big | Small);
//
//    P(Big, "BIG");
//    P(Small, "SMALL");
//    P(~Big, "FLIP");
//
//    P(Small, "OR");
//    P(~Big | Small, "RES");

    return (~Big | Small).isAllOnes();
  }

  bool k0(llvm::Value *V, std::string Val, size_t ExpectedWidth) {
    if (!V || !V->getType() || !V->getType()->isIntegerTy() ) {
      return false;
    }
    auto W = V->getType()->getIntegerBitWidth();

    if (W != ExpectedWidth) {
      return false;
    }

    llvm::APInt Value(W, Val, 2);
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      auto X = Con->getUniqueInteger();
      return KnownBitImplies(Value, ~X);
    }
    auto Analyzed = llvm::KnownBits(W);
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      computeKnownBits(V, Analyzed, DL, 4);

      // llvm::SmallVector<char> Result;
      // Analyzed.Zero.toString(Result, 2, false);

      auto b = KnownBitImplies(Value, Analyzed.Zero);
//      llvm::errs() << "HERE: " << Result << ' ' << Val
//        << ' ' << b << "\n\n";
      return b;
    }
    return false;
  }

  bool k1(llvm::Value *V, std::string Val, size_t ExpectedWidth) {
    if (!V || !V->getType() || !V->getType()->isIntegerTy()) {
      return false;
    }
    auto W = V->getType()->getIntegerBitWidth();

    if (ExpectedWidth != W) {
      return false;
    }

    llvm::APInt Value(W, Val, 2);
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      auto X = Con->getUniqueInteger();
      return KnownBitImplies(Value, X);
    }
    auto Analyzed = llvm::KnownBits(W);
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      computeKnownBits(V, Analyzed, DL, 4);
      return KnownBitImplies(Value, Analyzed.One);
    }
    return false;
  }

  bool cr(llvm::Value *V, std::string L, std::string H) {

    if (!V || !V->getType() || !V->getType()->isIntegerTy()) {
      return false;
    }
    auto W = V->getType()->getIntegerBitWidth();

    if (((L.length()-1)*64)/22 > W || ((H.length()-1)*64)/22 > W) {
      return false;
      // FIXME: should never happen
    }

    llvm::ConstantRange R(llvm::APInt(W, L, 10), llvm::APInt(W, H, 10));
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      return R.contains(Con->getUniqueInteger());
    }
    auto CR = computeConstantRange(V, true);
    return R.contains(CR);
  }

  bool vdb(llvm::DemandedBits *DB, llvm::Instruction *I, std::string DBUnderApprox, size_t ExpectedWidth) {

    if (I->getType()->getIntegerBitWidth() != ExpectedWidth) {
      return false;
    }

    llvm::APInt V = llvm::APInt(I->getType()->getIntegerBitWidth(), DBUnderApprox, 2);
    auto ComputedDB = DB->getDemandedBits(I);

//    llvm::errs() << DBUnderApprox << ' ' << llvm::toString(ComputedDB, 2, false) << ' '
//                 << (V | ~ComputedDB).isAllOnes() << "\n";

    // 0 in DBUnderApprox implies 0 in ComputedDB
    return (V | ~ComputedDB).isAllOnes();
  }

  bool symk0bind(llvm::Value *V, llvm::Value *&Bind, IRBuilder *B) {
    if (!V || !V->getType() || !V->getType()->isIntegerTy() ) {
      return false;
    }

    auto W = V->getType()->getIntegerBitWidth();

    auto Analyzed = llvm::KnownBits(W);
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      computeKnownBits(V, Analyzed, DL, 4);
      if (Analyzed.Zero == 0) {
        return false;
      }
      Bind = B->getInt(Analyzed.Zero);
      return true;
    }

    return false;
  }

  bool symk1bind(llvm::Value *V, llvm::Value *&Bind, IRBuilder *B) {
    if (!V || !V->getType() || !V->getType()->isIntegerTy() ) {
      return false;
    }

    auto W = V->getType()->getIntegerBitWidth();

    auto Analyzed = llvm::KnownBits(W);
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      computeKnownBits(V, Analyzed, DL, 4);
      if (Analyzed.One == 0) {
        return false;
      }
      Bind = B->getInt(Analyzed.One);
      return true;
    }

    return false;
  }

  bool symk0test(llvm::Value *Bound, llvm::Value *OtherSymConst) {
    llvm::Constant *BoundC = llvm::dyn_cast<llvm::Constant>(Bound);
    llvm::Constant *OtherC = llvm::dyn_cast<llvm::Constant>(OtherSymConst);

    if (!BoundC || !OtherC) {
      return false;
    }

    // Width sanity check
    if (BoundC->getType()->getIntegerBitWidth() != OtherC->getType()->getIntegerBitWidth()) {
      return false;
    }

    return KnownBitImplies(OtherC->getUniqueInteger(), ~BoundC->getUniqueInteger());
  }

  bool symk1test(llvm::Value *Bound, llvm::Value *OtherSymConst) {
    llvm::Constant *BoundC = llvm::dyn_cast<llvm::Constant>(Bound);
    llvm::Constant *OtherC = llvm::dyn_cast<llvm::Constant>(OtherSymConst);

    if (!BoundC || !OtherC) {
      return false;
    }

    // Width sanity check
    if (BoundC->getType()->getIntegerBitWidth() != OtherC->getType()->getIntegerBitWidth()) {
      return false;
    }

    // llvm::errs() << "SymK1Test: " << llvm::toString(OtherC->getUniqueInteger(), 2, false) << ' '
    //              << llvm::toString(BoundC->getUniqueInteger(), 2, false) << "\n";

    // llvm::errs() << "Result: " << KnownBitImplies(OtherC->getUniqueInteger(), BoundC->getUniqueInteger()) << "\n";

    return KnownBitImplies(OtherC->getUniqueInteger(), BoundC->getUniqueInteger());
  }

  bool symdb(llvm::DemandedBits *DB, llvm::Instruction *I, llvm::Value *&V, IRBuilder *B) {
    auto ComputedDB = DB->getDemandedBits(I);
    // Are there other non trivial failure modes?
    if (ComputedDB == 0) {
      return false;
    }
    V = B->getInt(ComputedDB);
// //     llvm::errs() << "SymDB: " << llvm::toString(ComputedDB, 2, false) << "\n";
    return true;
  }

  bool nz(llvm::Value *V) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      return !Con->getValue().isZero();
    }

    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      return llvm::isKnownNonZero(V, DL);
    }
    return false;
  }

  bool nsb(llvm::Value *V, size_t n) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      return Con->getValue().getNumSignBits() > n;
    }
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      return llvm::ComputeNumSignBits(V, DL) > n;
    }
    return false;
  }

  bool nn(llvm::Value *V) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      return Con->getValue().isNonNegative();
    }
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      return llvm::isKnownNonNegative(V, DL);
    }
    return false;
  }

  bool neg(llvm::Value *V) {
    if (ConstantInt *Con = llvm::dyn_cast<ConstantInt>(V)) {
      return Con->getValue().isNegative();
    }
    if (Instruction *I = llvm::dyn_cast<Instruction>(V)) {
      DataLayout DL(I->getParent()->getParent()->getParent());
      return llvm::isKnownNegative(V, DL);
    }
    return false;
  }

  bool filter(const std::set<size_t> &F, size_t id) {
    if (Low != -1 && High != -1) {
      llvm::errs() << Low << " " << id << " " << High << " " << (Low <= id && id < High) << "\n";
      return Low <= id && id < High;
    }
    if (F.empty()) return true;
    return F.find(id) != F.end();
//    return true;
  }

  struct Stats {
    void hit(size_t opt, int cost) {
      Hits[opt]++;
      Cost[opt] = cost;
    }
//    void dcmiss(size_t opt) {
//      DCMiss[opt]++;
//    }
    std::map<size_t, size_t> Hits;
    std::map<size_t, int64_t> Cost;
//    std::map<size_t, size_t> DCMiss;
    void print() {
      std::vector<std::pair<size_t, size_t>> Copy(Hits.size(), std::make_pair(0, 0));
      std::copy(Hits.begin(), Hits.end(), Copy.begin());
      std::sort(Copy.begin(), Copy.end(),
                [](auto &A, auto &B) {return A.second > B.second;});
      llvm::errs() << "Hits begin:\n";
      size_t sum = 0;
      for (auto &&P : Copy) {
        sum += P.second;
        int64_t cost;
        if (Cost.find(P.first) == Cost.end()) {
          cost = 1;
        } else {
          cost = Cost[P.first];
        }
        llvm::errs() << "OptID " << P.first << " matched " << P.second << " time(s). Cost " << int(P.second) * cost << "\n";
      }
      llvm::errs() << "Hits end. Total = " << sum << ".\n";
    }
  };
  bool nc(llvm::Value *a, llvm::Value *b) {
    if (llvm::isa<llvm::Constant>(a) || llvm::isa<llvm::Constant>(b)) return false;
    return true;
  }

  llvm::APInt V(llvm::Value *V) {
    if (!V || !isa<ConstantInt>(V)) {
      // FIXME This should ideally never happen, please fix
      return llvm::APInt(1, 0);
    }
    return llvm::dyn_cast<ConstantInt>(V)->getValue();
  }
  llvm::APInt V(size_t Width, size_t Val) {
    return llvm::APInt(Width, Val);
  }
  llvm::APInt V(size_t Width, std::string Val) {
    return llvm::APInt(Width, Val, 2);
  }
  llvm::APInt V(llvm::Value *Ctx, std::string Val) {
    return llvm::APInt(Ctx->getType()->getIntegerBitWidth(), Val, 2);
  }

  llvm::APInt W(llvm::Value *Ctx) {
    if (!Ctx) {
      // FIXME Should never happen.
      return llvm::APInt(32, 128);
    }
    return llvm::APInt(Ctx->getType()->getIntegerBitWidth(), Ctx->getType()->getIntegerBitWidth());
  }
  llvm::APInt W(llvm::Value *Ctx, size_t WidthOfWidth) {
    if (!Ctx) {
      // FIXME Should never happen.
      return llvm::APInt(WidthOfWidth, 128);
    }
    return llvm::APInt(WidthOfWidth, Ctx->getType()->getIntegerBitWidth());
  }
}

bool operator < (int x, const llvm::APInt &B) {
  return llvm::APInt(B.getBitWidth(), x).ult(B);
}

llvm::APInt shl(int A, llvm::APInt B) {
  return llvm::APInt(B.getBitWidth(), A).shl(B);
}

struct SouperCombinePass : public PassInfoMixin<SouperCombinePass> {
  static char ID;
  SouperCombinePass() {
    if (ListFile != "") {
      std::ifstream in(ListFile);
      size_t num;
      while (in >> num) {
        F.insert(num);
      }
    }
    W = std::make_shared<InstructionWorklist>();
  }
  ~SouperCombinePass() {
    St.print();
  }
/*
  virtual void getAnalysisUsage(AnalysisUsage &Info) const override {
   Info.addRequired<LoopInfoWrapperPass>();
    Info.addRequired<DominatorTreeWrapperPass>();
    Info.addRequired<DemandedBitsWrapperPass>();
    Info.addRequired<LazyValueInfoWrapperPass>();
   Info.addRequired<ScalarEvolutionWrapperPass>();
   Info.addRequired<TargetLibraryInfoWrapperPass>();
  }
*/

  bool runOnFunction(Function &F, FunctionAnalysisManager &FAM) {
//     llvm::errs() << "SouperCombine: " << F.getName() << "\n";
    AssumptionCache AC(F);

//     DT = new DominatorTree(F);
//     DB = new DemandedBits(F, AC, *DT);
////    LVI =
//    auto DL = new DataLayout(F.getParent());
//    auto TLI = new TargetLibraryInfo();
//    new LazyValueInfo

//     auto &LI = FAM.getResult<llvm::LoopAnalysis>(F);
    DT = &FAM.getResult<DominatorTreeAnalysis>(F);
    DB = &FAM.getResult<DemandedBitsAnalysis>(F);
//     auto &LVI = FAM.getResult<LazyValueAnalysis>(F);
//     auto &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);
//     auto &TLI = FAM.getResult<TargetLibraryAnalysis>(F);

    W->reserve(F.getInstructionCount());
    for (auto &BB : F) {
      for (auto &&I : BB) {
        if (I.getNumOperands() &&
            !isa<StoreInst>(&I) &&
            !isa<LoadInst>(&I) &&
            !isa<GetElementPtrInst>(&I) &&
            !isa<CallInst>(&I) &&
            I.getType()->isIntegerTy()) {
          W->push(&I);
        }
      }
    }
    IRBuilder Builder(F.getContext());
    // llvm::errs() << "Before:\n" << F;
    auto r = runThroughWorklist(Builder);
    // llvm::errs() << "After:\n" << F;
//    delete DB;
//    delete DT;
    return r;
  }

  bool processInst(Instruction *I, IRBuilder &Builder) {
    Builder.SetInsertPoint(I);
//    llvm::errs() << "HERE0\n";
    if (auto V = getReplacement(I, &Builder)) {
//      llvm::errs() << "HERE1\n";
      replace(I, V, Builder);
//      llvm::errs() << "BAR\n";
      return true;
    }
//    llvm::errs() << "HERE2\n";
    return false;
  }
  void replace(Instruction *I, Value *V, IRBuilder &Builder) {
    W->pushUsersToWorkList(*I);
    I->replaceAllUsesWith(V);
  }
  bool runThroughWorklist(IRBuilder &Builder) {
    bool Changed = false;
    while (auto I = W->removeOne()) {
//      llvm::errs() << "FOO\n";
//      I->print(llvm::errs());
      Changed = processInst(I, Builder) || Changed;
    }
    return Changed;
  }

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {

//     if (Verify && verifyFunction(F))
//       llvm::report_fatal_error(("function " + F.getName() + " broken before Souper").str().c_str());
//
    // TODO ENABLE Verification
    //bool res;
    //do {
      //int n = 2;
      runOnFunction(F, FAM);
//       if (res && verifyFunction(F))
//         llvm::report_fatal_error("function broken after Souper changed it");
    //} while (res && --n);

    return PreservedAnalyses::none();
  }


  Value *getReplacement(llvm::Instruction *I, IRBuilder *B) {
//    if (!I->hasOneUse()) {
//      return nullptr;
//    }
//    llvm::errs() << "\nHERE REPL\n";
    // Interestingly commenting out ^this block
    // slightly improves results.
    // Implying this situation can be improved further

    // Autogenerated transforms
    #include "gen.cpp.inc"

    return nullptr;
  }

  struct SymConst {
    SymConst(size_t Width, size_t Value, IRBuilder *B) : Width(Width), Value(Value), B(B) {}

    size_t Width;
    size_t Value; // TODO: APInt
    IRBuilder *B;

    llvm::Value *operator()() {
      return B->getIntN(Width, Value);
    }

    llvm::Value *operator()(llvm::Value *Ctx) {
      return B->getIntN(Ctx->getType()->getIntegerBitWidth(), Value);
    }
  };

  SymConst C(size_t Width, size_t Value, IRBuilder *B) {
    return SymConst(Width, Value, B);
  }

  // Value *C(size_t Width, size_t Value, IRBuilder *B) {
  //   return B->getIntN(Width, Value);
  // }


  Value *C(llvm::APInt Value, IRBuilder *B) {
    return ConstantInt::get(B->getIntNTy(Value.getBitWidth()), Value);
//    return B->getIntN(Value.getBitWidth(), Value.getLimitedValue());
  }

  Type *T(size_t W, IRBuilder *B) {
    return B->getIntNTy(W);
  }

  Type *T(llvm::Value *V) {
    return V->getType();
  }

  std::shared_ptr<InstructionWorklist> W;
  util::Stats St;
  DominatorTree *DT;
  DemandedBits *DB;
  LazyValueInfo *LVI;
  std::set<size_t> F;
};
}

namespace llvm {
void initializeSouperCombinePass(llvm::PassRegistry &);
}

char SouperCombinePass::ID = 0;

bool pipelineParsingCallback(StringRef Name, FunctionPassManager &FPM,
                             ArrayRef<PassBuilder::PipelineElement>) {
  if (Name == "souper-combine") {
    FPM.addPass(SouperCombinePass());
    return true;
  } else {
    return false;
  }
}

void passBuilderCallback(PassBuilder &PB) {
  PB.registerPipelineParsingCallback(pipelineParsingCallback);
  PB.registerPeepholeEPCallback(
        [](llvm::FunctionPassManager &FPM, llvm::OptimizationLevel Level) {
        FPM.addPass(SouperCombinePass());
      });
}

PassPluginLibraryInfo getSouperCombinePassPluginInfo() {
  llvm::PassPluginLibraryInfo Res;
  Res.APIVersion = LLVM_PLUGIN_API_VERSION;
  Res.PluginName = "souper-combine";
  Res.PluginVersion = LLVM_VERSION_STRING;
  Res.RegisterPassBuilderCallbacks = passBuilderCallback;
  return Res;
}

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getSouperCombinePassPluginInfo();
}
