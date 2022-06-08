#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/InstCombine/InstCombineWorklist.h"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace {
namespace util {
  Value *node(Instruction *I, const std::vector<size_t> &Path) {
    Value *Current = I;
    for (auto &&P : Path) {
      if (Instruction *CI = dyn_cast<Instruction>(Current)) {
        if (CI->getNumOperands() > P) {
          Current = CI->getOperand(P);
        } else {
          return nullptr;
        }
      } else {
        return nullptr;
      }
    }
    return Current;
  }
  bool check_width(std::vector<llvm::Value *> V, std::vector<size_t> W) {
    for (size_t i = 0; i < V.size(); ++i) {
      if (V[i]->getType()->getScalarSizeInBits() != W[i]) {
        return false;
      }
    }
    return true;
  }

  struct Stats {
    void hit(size_t opt) {
      Hits[opt]++;
    }
    std::map<size_t, size_t> Hits;
    void print() {
      std::vector<std::pair<size_t, size_t>> Copy(Hits.size(), std::make_pair(0, 0));
      std::copy(Hits.begin(), Hits.end(), Copy.begin());
      std::sort(Copy.begin(), Copy.end(),
                [](auto &A, auto &B) {return A.second > B.second;});
      llvm::errs() << "Hits begin:\n";
      for (auto &&P : Copy) {
        llvm::errs() << "OptID " << P.first << " matched " << P.second << " time(s).\n";
      }
      llvm::errs() << "Hits end.\n";
    }
  };
  bool nc(llvm::Value *a, llvm::Value *b) {
    if (llvm::isa<llvm::Constant>(a) || llvm::isa<llvm::Constant>(b)) return false;
    return true;
  }
}
struct SouperCombine : public FunctionPass {
  static char ID;
  SouperCombine() : FunctionPass(ID), Builder(TheContext) {
  }

  bool runOnFunction(Function &F) override {
    W.reserve(F.getInstructionCount());
    for (auto &BB : F) {
      for (auto &&I : BB) {
        W.push(&I);
      }
    }
    return run();
  }

  bool processInst(Instruction *I) {
    Builder.SetInsertPoint(I);
    if (auto V = getReplacement(I, &Builder)) {
      replace(I, V);
      return true;
    }
    return false;
  }
  void replace(Instruction *I, Value *V) {
    W.pushUsersToWorkList(*I);
    I->replaceAllUsesWith(V);
  }
  bool run() {
    bool Changed = false;
    while (auto I = W.removeOne()) {
      Changed = processInst(I) || Changed;
    }

    St.print();

    return Changed;
  }

  Value *C(size_t Width, size_t Value) {
    return ConstantInt::get(TheContext, APInt(Width, Value));
  }
  
  Value *getReplacement(llvm::Instruction *I, llvm::IRBuilder<> *B) {
    // Autogenerated transforms
#include "gen.cpp.inc"
    return nullptr;
  }
  
  llvm::Type *T(size_t W) {
    return llvm::Type::getIntNTy(TheContext, W);
  }

  InstCombineWorklist W;
  util::Stats St;
  LLVMContext TheContext;
  llvm::IRBuilder<> Builder;
};
}

char SouperCombine::ID = 0;
namespace llvm {
void initializeSouperCombinePass(llvm::PassRegistry &);
}

INITIALIZE_PASS_BEGIN(SouperCombine, "souper", "Souper super-optimizer pass",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(DemandedBitsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LazyValueInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_END(SouperCombine, "souper-combine", "Souper super-optimizer pass", false,
                    false)

static struct Register {
  Register() {
    initializeSouperCombinePass(*llvm::PassRegistry::getPassRegistry());
  }
} X;

static void registerSouperCombine(
    const llvm::PassManagerBuilder &Builder, llvm::legacy::PassManagerBase &PM) {
  PM.add(new SouperCombine);
}

static llvm::RegisterStandardPasses
RegisterSouperOptimizer(llvm::PassManagerBuilder::EP_Peephole,
                        registerSouperCombine);
