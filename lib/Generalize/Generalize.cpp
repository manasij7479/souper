#include "souper/Generalize/Generalize.h"

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/CommandLine.h"

#include "souper/Infer/AliveDriver.h"
#include "souper/Infer/Preconditions.h"
#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/ConstantSynthesis.h"
#include "souper/Infer/Pruning.h"
#include "souper/Infer/SynthUtils.h"
#include "souper/Inst/InstGraph.h"
#include "souper/Parser/Parser.h"
#include "souper/Generalize/Reducer.h"
// #include "souper/Tool/GetSolver.h"
#include <cstdlib>
#include <sstream>
#include <optional>

extern unsigned DebugLevel;

static llvm::cl::opt<bool> ReduceKBIFY("reduce-kbify",
    llvm::cl::desc("Try to reduce the number of instructions by introducing known bits constraints."
                   "(default=false)"),
    llvm::cl::init(true));

static llvm::cl::opt<bool> FindConstantRelations("relational",
    llvm::cl::desc("Find constant relations."
                   "(default=true)"),
    llvm::cl::init(true));

static llvm::cl::opt<size_t> SymbolizeNumInsts("symbolize-num-insts",
    llvm::cl::desc("Number of instructions to synthesize"
                   "(default=1)"),
    llvm::cl::init(1));

static llvm::cl::opt<bool> SymbolizeConstSynthesis("symbolize-constant-synthesis",
    llvm::cl::desc("Allow concrete constants in the generated code."),
    llvm::cl::init(false));

static llvm::cl::opt<bool> FixIt("fixit",
    llvm::cl::desc("Given an invalid optimization, generate a valid one."
                   "(default=false)"),
    llvm::cl::init(false));

using namespace llvm;

static cl::opt<size_t> NumResults("generalization-num-results",
    cl::desc("Number of Generalization Results"),
    cl::init(1));

static cl::opt<bool> JustReduce("just-reduce",
    cl::desc("JustReduce"),
    cl::init(false));

static cl::opt<bool> Basic("basic",
    cl::desc("Run all fast techniques."),
    cl::init(true));

static cl::opt<bool> OnlyWidth("only-width",
    cl::desc("Only infer width checks, no synthesis."),
    cl::init(false));

static cl::opt<bool> NoWidth("no-width",
    cl::desc("No width independence checks."),
    cl::init(false));

static cl::opt<bool> SymbolicDF("symbolic-df",
    cl::desc("Generalize with symbolic dataflow facts."),
    cl::init(true));

static cl::opt<bool> IgnoreCost("generalize-ignore-cost",
    cl::desc("Ignore cost, generalize patterns that are not cheaper."),
    cl::init(false));

namespace souper {

// This can probably be done more efficiently, but likely not the bottleneck anywhere
std::vector<std::vector<int>> GetCombinations(std::vector<int> Counts) {
  if (Counts.size() == 1) {
    std::vector<std::vector<int>> Result;
    for (int i = 0; i < Counts[0]; ++i) {
      Result.push_back({i});
    }
    return Result;
  }

  auto Last = Counts.back();
  Counts.pop_back();
  auto Partial = GetCombinations(Counts);

  std::vector<std::vector<int>> Result;
  for (int i = 0; i < Last; ++i) {
    for (auto Copy : Partial) {
      Copy.push_back(i);
      Result.push_back(Copy);
    }
  }
  return Result;
}

template <typename C, typename F>
bool All(const C &c, F f) {
  for (auto &&m : c) {
    if (!f(m)) {
      return false;
    }
  }
  return true;
}

size_t InferWidth(Inst::Kind K, const std::vector<Inst *> &Ops) {
  switch (K) {
    case Inst::KnownOnesP:
    case Inst::KnownZerosP:
    case Inst::Eq:
    case Inst::Ne:
    case Inst::Slt:
    case Inst::Sle:
    case Inst::Ult:
    case Inst::Ule: return 1;
    case Inst::Select: return Ops[1]->Width;
    default: return Ops[0]->Width;
  }
}


using ConstMapT = std::vector<std::pair<Inst *, llvm::APInt>>;
std::pair<ConstMapT, ParsedReplacement>
AugmentForSymKBDB(ParsedReplacement Original, InstContext &IC) {
  auto Input = Clone(Original, IC);
  std::vector<std::pair<Inst *, llvm::APInt>> ConstMap;
  if (Input.Mapping.LHS->DemandedBits.getBitWidth() == Input.Mapping.LHS->Width &&
    !Input.Mapping.LHS->DemandedBits.isAllOnesValue()) {
    auto DB = Input.Mapping.LHS->DemandedBits;
    auto SymDFVar = IC.createVar(DB.getBitWidth(), "symDF_DB");
    // SymDFVar->Name = "symDF_DB";

    SymDFVar->KnownOnes = llvm::APInt(DB.getBitWidth(), 0);
    SymDFVar->KnownZeros = llvm::APInt(DB.getBitWidth(), 0);
    // SymDFVar->Val = DB;

    Input.Mapping.LHS->DemandedBits.setAllBits();
    Input.Mapping.RHS->DemandedBits.setAllBits();

    auto W = Input.Mapping.LHS->Width;

    Input.Mapping.LHS = IC.getInst(Inst::DemandedMask, W, {Input.Mapping.LHS, SymDFVar});
    Input.Mapping.RHS = IC.getInst(Inst::DemandedMask, W, {Input.Mapping.RHS, SymDFVar});

    ConstMap.push_back({SymDFVar, DB});
  }

  std::vector<Inst *> Inputs;
  findVars(Input.Mapping.LHS, Inputs);

  for (auto &&I : Inputs) {
    auto Width = I->Width;
    if (!I->Range.isFullSet() && !I->Range.isEmptySet() && !I->Range.isSingleElement()) {
      Inst *LO = IC.createVar(Width, "symDF_LO");
      Inst *HI = IC.createVar(Width, "symDF_HI");

      // When signed?

      // larger than LO
      Inst *LargerThanEqLO = IC.getInst(Inst::Ule, 1, {LO, I});
      Input.PCs.push_back({LargerThanEqLO, IC.getConst(llvm::APInt(1, 1))});
      ConstMap.push_back({LO, I->Range.getLower()});

      // smaller than HI
      Inst *SmallerThanHI = IC.getInst(Inst::Ult, 1, {I, HI});
      Input.PCs.push_back({SmallerThanHI, IC.getConst(llvm::APInt(1, 1))});
      ConstMap.push_back({HI, I->Range.getUpper()});

      I->Range = llvm::ConstantRange::getFull(Width);
    }

    if (I->KnownZeros.getBitWidth() == I->Width &&
        I->KnownOnes.getBitWidth() == I->Width &&
        !(I->KnownZeros == 0 && I->KnownOnes == 0)) {
      if (I->KnownZeros != 0) {
        Inst *Zeros = IC.createVar(Width, "symDF_K0");

        // Inst *AllOnes = IC.getConst(llvm::APInt::getAllOnesValue(Width));
        // Inst *NotZeros = IC.getInst(Inst::Xor, Width,
        //                         {Zeros, AllOnes});
        // Inst *VarNotZero = IC.getInst(Inst::Or, Width, {I, NotZeros});
        // Inst *ZeroBits = IC.getInst(Inst::Eq, 1, {VarNotZero, NotZeros});
        Inst *ZeroBits = IC.getInst(Inst::KnownZerosP, 1, {I, Zeros});
        Input.PCs.push_back({ZeroBits, IC.getConst(llvm::APInt(1, 1))});
        ConstMap.push_back({Zeros, I->KnownZeros});
        I->KnownZeros = llvm::APInt(I->Width, 0);
      }

      if (I->KnownOnes != 0) {
        Inst *Ones = IC.createVar(Width, "symDF_K1");
        // Inst *VarAndOnes = IC.getInst(Inst::And, Width, {I, Ones});
        // Inst *OneBits = IC.getInst(Inst::Eq, 1, {VarAndOnes, Ones});
        Inst *OneBits = IC.getInst(Inst::KnownOnesP, 1, {I, Ones});
        Input.PCs.push_back({OneBits, IC.getConst(llvm::APInt(1, 1))});
        ConstMap.push_back({Ones, I->KnownOnes});
        I->KnownOnes = llvm::APInt(I->Width, 0);
      }
    }
  }

  return {ConstMap, Input};
}

bool typeCheck(Inst *I) {
  if (I->Ops.size() == 2) {
    if (I->Ops[0]->Width != I->Ops[1]->Width) {
      if (DebugLevel > 4) llvm::errs() << "Operands must have the same width\n";
      return false;
    }
  }
  if (I->K == Inst::Select) {
    if (I->Ops[0]->Width != 1) {
      if (DebugLevel > 4) llvm::errs() << "Select condition must be 1 bit wide\n";
      return false;
    }
    if (I->Ops[1]->Width != I->Ops[2]->Width) {
      if (DebugLevel > 4) llvm::errs() << "Select operands must have the same width\n";
      return false;
    }
  }
  if (Inst::isCmp(I->K)) {
    if (I->Width != 1) {
      if (DebugLevel > 4) llvm::errs() << "Comparison must be 1 bit wide\n";
      return false;
    }
  }
  if (I->K == Inst::Trunc) {
    if (I->Ops[0]->Width <= I->Width) {
      if (DebugLevel > 4) llvm::errs() << "Trunc operand must be wider than result\n";
      return false;
    }
  }
  if (I->K == Inst::ZExt || I->K == Inst::SExt) {
    if (I->Ops[0]->Width >= I->Width) {
      if (DebugLevel > 4) llvm::errs() << "Ext operand must be narrower than result\n";
      return false;
    }
  }
  return true;
}
bool typeCheck(ParsedReplacement &R) {
  if (R.Mapping.LHS->Width != R.Mapping.RHS->Width) {
    if (DebugLevel > 4) llvm::errs() << "LHS and RHS must have the same width\n";
    return false;
  }

  if (!typeCheck(R.Mapping.LHS)) {
    return false;
  }
  if (!typeCheck(R.Mapping.RHS)) {
    return false;
  }

  for (auto &&PC : R.PCs) {
    if (!typeCheck(PC.LHS)) {
      return false;
    }
    if (!typeCheck(PC.RHS)) {
      return false;
    }
  }
  return true;
}

struct ShrinkWrap {
  ShrinkWrap(InstContext &IC, Solver *S, ParsedReplacement Input,
             size_t TargetWidth = 8) : IC(IC), S(S), Input(Input),
                                       TargetWidth(TargetWidth) {}
  InstContext &IC;
  Solver *S;
  ParsedReplacement Input;
  size_t TargetWidth;

  std::map<Inst *, Inst *> InstCache;

  std::vector<Inst *> SynthConsts;

  // bool TryFixWidths(Inst *Root, std::map<Inst *, size_t> &Widths, size_t ResultWidth) {
  //   if (Widths.count(Root)) {
  //     if (Widths[Root] == ResultWidth)
  //   }
  // }

  Inst *ShrinkInst(Inst *I, Inst *Parent, size_t ResultWidth) {
    static size_t ReservedConstID = 1;
    if (InstCache.count(I)) {
      return InstCache[I];
    }
    if (I->K == Inst::Var) {
      if (I->Width == 1) {
        return I;
      }
      auto V = IC.createVar(ResultWidth, I->Name);
      InstCache[I] = V;
      return V;
    } else if (I->K == Inst::Const) {
      if (I->Width == 1) {
        return I;
      }
      // Treat 0, 1, and -1 specially
      if (I->Val.getLimitedValue() == 0) {
        auto C = IC.getConst(APInt(ResultWidth, 0));
        InstCache[I] = C;
        return C;
      } else if (I->Val.getLimitedValue() == 1) {
        auto C = IC.getConst(APInt(ResultWidth, 1));
        InstCache[I] = C;
        return C;
      } else if (I->Val.isAllOnesValue()) {
        auto C = IC.getConst(APInt::getAllOnesValue(ResultWidth));
        InstCache[I] = C;
        return C;
      } else {
        auto C = IC.createSynthesisConstant(ResultWidth, ReservedConstID++);
        SynthConsts.push_back(C);
        InstCache[I] = C;
        return C;
      }
    } else {
      if (I->K == Inst::Trunc) {
        size_t Target = 0;
        // llvm::errs() << "HERE: " << I->Width << " " << I->Ops[0]->Width << '\n';
        if (I->Ops[0]->Width == I->Width + 1) {
          // llvm::errs() << "a\n";
          Target = ResultWidth + 1;
        } else if (I->Ops[0]->Width == 2 * I->Width) {
          Target = ResultWidth * 2;
          // llvm::errs() << "b\n";
        } else if (I->Width == 1 && I->Ops[0]->Width != 1) {
          // llvm::errs() << "c\n";
          Target = TargetWidth;
          ResultWidth = 1;
        } else {
          // Maintain ratio
          // llvm::errs() << "d\n";
          Target = ResultWidth * I->Ops[0]->Width * 1.0 / I->Width;
          if (ResultWidth == 1 && I->Width != 1) {
            ResultWidth = 2;
          }
        }
        // llvm::errs() << "HERE: " << ResultWidth << " " << Target << '\n';
        // llvm::errs() << "Trunc " << I->Width << " " << ResultWidth << " " << Target << '\n';
        auto Operand = ShrinkInst(I->Ops[0], I, Target);
        if (Operand->Width <= ResultWidth) {
          return nullptr;
        }
        return IC.getInst(Inst::Trunc, ResultWidth, { ShrinkInst(I->Ops[0], I, Target)});
      }
      if (I->K == Inst::ZExt || I->K == Inst::SExt) {
        size_t Target = 0;
        if (I->Ops[0]->Width == I->Width - 1) {
          Target = ResultWidth - 1;
        } else if (I->Ops[0]->Width == I->Width / 2) {
          Target = ResultWidth / 2;
        } else if (I->Ops[0]->Width == 1) {
          Target = 1;
        } else {
          // Maintain ratio
          Target = ResultWidth * I->Ops[0]->Width * 1.0 / I->Width;
        }
        // llvm::errs() << "NAME: " << I->Ops[0]->Name << '\t' << I->Ops[0]->Width << '\n';
        // llvm::errs() << "Ext " << I->Width << " " << ResultWidth << " " << Target << '\n';
        auto Operand = ShrinkInst(I->Ops[0], I, Target);

        if (Operand->Width >= ResultWidth) {
          return nullptr;
        }
        return IC.getInst(I->K, ResultWidth, {Operand});
      }

      if (I->K == Inst::Eq || I->K == Inst::Ne ||
          I->K == Inst::Ult || I->K == Inst::Slt ||
          I->K == Inst::Ule || I->K == Inst::Sle ||
          I->K == Inst::KnownOnesP || I->K == Inst::KnownZerosP) {
        ResultWidth = TargetWidth;
      }


      // print kind name
      // llvm::errs() << "Par " << Inst::getKindName(I->K) << " " << I->Width << " " << ResultWidth << '\n';

      std::map<Inst *, Inst *> OpMap;
      std::vector<Inst *> OriginalOps = I->Ops;

      std::sort(OriginalOps.begin(), OriginalOps.end(), [&](Inst *A, Inst *B) {
        if (InstCache.find(A) != InstCache.end()) {
          return true;
        }
        if (A->K == Inst::Const) {
          return false;
        }

        if (A->K == Inst::Var && !(B->K == Inst::Var || B->K == Inst::Const)) {
          return false;
        }
        return A->Width > B->Width;
      });

      for (auto Op : OriginalOps) {
        OpMap[Op] = ShrinkInst(Op, I, ResultWidth);
        if (!OpMap[Op]) {
          return nullptr;
        }
        if (Op->Width != 1) {
          ResultWidth = OpMap[Op]->Width;
        }
      }

      std::vector<Inst *> Ops;
      for (auto Op : I->Ops) {
        Ops.push_back(OpMap[Op]);
      }

      return IC.getInst(I->K, InferWidth(I->K, Ops), Ops);
    }
  }

  std::optional<ParsedReplacement> operator()() {

    auto [CM, Aug] = AugmentForSymKBDB(Input, IC);

    if (!CM.empty()) {
      Input = Aug;
    }

    // Abort if inputs are of <= Target width
    std::vector<Inst *> Inputs;
    // TODO: Is there a better decision here?
    findVars(Input.Mapping.LHS, Inputs);
    for (auto I : Inputs) {
      if (I->Width <= TargetWidth) {
        return {};
      }
      if (!I->Range.isFullSet()) {
        return {};
      }
    }

    ParsedReplacement New;
    New.Mapping.LHS = ShrinkInst(Input.Mapping.LHS, nullptr, TargetWidth);
    New.Mapping.RHS = ShrinkInst(Input.Mapping.RHS, nullptr, TargetWidth);
    if (!New.Mapping.LHS || !New.Mapping.RHS) {
      return {};
    }
    for (auto PC : Input.PCs) {
      New.PCs.push_back({ShrinkInst(PC.LHS, nullptr, TargetWidth),
                         ShrinkInst(PC.RHS, nullptr, TargetWidth)});
      if (!New.PCs.back().LHS || !New.PCs.back().RHS) {
        return {};
      }
    }

    if (!typeCheck(New)) {
      llvm::errs() << "Type check failed\n";
      return {};
    }

    std::optional<ParsedReplacement> Result;
    size_t NumInequalityPCs = 0;

    // Push Inequality PCs
    for (size_t i = 1; i < SynthConsts.size(); ++i) {
      for (size_t j = 0; j < i; ++j) {
        if (SynthConsts[i]->Width != SynthConsts[j]->Width) {
          continue;
        }
        auto C1 = SynthConsts[i];
        auto C2 = SynthConsts[j];
        auto PC = IC.getInst(Inst::Ne, 1, {C1, C2});
        New.PCs.push_back({PC, IC.getConst(llvm::APInt(1, 1))});
        ++NumInequalityPCs;
      }
    }

    // Verify
    do {
      Result = Verify(New, IC, S);
      if (Result) {
        break;
      } else {
        New.PCs.pop_back();
      }
    } while (NumInequalityPCs--);

    if (!Result) {
      return {};
    }

    // Pop remaining Inequality PCs
    while (NumInequalityPCs--) {
      Result.value().PCs.pop_back();
    }

    return Result;
    // return Verify(New, IC, S);
  }
};

std::vector<Inst *> findConcreteConsts(const ParsedReplacement &Input) {
  std::vector<Inst *> Consts;
  auto Pred = [](Inst *I) {
    return I->K == Inst::Const && I->Name.find("sym") == std::string::npos;
  };

  findInsts(Input.Mapping.LHS, Consts, Pred);
  findInsts(Input.Mapping.RHS, Consts, Pred);
  std::set<Inst *> ResultSet; // For deduplication
  for (auto &&C : Consts) {
    ResultSet.insert(C);
  }
  std::vector<Inst *> Result;
  for (auto &&C : ResultSet) {
    Result.push_back(C);
  }
  return Result;
}

std::vector<Inst *> FilterExprsByValue(const std::vector<Inst *> &Exprs,
  llvm::APInt TargetVal, const std::vector<std::pair<Inst *, llvm::APInt>> &CMap) {
  std::unordered_map<Inst *, EvalValue> ValueCache;
  for (auto &&[I, V] : CMap) {
    ValueCache[I] = EvalValue(V);
  }
  std::vector<Inst *> FilteredExprs;
  ConcreteInterpreter CPos(ValueCache);
  for (auto &&E : Exprs) {
    if (E->Width != TargetVal.getBitWidth()) {
      continue;
    }
    auto Result = CPos.evaluateInst(E);
    if (Result.hasValue() && Result.getValue().getBitWidth() == TargetVal.getBitWidth()) {
      // llvm::errs() << Result.getValue() << "\t" <<  TargetVal << "\n";
      if (Result.getValue() == TargetVal) {
        FilteredExprs.push_back(E);
      }
    } else if (Result.K == EvalValue::ValueKind::Unimplemented) {
      FilteredExprs.push_back(E);
    }
  }
  return FilteredExprs;
}

std::vector<Inst *> FilterRelationsByValue(const std::vector<Inst *> &Relations,
                        const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
                        std::vector<ValueCache> CEXs) {
  std::unordered_map<Inst *, EvalValue> ValueCache;
  for (auto &&[I, V] : CMap) {
    ValueCache[I] = EvalValue(V);
  }

  ConcreteInterpreter CPos(ValueCache);
  std::vector<ConcreteInterpreter> CNegs;
  for (auto &&CEX : CEXs) {
    CNegs.push_back(CEX);
  }

  std::vector<Inst *> FilteredRelations;
  for (auto &&R : Relations) {
    auto Result = CPos.evaluateInst(R);
    // Positive example
    if (Result.hasValue() && !Result.getValue().isAllOnesValue()) {
      continue;
    }

    // Negative examples
    bool foundUnsound = false;
    for (auto &&CNeg : CNegs) {
      auto ResultNeg = CNeg.evaluateInst(R);
      if (ResultNeg.hasValue() && !ResultNeg.getValue().isNullValue()) {
        foundUnsound = true;
        break;
      }
    }
    if (foundUnsound) {
      continue;
    }
    FilteredRelations.push_back(R);
  }
  return FilteredRelations;
}

std::vector<Inst *> InferConstantLimits(
  const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
        InstContext &IC, const ParsedReplacement &Input,
        std::vector<ValueCache> CEXs) {
  std::vector<Inst *> Results;
  if (!FindConstantRelations) {
    return Results;
  }
  auto ConcreteConsts = findConcreteConsts(Input);
  std::sort(ConcreteConsts.begin(), ConcreteConsts.end(),
          [](auto A, auto B) {
            if (A->Width == B->Width) {
              return A->Val.ugt(B->Val);
            } else {
              return A->Width < B->Width;
            }
          });

  std::vector<Inst *> Vars;
  findVars(Input.Mapping.LHS, Vars);

  for (auto V : Vars) {
    for (auto &&[XI, XC] : CMap) {
      if (V->Width ==1 || XI->Width == 1) {
        continue;
      }
      // X < Width, X <= Width
      auto Width = Builder(V, IC).BitWidth()();

      if (XI->Width < V->Width) {
        Width = Builder(Width, IC).Trunc(XI->Width)();
      } else if (XI->Width > V->Width) {
        Width = Builder(Width, IC).ZExt(XI->Width)();
      }

      Results.push_back(Builder(XI, IC).Ult(Width)());
      Results.push_back(Builder(XI, IC).Ule(Width)());

      // x ule UMAX
      if (V->Width < XI->Width) {
        auto UMax = Builder(IC, llvm::APInt(XI->Width, 1)).Shl(Width).Sub(1);
        Results.push_back(Builder(XI, IC).Ule(UMax)());
      }

      // X ule SMAX
      auto WM1 = Builder(Width, IC).Sub(1);
      auto SMax = Builder(IC, llvm::APInt(XI->Width, 1)).Shl(WM1).Sub(1)();
      Results.push_back(Builder(XI, IC).Ule(SMax)());

      auto gZ = Builder(XI, IC).Ugt(0)();
      Results.push_back(Builder(XI, IC).Ult(Width).And(gZ)());
      Results.push_back(Builder(XI, IC).Ule(Width).And(gZ)());

      // 2 * X < C, 2 * X >= C
      for (auto C : ConcreteConsts) {
        if (C->Width != XI->Width) {
          continue;
        }
        auto Sum = Builder(XI, IC).Add(XI)();
        Results.push_back(Builder(Sum, IC).Ult(C->Val)());
        Results.push_back(Builder(Sum, IC).Ugt(C->Val)());
      }
    }
  }


  for (auto &&[XI, XC] : CMap) {
    for (auto &&[YI, YC] : CMap) {
      if (XI == YI) {
        continue;
      }
      if (XI->Width != YI->Width) {
        continue;
      }
      auto Sum = Builder(XI, IC).Add(YI)();
      // // Sum related to width
      // auto Width = Builder(Sum, IC).BitWidth();
      // Results.push_back(Builder(Sum, IC).Ult(Width)());
      // Results.push_back(Builder(Sum, IC).Ule(Width)());
      // Results.push_back(Builder(Sum, IC).Eq(Width)());

      // Sum less than const, Sum greater= than const
      for (auto C : ConcreteConsts) {
        if (Sum->Width != C->Width) {
          continue;
        }
        Results.push_back(Builder(Sum, IC).Ult(C->Val)());
        Results.push_back(Builder(Sum, IC).Ugt(C->Val)());
      }
    }
  }

  return FilterRelationsByValue(Results, CMap, CEXs);
}

// Enforce commutativity to prune search space
bool comm(Inst *A, Inst *B, Inst *C) {
  return A > B && B > C;
}
bool comm(Inst *A, Inst *B) {
  return A > B;
}

std::vector<Inst *> BitFuncs(Inst *I, InstContext &IC) {
  std::vector<Inst *> Results;
  Results.push_back(Builder(I, IC).CtPop()());
  Results.push_back(Builder(I, IC).Ctlz()());
  Results.push_back(Builder(I, IC).Cttz()());

  auto Copy = Results;
  for (auto &&C : Copy) {
    if (C->Width == 1) {
      continue;
    }
    if (C->Width != 1 && C->K == Inst::Var) {
      Results.push_back(Builder(C, IC).BitWidth().Sub(C)());
    }
  }

  return Results;
}

// This was originally intended to find relational constraints
// but we also use to fine some ad hoc constraints now.
// TODO: Filter relations by concrete interpretation
#define C2 comm(XI, YI)
#define C3 comm(XI, YI, ZI)

std::vector<Inst *> InferPotentialRelations(
        const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
        InstContext &IC, const ParsedReplacement &Input, std::vector<ValueCache> CEXs,
        bool LatticeChecks = false) {
  std::vector<Inst *> Results;
  if (!FindConstantRelations) {
    return Results;
  }


  // if (DebugLevel) {
  //   llvm::errs() << "Symconsts for rels: " << CMap.size() << "\n";
  // }
  // Triple rels
  if (CMap.size() >= 3) {
    for (auto &&[XI, XC] : CMap) {
      for (auto &&[YI, YC] : CMap) {
        for (auto &&[ZI, ZC] : CMap) {
          if (XI == YI || XI == ZI || YI == ZI) {
            continue;
          }
          if (XC.getBitWidth() != YC.getBitWidth() ||
              XC.getBitWidth() != ZC.getBitWidth()) {
            continue;
          }

          if (C3 && (XC | YC | ZC).isAllOnesValue()) {
            Results.push_back(Builder(XI, IC).Or(YI).Or(ZI)
              .Eq(llvm::APInt::getAllOnesValue(XI->Width))());
          }

          if (C3 && (XC & YC & ZC) == 0) {
            Results.push_back(Builder(XI, IC).And(YI).And(ZI)
              .Eq(llvm::APInt(XI->Width, 0))());
          }

          // TODO Make width independent by using bitwidth insts
          if (C2 && (XC | YC | ~ZC).isAllOnesValue()) {
            Results.push_back(Builder(XI, IC).Or(YI).Or(Builder(ZI, IC).Flip())
              .Eq(llvm::APInt::getAllOnesValue(XI->Width))());
          }

          if (XC << YC == ZC) {
            Results.push_back(Builder(XI, IC).Shl(YI).Eq(ZI)());
          }

          if (XC.lshr(YC) == ZC) {
            Results.push_back(Builder(XI, IC).LShr(YI).Eq(ZI)());
          }

          if (C2 && XC * YC == ZC) {
            Results.push_back(Builder(XI, IC).Mul(YI).Eq(ZI)());
          }

          if (C2 && XC + YC == ZC) {
            Results.push_back(Builder(XI, IC).Add(YI).Eq(ZI)());
          }

          // if (C2 && (XC & YC).eq(ZC)) {
          //   Results.push_back(Builder(XI, IC).And(YI).Eq(ZI)());
          // }

          // if (C2 && (XC | YC).eq(ZC)) {
          //   Results.push_back(Builder(XI, IC).Or(YI).Eq(ZI)());
          // }

          // if (C2 && (XC ^ YC).eq(ZC)) {
          //   Results.push_back(Builder(XI, IC).Xor(YI).Eq(ZI)());
          // }

          // if (C2 && (XC != 0 && YC != 0) && (XC + YC).eq(ZC)) {
          //   Results.push_back(Builder(XI, IC).Add(YI).Eq(ZI)());
          // }

        }
      }
    }
  }

  // Pairwise relations
  for (auto &&[XI, XC] : CMap) {
    // llvm::errs() << "HERE: " << XC << "\n";
    for (auto &&[YI, YC] : CMap) {
      if (XI == YI || XC.getBitWidth() != YC.getBitWidth()) {
        continue;
      }

      if (~XC == YC) {
        Results.push_back(Builder(XI, IC).Flip().Eq(YI)());
      }

      // no common bits set
      if ((XC & YC) == 0) {
        Results.push_back(Builder(XI, IC).And(YI).Eq(llvm::APInt(XI->Width, 0))());
      }

      if ((XC & YC) == XC) {
        Results.push_back(Builder(XI, IC).And(YI).Eq(XI)());
      }

      if ((XC | ~YC) == ~YC) {
        auto YFlip = Builder(YI, IC).Flip();
        Results.push_back(Builder(XI, IC).Or(YFlip).Eq(YFlip)());
      }

      if ((XC | ~YC) == ~XC) {
        auto YFlip = Builder(YI, IC).Flip();
        auto XFlip = Builder(XI, IC).Flip();
        Results.push_back(Builder(XI, IC).Or(YFlip).Eq(XFlip)());
      }

      if ((XC & YC) == YC) {
        Results.push_back(Builder(XI, IC).And(YI).Eq(YI)());
      }

      if ((XC | YC) == XC) {
        Results.push_back(Builder(XI, IC).Or(YI).Eq(XI)());
      }
      if ((XC | YC) == YC) {
        Results.push_back(Builder(XI, IC).Or(YI).Eq(YI)());
      }

      if (XC == (XC.lshr(YC).shl(YC))) {
        Results.push_back(Builder(XI, IC).LShr(YI).Shl(YI).Eq(XI)());
      }

      if (XC == (XC.ashr(YC).shl(YC))) {
        Results.push_back(Builder(XI, IC).AShr(YI).Shl(YI).Eq(XI)());
      }

      if (XC == (XC.shl(YC).lshr(YC))) {
        Results.push_back(Builder(XI, IC).Shl(YI).LShr(YI).Eq(XI)());
      }

      if (XC == (XC.shl(YC).ashr(YC))) {
        Results.push_back(Builder(XI, IC).Shl(YI).AShr(YI).Eq(XI)());
      }

      // Mul C
      if (C2 && YC!= 0 && XC.urem(YC) == 0) {
        auto Fact = XC.udiv(YC);
        if (Fact != 1 && Fact != 0) {
          Results.push_back(Builder(YI, IC).Mul(Fact).Eq(XI)());
        }
      }

      // Add C
      // auto Diff = XC - YC;
      // if (Diff != 0) {
      //   Results.push_back(Builder(XI, IC).Sub(Diff).Eq(YI)());
      // }

      if (C2 && XC != 0 && YC.urem(XC) == 0) {
        auto Fact = YC.udiv(XC);
        if (Fact != 1 && Fact != 0) {
          Results.push_back(Builder(XI, IC).Mul(Fact).Eq(YI)());
        }
      }

      auto One = llvm::APInt(XC.getBitWidth(), 1);

      if (XI->Width != 1 && XC - YC == 1) {
        Results.push_back(Builder(XI, IC).Sub(YI).Eq(One)());
      }

      auto GENComps = [&] (Inst *A, llvm::APInt AVal, Inst *B, llvm::APInt BVal) {
        if (AVal.ne(BVal)) Results.push_back(Builder(A, IC).Ne(B)());
        // For width == 1, there is exactly one model, hence it isn't a generalization
        if (AVal.sle(BVal)  && A->Width != 1) Results.push_back(Builder(A, IC).Sle(B)());
        if (AVal.ule(BVal)  && A->Width != 1) Results.push_back(Builder(A, IC).Ule(B)());
        if (AVal.slt(BVal)  && A->Width != 1) Results.push_back(Builder(A, IC).Slt(B)());
        if (AVal.ult(BVal)  && A->Width != 1) Results.push_back(Builder(A, IC).Ult(B)());
      };

      GENComps(XI, XC, YI, YC);
      // GENComps(Builder(IC, One).Shl(XI)() , One.shl(XC), YI, YC);
      // GENComps(XI, XC, Builder(IC, One).Shl(YI)() , One.shl(YC));


      // auto XBits = BitFuncs(XI, IC);
      // auto YBits = BitFuncs(YI, IC);

      // for (auto &&XBit : XBits) {
      //   for (auto &&YBit : YBits) {
      //     Results.push_back(Builder(XBit, IC).Ule(YBit)());
      //     Results.push_back(Builder(XBit, IC).Ult(YBit)());
      //   }
      // }

      // No example yet where this is useful
      // for (auto &&XBit : XBits) {
      //   for (auto &&YBit : YBits) {
      //     Results.push_back(Builder(XBit, IC).Ne(YBit)());
      //     Results.push_back(Builder(XBit, IC).Eq(YBit)());
      //   }
      // }

    }
    if (XI->Width != 1) {
      Results.push_back(Builder(XI, IC).Eq(Builder(XI, IC).BitWidth().Sub(1))());
      // Results.push_back(Builder(XI, IC).Eq(Builder(XI, IC).BitWidth().UDiv(2))());
      // Results.push_back(Builder(XI, IC).Eq(Builder(XI, IC).BitWidth())());
    }
  }

  for (auto &&[XI, XC] : CMap) {
    for (auto &&[YI, YC] : CMap) {
      if (XI == YI || XC.getBitWidth() == YC.getBitWidth()) {
        continue;
      }

      if (XC.getLimitedValue() == YC.getLimitedValue()) {
        if (XI->Width > YI->Width) {
          Results.push_back(Builder(YI, IC).ZExt(XI->Width).Eq(XI)());
        } else if (XI->Width < YI->Width) {
          Results.push_back(Builder(XI, IC).ZExt(YI->Width).Eq(YI)());
        }
      } else {
        if (XI->Width > YI->Width) {
          Results.push_back(Builder(YI, IC).ZExt(XI->Width).Ne(XI)());
        } else if (XI->Width < YI->Width) {
          Results.push_back(Builder(XI, IC).ZExt(YI->Width).Ne(YI)());
        }
      }

      if (XC.getLimitedValue() < YC.getLimitedValue()) {
        if (XI->Width > YI->Width) {
          Results.push_back(Builder(XI, IC).Ult(Builder(YI, IC).ZExt(XI->Width))());
          Results.push_back(Builder(XI, IC).Slt(Builder(YI, IC).ZExt(XI->Width))());
          Results.push_back(Builder(XI, IC).Ult(Builder(YI, IC).SExt(XI->Width))());
          Results.push_back(Builder(XI, IC).Slt(Builder(YI, IC).SExt(XI->Width))());
        } else if (XI->Width < YI->Width) {
          Results.push_back(Builder(XI, IC).ZExt(YI->Width).Ult(YI)());
          Results.push_back(Builder(XI, IC).ZExt(YI->Width).Slt(YI)());
          Results.push_back(Builder(XI, IC).SExt(YI->Width).Ult(YI)());
          Results.push_back(Builder(XI, IC).SExt(YI->Width).Slt(YI)());
        }
      }

    }
  }

  // for (auto R : InferConstantLimits(CMap, IC, Input)) {
  //   Results.push_back(R);
  // }
  // llvm::errs() << "HERE: " << Results.size() << '\n';
  Results = FilterRelationsByValue(Results, CMap, CEXs);

  // llvm::errs() << "HERE: " << Results.size() << "\t" << LatticeChecks << '\n';
  // if (LatticeChecks) {
  //   std::vector<Inst *> Inputs;
  //   findVars(Input.Mapping.LHS, Inputs);

  //   std::vector<Inst *> WExprs;

  //   for (auto X : Inputs) {
  //     for (auto Y : Inputs) {
  //       if (X == Y || X->Width >= Y->Width) {
  //         continue;
  //       }

  //       // (-1 << zext(width(X)))
  //       auto MinusOne = llvm::APInt::getAllOnesValue(Y->Width);
  //       auto ZExt = Builder(X, IC).BitWidth().ZExt(Y->Width)();
  //       auto OnesThenZeros = Builder(IC.getConst(MinusOne), IC).Shl(ZExt);
  //       WExprs.push_back(OnesThenZeros());
  //       // Flip Above
  //       WExprs.push_back(OnesThenZeros.Flip()());

  //       // (-1 >> zext(width(X)))
  //       auto ZerosThenOnes = Builder(IC.getConst(MinusOne), IC).LShr(ZExt);
  //       WExprs.push_back(ZerosThenOnes());
  //       // Flip Above
  //       WExprs.push_back(ZerosThenOnes.Flip()());

  //     }
  //   }

  //   // TODO Less brute force
  //   for (auto &&[XI, XC] : CMap) {
  //     for (auto &&[YI, YC] : CMap) {
  //       if (XI == YI || XC.getBitWidth() != YC.getBitWidth()) {
  //         continue;
  //       }
  //       // llvm::errs() << "HERE: " << XI->Name << ' ' << YI->Name << ' ' << XC.getLimitedValue() << ' ' <<  YC.getLimitedValue() << '\n';
  //       Results.push_back(IC.getInst(Inst::KnownOnesP, 1, {XI, YI}));
  //       Results.push_back(IC.getInst(Inst::KnownZerosP, 1, {XI, YI}));
  //     }
  //   }

  //   for (auto &&Expr : WExprs) {
  //     for (auto &&[XI, XC] : CMap) {
  //       Results.push_back(IC.getInst(Inst::KnownOnesP, 1, {XI, Expr}));
  //       Results.push_back(IC.getInst(Inst::KnownZerosP, 1, {XI, Expr}));
  //       Results.push_back(IC.getInst(Inst::KnownOnesP, 1, {Expr, XI}));
  //       Results.push_back(IC.getInst(Inst::KnownZerosP, 1, {Expr, XI}));
  //     }
  //   }
  // }
  // llvm::errs() << "THERE: " << Results.size() << "\t" << LatticeChecks << '\n';

  return Results;
}

#undef C2
#undef C3

struct Cmp {
  bool operator() (Inst *A, Inst *B) const {
    return B->Val.getLimitedValue() < A->Val.getLimitedValue();
  }
};

std::set<Inst *, Cmp> findConcreteConsts(Inst *I) {
  std::vector<Inst *> Results;
  std::set<Inst *, Cmp> Ret;
  auto Pred = [](Inst *I) {return I->K == Inst::Const;};
  findInsts(I, Results, Pred);
  for (auto R : Results) {
    Ret.insert(R);
  }
  return Ret;
}

std::optional<ParsedReplacement> DFPreconditionsAndVerifyGreedy(
  ParsedReplacement Input, InstContext &IC, Solver *S,
  std::map<Inst *, llvm::APInt> SymCS) {

  // return {};

  std::map<Inst *, std::pair<llvm::APInt, llvm::APInt>> Restore;

  // auto Clone = souper::Clone(Input, IC);
  // std::swap(Input, Clone);

  size_t BitsWeakened = 0;

  for (auto &&C : SymCS) {
    if (C.first->Width < 4) continue;
    Restore[C.first] = {C.first->KnownZeros, C.first->KnownOnes};
    C.first->KnownZeros = ~C.second;
    C.first->KnownOnes = C.second;
  }

  std::map<Inst *, llvm::APInt> RevertMap;

  std::optional<ParsedReplacement> Ret;
  auto SOLVE = [&]() -> bool {
    Ret = Verify(Input, IC, S);
    if (Ret) {
      return true;
    } else {
      return false;
    }
  };
  size_t ConstsWeakened = 0;
  for (auto &&C : SymCS) {
    if (C.first->Width < 4) continue;
    BitsWeakened = 0;
    for (size_t i = 0; i < C.first->Width; ++i) {
      llvm::APInt OriZ = C.first->KnownZeros;
      llvm::APInt OriO = C.first->KnownOnes;

      if (OriO[i] == 0 && OriZ[i] == 0) {
        continue;
      }

      if (OriO[i] == 1) C.first->KnownOnes.clearBit(i);
      if (OriZ[i] == 1) C.first->KnownZeros.clearBit(i);

      if (!SOLVE()) {
        C.first->KnownZeros = OriZ;
        C.first->KnownOnes = OriO;
      } else {
        BitsWeakened++;
      }
    }
    // llvm::errs() << "BitsWeakened: " << BitsWeakened << '\n';
    if (BitsWeakened <= C.first->Width / 2) {
      C.first->KnownZeros = ~SymCS[C.first];
      C.first->KnownOnes = SymCS[C.first];
      RevertMap[C.first] = SymCS[C.first];
    } else {
      ConstsWeakened++;
    }
  }
  // llvm::errs() << "ConstsWeakened: " << ConstsWeakened << '\n';
  if (!ConstsWeakened) {
    // std::swap(Input, Clone);
    for (auto &&P : Restore) {
      P.first->KnownZeros = P.second.first;
      P.first->KnownOnes = P.second.second;
    }
    // Input.print(llvm::errs(), true);
    // llvm::errs() << "\n<-Input\n";
    // Clone.print(llvm::errs(), true);
    // llvm::errs() << "\n<-Clone\n";
    return {};
  } else {
    return souper::Replace(Input, IC, RevertMap);
  }
}

std::optional<ParsedReplacement> SimplePreconditionsAndVerifyGreedy(
        ParsedReplacement Input, InstContext &IC,
        Solver *S, std::map<Inst *, llvm::APInt> SymCS) {
  // Assume Input is not valid
  std::map<Inst *, llvm::APInt> NonBools;
  for (auto &&C : SymCS) {
    if (C.first->Width != 1) {
      NonBools.insert(C);
    }
  }
  std::swap(SymCS, NonBools);

  std::optional<ParsedReplacement> Clone = std::nullopt;

  auto SOLVE = [&]() -> bool {
    Clone = Verify(Input, IC, S);
    if (Clone) {
      return true;
    } else {
      return false;
    }
  };

  std::vector<Inst *> Insts;
  findVars(Input.Mapping.LHS, Insts);

  std::vector<std::map<Inst *, llvm::APInt>> Inputs;
  Inputs.push_back({});
  for (auto &&P : SymCS) {
    Inputs.back()[P.first] = P.second;
  }

  std::map<Inst *, std::vector<llvm::APInt>> CVals;

  for (auto &&I : Inputs) {
    for (auto &&P: I) {
      CVals[P.first].push_back(P.second);
    }
  }

  #define DF(Fact, Check)                                       \
  if (All(CVals[C], [](auto Val) { return Check;})) {           \
  C->Fact = true; auto s = SOLVE(); C->Fact = false;            \
  if(s) return Clone;};

  #define DF2(C1, C2, Fact1, Check1, Fact2, Check2)             \
  if (All(CVals[C1], [](auto Val) { return Check1;})) {         \
  if (All(CVals[C2], [](auto Val) { return Check2;})) {         \
  C1->Fact1 = true; C2->Fact2 = true; auto s = SOLVE();         \
  C1->Fact1 = false; C2->Fact2 = false;                         \
  if(s) return Clone;}};

  #define DF3(C1, C2, C3, Fact1, Check1, Fact2, Check2, Fact3, Check3)\
  if (All(CVals[C1], [](auto Val) { return Check1;})) {         \
  if (All(CVals[C2], [](auto Val) { return Check2;})) {         \
  if (All(CVals[C3], [](auto Val) { return Check3;})) {         \
  C1->Fact1 = true; C2->Fact2 = true; C3->Fact3 = true;         \
  auto s = SOLVE();                                             \
  C1->Fact1 = false; C2->Fact2 = false; C3->Fact3 = false;      \
  if(s) return Clone;}}};


  for (auto &&P : SymCS) {
    auto C = P.first;
    DF(PowOfTwo, Val.isPowerOf2()); // Invoke solver only if Val is a power of 2
    DF(NonNegative, Val.uge(0));
    DF(NonZero, Val != 0);
    DF(Negative, Val.slt(0));
    DF2(C, C, NonNegative, Val.uge(0), NonZero, Val != 0);
    for (auto &&P2 : SymCS) {
      if (P.first == P2.first) {
        continue;
      }
      auto C2 = P2.first;
      DF2(C, C2, NonZero, Val != 0, NonZero, Val != 0);
      DF2(C, C2, NonNegative, Val.uge(0), NonNegative, Val.uge(0));
      DF2(C, C2, Negative, Val.slt(0), Negative, Val.slt(0));
      DF2(C, C2, PowOfTwo, Val.isPowerOf2(), PowOfTwo, Val.isPowerOf2());

      for (auto &&P3 : SymCS) {
        if (P.first == P3.first) {
          continue;
        }
        if (P2.first == P3.first) {
          continue;
        }
        auto C3 = P3.first;
        DF3(C, C2, C3, PowOfTwo, Val.isPowerOf2(), PowOfTwo, Val.isPowerOf2(), PowOfTwo, Val.isPowerOf2());

      }
    }
  }

  #undef DF
  #undef DF2
  #undef DF3


  return Clone;
}

size_t BruteForceModelCount(Inst *Pred) {
  if (Pred->Width >= 8) {
    llvm::errs() << "Too wide for brute force model counting.\n";
    return 0;
  }

  std::vector<Inst *> Inputs;
  findVars(Pred, Inputs);

  ValueCache Cache;
  for (auto I : Inputs) {
    Cache[I] = EvalValue(llvm::APInt(I->Width, 0));
  }

  auto Update = [&]() {
    for (auto I : Inputs) {
      if (Cache[I].getValue() == llvm::APInt(I->Width, -1)) {
        continue;
      } else {
        Cache[I] = EvalValue(Cache[I].getValue() + 1);
        return true;
      }
    }
    return false;
  };

  size_t ModelCount = 0;

  do {
    ConcreteInterpreter CI(Cache);

    if (CI.evaluateInst(Pred).hasValue() &&
        CI.evaluateInst(Pred).getValue().getBoolValue()) {
      ++ModelCount;
    }
  } while (Update());

  return ModelCount;
}

void SortPredsByModelCount(std::vector<Inst *> &Preds) {
  std::unordered_map<Inst *, size_t> ModelCounts;
  for (auto P : Preds) {
    ModelCounts[P] = BruteForceModelCount(P);
  }
  std::sort(Preds.begin(), Preds.end(), [&](Inst *A, Inst *B) {
    return ModelCounts[A] > ModelCounts[B];
  });
}

std::optional<ParsedReplacement> VerifyWithRels(InstContext &IC, Solver *S,
                                 ParsedReplacement Input,
                                 std::vector<Inst *> &Rels,
                                 std::map<Inst *, llvm::APInt> SymCS = {}) {
  std::vector<Inst *> ValidRels;

  ParsedReplacement FirstValidResult = Input;

  for (auto Rel : Rels) {
    Input.PCs.push_back({Rel, IC.getConst(llvm::APInt(1, 1))});

    // InfixPrinter IP(Input);
    // IP(llvm::errs());

    auto Clone = Verify(Input, IC, S);

    if (!Clone && !SymCS.empty()) {
      Clone = SimplePreconditionsAndVerifyGreedy(Input, IC, S, SymCS);
    }

    // InfixPrinter IP(Input);
    // IP(llvm::errs());

    // Input.print(llvm::errs(), true);

    // llvm::errs() << "RESULT: " << Clone.has_value() << "\n";

    if (Clone) {
      ValidRels.push_back(Rel);
      FirstValidResult = Clone.value();
      if (Rels.size() > 10) {
        return Clone;
      }
    }
    Input.PCs.pop_back();
  }

  if (ValidRels.empty()) {
    return std::nullopt;
  }

  std::vector<Inst *> Inputs;
  findVars(Input.Mapping.LHS, Inputs);

  size_t MaxWidth = 0;
  for (auto I : Inputs) {
    if (I->Width > MaxWidth) {
      MaxWidth = I->Width;
    }
  }

  if (MaxWidth > 8) {
    if (DebugLevel > 4) {
      llvm::errs() << "Too wide for brute force model counting.\n";
    }
    // TODO: Use approximate model counting?
    return FirstValidResult;
  }

  SortPredsByModelCount(ValidRels);
  // For now, return the weakest valid result
  Input.PCs.push_back({ValidRels[0], IC.getConst(llvm::APInt(1, 1))});
  return Input;
}


std::optional<ParsedReplacement>
FirstValidCombination(ParsedReplacement Input,
                      const std::vector<Inst *> &Targets,
                      const std::vector<std::vector<Inst *>> &Candidates,
                      std::map<Inst *, Inst *> InstCache,
                      InstContext &IC, Solver *S,
                      std::map<Inst *, llvm::APInt> SymCS,
                      bool GEN,
                      bool SDF,
                      bool DFF,
                      std::vector<Inst *> Rels = {},
                      bool print = false) {

  // if (Candidates[0].size()) {
  // llvm::errs() << "FirstValidCombination: " << Candidates[0].size() << "\n";

  // ReplacementContext RC;
  // RC.printInst(Candidates[0][0], llvm::errs(), true);
  // llvm::errs() << "\n";
  // }

  std::vector<int> Counts;
  for (auto &&Cand : Candidates) {
    Counts.push_back(Cand.size());
  }

  auto Combinations = GetCombinations(Counts);

  size_t IterLimit = 2000;
  size_t CurIter = 0;

  std::set<Inst *> SymConstsInPC;
  for (auto PC : Input.PCs) {
    std::vector<Inst *> Vars;
    findVars(PC.LHS, Vars);
    for (auto &&V : Vars) {
      if (V->Name.starts_with("sym")) {
        SymConstsInPC.insert(V);
      }
    }
  }

  for (auto &&Comb : Combinations) {
    if (CurIter >= IterLimit) {
      break;
    } else {
      CurIter++;
    }

    static int SymExprCount = 0;
    auto InstCacheRHS = InstCache;

    std::vector<Inst *> VarsFound;

    for (int i = 0; i < Targets.size(); ++i) {
      InstCacheRHS[Targets[i]] = Candidates[i][Comb[i]];
      findVars(Candidates[i][Comb[i]], VarsFound);
      if (Candidates[i][Comb[i]]->K != Inst::Var) {
        Candidates[i][Comb[i]]->Name = std::string("constexpr_") + std::to_string(SymExprCount++);
      }
    }

    std::set<Inst *> SymsInCurrent = SymConstsInPC;
    for (auto &&V : VarsFound) {
      if (V->Name.starts_with("sym")) {
        SymsInCurrent.insert(V);
      }
    }

    std::map<Inst *, Inst *> ReverseMap;

    for (auto &&[C, Val] : SymCS) {
      if (SymsInCurrent.find(C) == SymsInCurrent.end()) {
        ReverseMap[C] = Builder(IC, Val)();
      }
    }

    std::optional<ParsedReplacement> Clone = std::nullopt;

    auto SOLVE = [&](ParsedReplacement P) -> bool {
      // InfixPrinter IP(P);
      // IP(llvm::errs());
      // llvm::errs() << "\n";

      if (GEN) {
        Clone = Verify(P, IC, S);
        if (Clone) {
          return true;
        }
      }

      if (!Rels.empty()) {
        auto Result = VerifyWithRels(IC, S, P, Rels);
        if (Result) {
          Clone = *Result;
          return true;
        }
      }

      if (SDF) {
        Clone = SimplePreconditionsAndVerifyGreedy(P, IC, S, SymCS);

        if (Clone) {
          return true;
        }
      }

      if (DFF) {
        Clone = DFPreconditionsAndVerifyGreedy(P, IC, S, SymCS);
        if (Clone) {
          return true;
        }
      }

      return false;
    };

    auto Copy = Input;
    Copy.Mapping.LHS = Replace(Input.Mapping.LHS, IC, InstCacheRHS);
    Copy.Mapping.RHS = Replace(Input.Mapping.RHS, IC, InstCacheRHS);



    // Copy.PCs = Input.PCs;
    if (SOLVE(Copy)) {
      return Clone;
    }

    if (!ReverseMap.empty()) {
      Copy.Mapping.LHS = Replace(Copy.Mapping.LHS, IC, ReverseMap);
      Copy.Mapping.RHS = Replace(Copy.Mapping.RHS, IC, ReverseMap);

      if (SOLVE(Copy)) {
        return Clone;
      }
    }

  }
  return std::nullopt;
}



std::vector<Inst *> IOSynthesize(llvm::APInt Target,
const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap,
InstContext &IC, size_t Threshold, bool ConstMode, Inst *ParentConst = nullptr) {

  std::vector<Inst *> Results;

  // Handle width changes
  for (const auto &[I, Val] : ConstMap) {
    if (I == ParentConst) {
      continue; // avoid no-ops
    }
    if (Target.getBitWidth() == I->Width || !Threshold ) {
      continue;
    }

    // if (I->Name == "symDF_DB") {
    //   continue;
    // }

    llvm::APInt NewTarget = Target;
    if (Target.getBitWidth() < I->Width) {
      NewTarget = Target.sgt(0) ? Target.zext(I->Width) : Target.sext(I->Width);
    } else if (Target.getBitWidth() > I->Width) {
      NewTarget = Target.trunc(I->Width);
    }
    for (auto X : IOSynthesize(NewTarget, ConstMap, IC, Threshold - 1, ConstMode, nullptr)) {
      // ReplacementContext RC;
      // RC.printInst(X, llvm::errs(), true);
      if (NewTarget.getBitWidth() < Target.getBitWidth()) {
        Results.push_back(Builder(IC, X).ZExt(Target.getBitWidth())());
        Results.push_back(Builder(IC, X).SExt(Target.getBitWidth())());
      } else if (NewTarget.getBitWidth() > Target.getBitWidth()) {
        Results.push_back(Builder(IC, X).Trunc(Target.getBitWidth())());
      }
    }
  }

  for (const auto &[I, Val] : ConstMap) {
    if (I == ParentConst) {
      continue;
    }
    if (I->Width != Target.getBitWidth()) {
      continue;
    }
    if (!ConstMode) {
      if (Val == Target) {
        Results.push_back(I);
      } else if (Val == 0 - Target) {
        Results.push_back(Builder(IC, I).Negate()());
      } else if (Val == ~Target) {
        Results.push_back(Builder(IC, I).Flip()());
      }

      // llvm::errs() << "Trying to synthesize " << Target << " from " << Val << "\n";

      auto One = llvm::APInt(I->Width, 1);
      // llvm::errs() << "1: " << One.shl(Val) << "\n";
      if (One.shl(Val) == Target) {
        Results.push_back(Builder(IC, One).Shl(I)());
      }
      auto MinusOneVal = llvm::APInt::getAllOnesValue(I->Width);

      auto OneBitOne = llvm::APInt(1, 1);
      auto MinusOne = Builder(IC, OneBitOne).SExt(I->Width)();

      // llvm::errs() << "2: " << MinusOne.shl(Val) << "\n";
      if (MinusOneVal.shl(Val) == Target) {
        Results.push_back(Builder(IC, MinusOne).Shl(I)());
      }
      // llvm::errs() << "3: " << MinusOne.lshr(Val) << "\n";
      if (MinusOneVal.lshr(Val) == Target) {
        Results.push_back(Builder(IC, MinusOne).LShr(I)());
      }
    } else {
      if (ParentConst) {
        Results.push_back(Builder(IC, Target)());
      }
    }
  }

  if (!Threshold) {
    return Results;
  }

  // Recursive formulation

  #define for_no_nop(X, x) \
  if (Target != x) for (auto X : \
  IOSynthesize(x, ConstMap, IC, Threshold - 1, ConstMode, ParentConst))

  for (const auto &[I, Val] : ConstMap) {
    if (I->Width != Target.getBitWidth()) {
      continue;
    }

    if (I == ParentConst) {
      continue;
    }
    ParentConst = I;

    // Binary operators

    // C + X == Target
    for_no_nop(X, Target - Val) {
      Results.push_back(Builder(I, IC).Add(X)());
    }

    // C - X == Target
    for_no_nop(X, Val - Target) {
      Results.push_back(Builder(I, IC).Sub(X)());
    }

    // X - C == Target
    for_no_nop(X, Target + Val) {
      Results.push_back(Builder(X, IC).Sub(I)());
    }

    // C * X == Target
    if (Val.isNegative() || Target.isNegative()) {
      if (Val != 0 && Target.srem(Val) == 0) {
        for_no_nop(X, Target.sdiv(Val)) {
          Results.push_back(Builder(X, IC).Mul(I)());
        }
      }
    } else {
      if (Val != 0 && Target.urem(Val) == 0) {
        for_no_nop(X, Target.udiv(Val)) {
          Results.push_back(Builder(X, IC).Mul(I)());
        }
      }
    }

    // C / X == Target
    if (Val.isNegative() || Target.isNegative()) {
      if (Target != 0 && Val.srem(Target) == 0) {
        for_no_nop(X, Val.sdiv(Target)) {
          Results.push_back(Builder(I, IC).SDiv(X)());
        }
      }
    } else {
      if (Target != 0 && Val.urem(Target) == 0) {
        for_no_nop(X, Val.udiv(Target)) {
          Results.push_back(Builder(I, IC).UDiv(X)());
        }
      }
    }

    // X / C == Target

    if (Val.isNegative() || Target.isNegative()) {
      if (Val != 0 && Target.srem(Val) == 0) {
        for_no_nop(X, Val * Target) {
          Results.push_back(Builder(X, IC).SDiv(I)());
        }
      }
    } else {
      if (Val != 0 && Target.urem(Val) == 0) {
        for_no_nop(X, Val * Target) {
          Results.push_back(Builder(X, IC).UDiv(I)());
        }
      }
    }

    // Shifts?

    // Unary operators (no recursion required)
    if (Target == Val.logBase2()) {
      Results.push_back(Builder(I, IC).LogB()());
    }

    if (Target == Val.reverseBits()) {
      Results.push_back(Builder(I, IC).BitReverse()());
    }
    // TODO Add others

    // bit flip
    llvm::APInt D = Val;
    D.flipAllBits();
    if (Target == D) {
      Results.push_back(Builder(I, IC).Xor(llvm::APInt::getAllOnesValue(I->Width))());
    }

    if (Target == D + 1) {
      Results.push_back(Builder(I, IC).Xor(llvm::APInt::getAllOnesValue(I->Width)).Add(1)());
    }

    // neg
    D = Val;
    D.negate();
    if (Target == D && D != Val) {
      Results.push_back(Builder(IC, llvm::APInt::getAllOnesValue(I->Width)).Sub(I)());
    }

    for (const auto &[I2, Val2] : ConstMap) {
      if (I == I2 || I->Width != I2->Width || I2 == ParentConst) {
        continue;
      }
      if ((Val & Val2) == Target && !Val.isAllOnesValue() && !Val2.isAllOnesValue()) {
        Results.push_back(Builder(I, IC).And(I2)());
      }
      if ((Val | Val2) == Target && Val != 0 && Val2 != 0) {
        Results.push_back(Builder(I, IC).Or(I2)());
      }
      if ((Val ^ Val2) == Target && Val != Target && Val2 != Target) {
        Results.push_back(Builder(I, IC).Xor(I2)());
      }
    }
  }

  return Results;
}

void CountUses(Inst *I, std::map<Inst *, size_t> &Count) {
  std::vector<Inst *> Stack{I};
  std::set<Inst *> Visited;
  while (!Stack.empty()) {
    auto *I = Stack.back();
    Stack.pop_back();
    if (Visited.count(I)) {
      continue;
    }
    Visited.insert(I);
    for (auto *U : I->Ops) {
      if (U->K == Inst::Var) {
        Count[U]++;
      }
      Stack.push_back(U);
    }
  }
}

// // Filter candidates to rule out NOPs as much as possible
// std::vector<Inst *> FilterCand(std::vector<Inst *> Cands,
// const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap) {
//   return Cands;
//   std::vector<Inst *> Results;
//   for (auto &&C : Cands) {
//     std::map<Inst *, size_t> VarCount = CountUses(C);

//     C->Print();
//     for (auto &[I, Count] : VarCount) {
//       llvm::errs() << I->Name << " " << Count << "\t";
//     }
//     llvm::errs() << "\n\n";


//     bool hasDupe = false;
//     for (auto &[_, Count] : VarCount) {
//       if (Count > 4) {
//         hasDupe = true;
//         break;
//       }
//     }
//     if (hasDupe) {
//       continue;
//     }

//     Results.push_back(C);
//   }
//   return Results;
// }

std::vector<std::vector<Inst *>>
InferSpecialConstExprsAllSym(std::vector<Inst *> RHS,
const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap,
                             InstContext &IC, int depth = 3) {
  std::vector<std::vector<Inst *>> Results;
  for (auto R : RHS) {
    auto Cands = IOSynthesize(R->Val, ConstMap, IC, depth, false);

    // Filter by value
    std::vector<Inst *> Filtered = FilterExprsByValue(Cands, R->Val, ConstMap);

    std::set<Inst *> Temp; // TODO: Push the sorting here
    for (auto C : Cands) {
      Temp.insert(C);
    }
    std::vector<Inst *> DedupedCands;
    for (auto C : Temp) {
      DedupedCands.push_back(C);
    }
    Results.push_back(DedupedCands);
    std::sort(Results.back().begin(), Results.back().end(),
              [](Inst *A, Inst *B) { return instCount(A) < instCount(B);});
  }
  return Results;
}

std::vector<std::vector<Inst *>>
InferSpecialConstExprsWithConcretes(std::vector<Inst *> RHS,
const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap,
                             InstContext &IC, int depth = 3) {
  std::vector<std::vector<Inst *>> Results;
  for (auto R : RHS) {
    auto Cands = IOSynthesize(R->Val, ConstMap, IC, depth, true);
    std::vector<Inst *> Filtered;
    for (auto Cand : Cands) {
      if (Cand->K != Inst::Const) {
        Filtered.push_back(Cand);
      }
    }
    Results.push_back(Filtered);
  }
  return Results;
}

std::vector<Inst *> AllSubExprs(Inst *I, size_t W) {
  std::set<Inst *> Visited;
  std::vector<Inst *> Stack{I};

  std::vector<Inst *> Result;

  while (!Stack.empty()) {
    auto *I = Stack.back();
    Stack.pop_back();
    if (Visited.count(I)) {
      continue;
    }
    if (I->K == Inst::Var || I->K == Inst::Const) {
      continue;
    }
    Visited.insert(I);
    if (I->Width == W) {
      Result.push_back(I);
    }
    Stack.insert(Stack.end(), I->Ops.begin(), I->Ops.end());
  }

  return Result;
}

std::vector<Inst *> ExtractSketchesSimple(InstContext &IC, ParsedReplacement Input,
                                          const std::map<Inst *, Inst *> &SymConstMap,
                                          size_t Width) {
  std::vector<Inst *> Sketches;
  std::vector<Inst *> Inputs;
  findVars(Input.Mapping.LHS, Inputs);

  if (Inputs.size() != 1) {
    return Sketches;
  }

  auto BoolOne = IC.getConst(llvm::APInt(1, 1));
  std::vector<Inst *> ConstList = {IC.getConst(llvm::APInt(Inputs[0]->Width, 0)),
                                   IC.getConst(llvm::APInt(Inputs[0]->Width, 1)),
                                   Builder(BoolOne, IC).SExt(Inputs[0]->Width)()};

  for (auto &&C : ConstList) {
    auto MapCopy = SymConstMap;
    MapCopy[Inputs[0]] = C;

    if (MapCopy.empty()) {
      continue;
    }

    auto Root = Replace(Input.Mapping.LHS, IC, MapCopy);

    for (auto I : AllSubExprs(Root, Width)) {
      Sketches.push_back(I);
    }
  }

  return Sketches;
}

// precondition: operands are const, won't check here
std::optional<llvm::APInt> Fold(Inst *I) {
  switch (I->K) {
    case Inst::Add:
      return I->Ops[0]->Val + I->Ops[1]->Val;
    case Inst::Sub:
      return I->Ops[0]->Val - I->Ops[1]->Val;
    case Inst::Mul:
      return I->Ops[0]->Val * I->Ops[1]->Val;
    case Inst::And:
      return I->Ops[0]->Val & I->Ops[1]->Val;
    case Inst::Or:
      return I->Ops[0]->Val | I->Ops[1]->Val;
    case Inst::Xor:{
      return I->Ops[0]->Val ^ I->Ops[1]->Val;}
    case Inst::Trunc:
      return I->Ops[0]->Val.trunc(I->Width);
    case Inst::SExt:
     if (I->Ops[0]->Val == 0)
       return I->Ops[0]->Val.sext(I->Width);
     else
       return std::nullopt;
    case Inst::ZExt:
      if (I->Ops[0]->Val == 0)
       return I->Ops[0]->Val.zext(I->Width);
     else
       return std::nullopt;
    default: return std::nullopt;
  }
}

bool OpsConstP(Inst *I) {
  for (auto &&Op : I->Ops) {
    if (Op->K != Inst::Const) {
      return false;
    }
  }
  return true;
}

bool LHSZ(Inst *I) {
  return I->Ops.size() ==2 && I->Ops[0]->K == Inst::Const && I->Ops[0]->Val == 0;
}
bool RHSZ(Inst *I) {
  return I->Ops.size() ==2 && I->Ops[1]->K == Inst::Const && I->Ops[1]->Val == 0;
}
bool LHSM1(Inst *I) {
  return I->Ops.size() ==2 && I->Ops[0]->K == Inst::Const && I->Ops[0]->Val.isAllOnes();
}
bool RHSM1(Inst *I) {
  return I->Ops.size() ==2 && I->Ops[1]->K == Inst::Const && I->Ops[1]->Val.isAllOnes();
}

Inst *ConstantFoldingLiteImpl(InstContext &IC, Inst *I, std::set<Inst *> &Visited) {
  if (I->Ops.empty()) {
    return I;
  }
  if (Visited.find(I) != Visited.end()) {
    return I;
  } else {
    Visited.insert(I);
  }

  std::vector<Inst *> FoldedOps;
  for (auto Op : I->Ops) {
    FoldedOps.push_back(ConstantFoldingLiteImpl(IC, Op, Visited));
  }
  I->Ops = FoldedOps;

  if (OpsConstP(I)) {
    if (auto C = Fold(I)) {
      return IC.getConst(C.value());
    }
  }

  if (LHSZ(I)) {
    if (I->K == Inst::Add || I->K == Inst::Sub ||
        I->K == Inst::Xor || I->K == Inst::Or) {
      return I->Ops[1];
    }
    if (I->K == Inst::Mul || I->K == Inst::And) {
      return IC.getConst(llvm::APInt(I->Width, 0));
    }
  }

  if (RHSZ(I)) {
    if (I->K == Inst::Add || I->K == Inst::Sub ||
        I->K == Inst::Xor || I->K == Inst::Or) {
      return I->Ops[0];
    }
    if (I->K == Inst::Mul || I->K == Inst::And) {
      return IC.getConst(llvm::APInt(I->Width, 0));
    }
  }

  if (LHSM1(I)) {
    if (I->K == Inst::Mul || I->K == Inst::And) {
      return I->Ops[1];
    }
    if (I->K == Inst::Or) {
      return I->Ops[0];
    }
  }

  if (RHSM1(I)) {
    if (I->K == Inst::Mul || I->K == Inst::And) {
      return I->Ops[0];
    }
    if (I->K == Inst::Or) {
      return I->Ops[1];
    }
  }

  return I;
}

Inst *ConstantFoldingLite(InstContext &IC, Inst *I) {
  std::set<Inst *> Visited;
  return ConstantFoldingLiteImpl(IC, I, Visited);
}

std::vector<std::vector<Inst *>> InferSketchExprs(std::vector<Inst *> RHS,
                                                  ParsedReplacement Input,
                                                  InstContext &IC,
                                                  const std::map<Inst *, Inst *> &SymConstMap,
                                                  const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap) {
  std::vector<std::vector<Inst *>> Results;
  bool HasResults = false;
  for (auto Target : RHS) {
    auto Cands = ExtractSketchesSimple(IC, Input, SymConstMap, Target->Width);
    for (auto &C : Cands) {
      C = ConstantFoldingLite(IC, C);
    }
    Results.push_back(FilterExprsByValue(Cands, Target->Val, ConstMap));
    if (!Results.back().empty()) {
      HasResults = true;
    }
  }
  if (!HasResults) {
    return {};
  }
  return Results;
}



std::vector<std::vector<Inst *>> Enumerate(std::vector<Inst *> RHSConsts,
                                           std::set<Inst *> AtomicComps, InstContext &IC,
                                           const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap,
                                           size_t NumInsts = 1) {
    std::vector<std::vector<Inst *>> Candidates;

    std::vector<Inst *> Components;
    for (auto &&C : AtomicComps) {
      // if (C->Name == "symDF_DB") {
      //   continue;
      // }

      auto MinusOne = Builder(IC, llvm::APInt(1, 1)).SExt(C->Width)();

      // auto MinusOne = Builder(IC, llvm::APInt(C->Width, 1)).AShr(Builder(IC, C).BitWidth())();
      // auto MinusOne = Builder(IC, llvm::APInt::getAllOnesValue(C->Width))();
      Components.push_back(C);
      Components.push_back(Builder(C, IC).BSwap()());
      Components.push_back(Builder(C, IC).LogB()());

      if (C->Width != 1 && NumInsts < 2) {
        Components.push_back(Builder(C, IC).Sub(1)());
        Components.push_back(Builder(C, IC).Add(1)());

        auto TwoC = Builder(C, IC).Add(C);
        Components.push_back(TwoC.Flip()());
      }

      Components.push_back(Builder(C, IC).Xor(MinusOne)());

      Components.push_back(Builder(IC, MinusOne).Shl(C)());
      Components.push_back(Builder(IC, llvm::APInt(C->Width, 1)).Shl(C)());

      if (C->Width != 1 && C->K == Inst::Var) {
        Components.push_back(Builder(IC, C).BitWidth().Sub(1)());
        Components.push_back(Builder(IC, C).BitWidth().Sub(C)());
        auto CModWidth = Builder(IC, C).URem(Builder(IC, C).BitWidth());
        Components.push_back(CModWidth());
        Components.push_back(Builder(IC, C).BitWidth().Sub(CModWidth)());
      }

      for (auto &&C2 : AtomicComps) {
        if (C == C2) {
          continue;
        }
        auto UL = Builder(IC, C).Ult(C2);
        auto SL = Builder(IC, C).Slt(C2);

        Components.push_back(UL.Select(C, C2)());
        Components.push_back(SL.Select(C, C2)());
        // Components.push_back(ULT.Select(C2, C)());
        // Components.push_back(SLT.Select(C2, C)());
      }

    }

    std::set<size_t> VisitedWidths{1};
    for (auto &&C : AtomicComps) {
      if (VisitedWidths.find(C->Width) == VisitedWidths.end()) {
        VisitedWidths.insert(C->Width);
        auto MinusOne = Builder(IC, llvm::APInt(1, 1)).SExt(C->Width)();
        // Components.push_back(MinusOne);
        Components.push_back(Builder(IC, MinusOne).LShr(1)());
        Components.push_back(Builder(IC, MinusOne).Shl(1)());
        // Components.push_back(Builder(IC, MinusOne).Add(1)()); // zero
        Components.push_back(Builder(IC, MinusOne).Sub(1)());
      }
    }

    for (auto &&Target : RHSConsts) {
      std::vector<Inst *> CandsForTarget;
      for (auto Comp : Components) {
        if (Comp->Width == Target->Width) {
          CandsForTarget.push_back(Comp);
        }
      }
      EnumerativeSynthesis ES;
      auto Guesses = ES.generateExprs(IC, NumInsts, Components,
                                      Target->Width);
      for (auto &&Guess : Guesses) {
        std::set<Inst *> ConstSet;
        souper::getConstants(Guess, ConstSet);
        if (!ConstSet.empty()) {
          if (SymbolizeConstSynthesis) {
            CandsForTarget.push_back(Guess);
          }
        } else {
          CandsForTarget.push_back(Guess);
        }
      }
      // llvm::errs() << "HERE:\t" << Target->Val << "\n";
      Candidates.push_back(FilterExprsByValue(CandsForTarget, Target->Val, ConstMap));
      // Candidates.push_back(CandsForTarget);
    }
    return Candidates;
}

void findDangerousConstants(Inst *I, std::set<Inst *> &Results) {
  std::set<Inst *> Visited;
  std::vector<Inst *> Stack{I};
  while (!Stack.empty()) {
    auto Cur = Stack.back();
    Stack.pop_back();
    Visited.insert(Cur);

    // if (Cur->K == Inst::Const && Cur->Val == 0) {
    //   // Don't try to 'generalize' zero!
    //   Results.insert(Cur);
    // }

    if (Cur->K == Inst::Xor) {
      if (Cur->Ops[0]->K == Inst::Const) {
        if (Cur->Ops[0]->Val.isAllOnes()) {
          Results.insert(Cur->Ops[0]);
        }
      }
      if (Cur->Ops[1]->K == Inst::Const) {
        if (Cur->Ops[1]->Val.isAllOnes()) {
          Results.insert(Cur->Ops[1]);
        }
      }
    }

    if (Visited.find(Cur) == Visited.end()) {
      continue;
    }
    for (auto Child : Cur->Ops) {
      if (Cur->K == Inst::ExtractValue) {
        if (Child->K == Inst::Const) {
          // Constant operands of ExtractValue instructions
          Results.insert(Child);
        }
      }
      Stack.push_back(Child);
    }
  }
}

// TODO: memoize
bool hasMultiArgumentPhi(Inst *I) {
  if (I->K == Inst::Phi) {
    return I->Ops.size() > 1;
  }
  for (auto Op : I->Ops) {
    if (hasMultiArgumentPhi(Op)) {
      return true;
    }
  }
  return false;
}

ParsedReplacement ReducePoison(InstContext &IC,
  Solver *S, ParsedReplacement Input) {
  Reducer R(IC, S);
  return R.ReducePoison(Input);
}

ParsedReplacement ReduceBasic(InstContext &IC,
                              Solver *S, ParsedReplacement Input) {
  static Reducer R(IC, S);
  Input = R.ReducePCs(Input);
  Input = R.ReduceRedundantPhis(Input);
  Input = R.ReduceGreedy(Input);
  Input = R.ReduceBackwards(Input);
  Input = R.ReducePairsGreedy(Input);
  Input = R.ReduceTriplesGreedy(Input);
  Input = R.WeakenKB(Input);
  Input = R.WeakenCR(Input);
  Input = R.WeakenDB(Input);
  Input = R.WeakenOther(Input);
  if (ReduceKBIFY) {
    Input = R.ReduceGreedyKBIFY(Input);
  }
  Input = R.ReducePCs(Input);
  Input = R.ReducePCsToDF(Input);
  // Input = R.ReducePoison(Input);
  return Input;
}

ParsedReplacement DeAugment(InstContext &IC,
                            Solver *S, ParsedReplacement Augmented) {
  auto Result = ReduceBasic(IC, S, Augmented);
  Inst *SymDBVar = nullptr;
  if (Result.Mapping.LHS->K == Inst::DemandedMask) {
    SymDBVar = Result.Mapping.LHS->Ops[1];
  }

  if (!SymDBVar) {
    return Result;
  }

  if (SymDBVar->K == Inst::Const) {
    Result.Mapping.LHS = Result.Mapping.LHS->Ops[0];
    Result.Mapping.LHS->DemandedBits = SymDBVar->Val;
    Result.Mapping.RHS = Result.Mapping.RHS->Ops[0];
    return Result;
  }

  std::map<Inst *, size_t> LHSCount, RHSCount;
  CountUses(Result.Mapping.LHS, LHSCount);
  for (auto M : Result.PCs) {
    CountUses(M.LHS, LHSCount);
    CountUses(M.RHS, LHSCount);
  }
  CountUses(Result.Mapping.RHS, RHSCount);

  if (LHSCount[SymDBVar] == 1 && RHSCount[SymDBVar] == 1) {
    // We can remove the SymDBVar
    Result.Mapping.LHS = Result.Mapping.LHS->Ops[0];
    Result.Mapping.RHS = Result.Mapping.RHS->Ops[0];
    return Result;
  } else {
    return Result;
  }
}

// Assuming the input has leaves pruned and preconditions weakened
std::optional<ParsedReplacement> SuccessiveSymbolize(InstContext &IC,
                            Solver *S, ParsedReplacement Input, bool &Changed,
                            std::vector<std::pair<Inst *, llvm::APInt>> ConstMap = {}) {

  // Print first successful result and exit, no result sorting.
  // Prelude
  bool Nested = !ConstMap.empty();
  auto Original = Input;

  auto Fresh = Input;
  size_t ticks = std::clock();
  auto Refresh = [&] (auto Msg) {
    // Input = Clone(Fresh, IC);
    Input = Fresh;
    if (DebugLevel > 2) {
      auto now = std::clock();
      llvm::errs() << "POST " << Msg << " - " << (now - ticks)*1000/CLOCKS_PER_SEC << " ms\n";
      ticks = now;
    }
    Changed = true;
  };

  auto LHSConsts = findConcreteConsts(Input.Mapping.LHS);

  auto RHSConsts = findConcreteConsts(Input.Mapping.RHS);

  std::set<Inst *> ConstsBlackList;
  findDangerousConstants(Input.Mapping.LHS, ConstsBlackList);
  findDangerousConstants(Input.Mapping.RHS, ConstsBlackList);

  for (auto &&C : ConstsBlackList) {
    LHSConsts.erase(C);
    RHSConsts.erase(C);
  }

  ParsedReplacement Result = Input;

  std::map<Inst *, Inst *> SymConstMap;

  std::map<Inst *, Inst *> InstCache;

  std::map<Inst *, llvm::APInt> SymCS;

  if (Nested) {
    for (auto Pair : ConstMap) {
      SymCS.insert(Pair);
    }
  }

  static int i = 1;
  for (auto I : LHSConsts) {
    auto Name = "symconst_" + std::to_string(i++);
    SymConstMap[I] = IC.createVar(I->Width, Name);

    // llvm::errs() << "HERE : " << Name << '\t' << SymConstMap[I]->Name << "\n";

    InstCache[I] = SymConstMap[I];
    SymCS[SymConstMap[I]] = I->Val;
  }
  for (auto I : RHSConsts) {
    if (SymConstMap.find(I) != SymConstMap.end()) {
      continue;
    }
    auto Name = "symconst_" + std::to_string(i++);
    SymConstMap[I] = IC.createVar(I->Width, Name);
    InstCache[I] = SymConstMap[I];
//    SymCS[SymConstMap[I]] = I->Val;
  }

  std::vector<Inst *> RHSFresh; // RHSConsts - LHSConsts

  for (auto C : RHSConsts) {
    if (LHSConsts.find(C) == LHSConsts.end()) {
      RHSFresh.push_back(C);
    } else {
      if (C != *LHSConsts.find(C)) {
        RHSFresh.push_back(C);
      }
    }
  }

  Refresh("Prelude");
  // Step 1 : Just direct symbolize for common consts, no constraints

  std::map<Inst *, Inst *> CommonConsts;
  for (auto C : LHSConsts) {
    CommonConsts[C] = SymConstMap[C];

    // llvm::errs() << "Common Const: " << C->Val << "\t" << SymConstMap[C]->Name << "\n";

  }
  if (!CommonConsts.empty()) {
    Result = Replace(Result, IC, CommonConsts);
    auto Clone = Verify(Result, IC, S);
    if (Clone) {
      return Clone;
    }

    Clone = SimplePreconditionsAndVerifyGreedy(Result, IC, S, SymCS);
    if (Clone) {
      return Clone;
    }

//    Clone = DFPreconditionsAndVerifyGreedy(Result, IC, S, SymCS);
//    if (Clone.Mapping.LHS && Clone.Mapping.RHS) {
//      return Clone;
//    }

  }
  Refresh("Direct Symbolize for common consts");

  std::vector<std::pair<Inst *, llvm::APInt>> ConstMapCurrent;

  for (auto &&C : LHSConsts) {
    ConstMapCurrent.push_back({SymConstMap[C], C->Val});
  }

  for (auto &&P : ConstMap) {
    ConstMapCurrent.push_back(P);
  }
  ConstMap = ConstMapCurrent;

  std::vector<std::vector<Inst *>> SimpleCandidates =
    InferSpecialConstExprsAllSym(RHSFresh, ConstMap, IC, /*depth=*/ 2);

  if (!SimpleCandidates.empty()) {
    // if (DebugLevel > 4) {
    //   llvm::errs() << "InferSpecialConstExprsAllSym candidates: " << SimpleCandidates[0].size() << "\n";
    //   llvm::errs() << ConstMap.size() << "\n";
    //   llvm::errs() << RHSFresh.size() << "\n";
    // }
    auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidates,
                                       InstCache, IC, S, SymCS,
                                       true, false, false);
    if (Clone) {
      return Clone;
    }
  }
  Refresh("Special expressions, no constants, no constraints");

  for (auto C : LHSConsts) {

    std::map<Inst *, Inst *> TargetConstMap;
    TargetConstMap[C] = SymConstMap[C];
    auto Rep = Replace(Input, IC, TargetConstMap);

    auto Clone = Verify(Rep, IC, S);
    if (!Clone) {
      Clone = SimplePreconditionsAndVerifyGreedy(Result, IC, S, SymCS);
    }
    if (Clone) {
      bool changed = false;
      auto Gen = SuccessiveSymbolize(IC, S, Clone.value(), changed);
      return changed ? Gen : Clone;
    }
  }
  Refresh("Symbolize common consts, one by one");

  if (LHSConsts.size() >= 2 && LHSConsts.size() < 5) {
    for (auto C1 : LHSConsts) {
      for (auto C2 : LHSConsts) {
        if (C1 == C2 || C1->Width != C2->Width) {
          continue;
        }

        std::map<Inst *, Inst *> TargetConstMap;
        TargetConstMap[C1] = SymConstMap[C1];
        TargetConstMap[C2] = SymConstMap[C2];

        auto Rep = Replace(Input, IC, TargetConstMap);

        auto Clone = Verify(Rep, IC, S);

        if (Clone) {
          return Clone;
        }

        std::vector<std::pair<Inst *, llvm::APInt>> ValsMap;
        ValsMap.push_back({TargetConstMap[C1], SymCS[TargetConstMap[C1]]});
        ValsMap.push_back({TargetConstMap[C2], SymCS[TargetConstMap[C2]]});

        auto Relations = InferPotentialRelations(ValsMap, IC, Rep, {}, Nested);

        // for (auto R : Relations) {
        //   ReplacementContext RC;
        //   RC.printInst(R, llvm::errs(), true);
        //   llvm::errs() << "\n";
        // }

        Clone = VerifyWithRels(IC, S, Rep, Relations, SymCS);

        if (Clone) {
          return Clone;
        }

      }
    }
  }
  Refresh("Symbolize common consts, two at a time");

  // Step 1.5 : Direct symbolize, simple rel constraints on LHS

  auto CounterExamples = GetMultipleCEX(Result, IC, S, 3);
  if (Nested) {
    CounterExamples = {};
    // FIXME : Figure out how to get CEX for symbolic dataflow
  }

  // Input.print(llvm::errs(), true);
  // llvm::errs() << "LC " << LHSConsts.size() << "\n";
  // llvm::errs() << "RC " << RHSConsts.size() << "\n";
  // llvm::errs() << "RF " << RHSFresh.size() << "\n";

  // llvm::errs() << "CM " << ConstMap.size() << "\n";
  auto Relations = InferPotentialRelations(ConstMap, IC, Input, CounterExamples, Nested);
  // llvm::errs() << "Relations " << Relations.size() << "\n";

  std::map<Inst *, Inst *> JustLHSSymConstMap;

  for (auto &&C : LHSConsts) {
    JustLHSSymConstMap[C] = SymConstMap[C];
  }

  auto Copy = Replace(Input, IC, JustLHSSymConstMap);
  // for (auto &&R : Relations) {
  //   Copy.PCs.push_back({R, IC.getConst(llvm::APInt(1, 1))});
  //   // Copy.print(llvm::errs(), true);
  //   auto Clone = Verify(Copy, IC, S);
  //   if (Clone.Mapping.LHS && Clone.Mapping.RHS) {
  //     return Clone;
  //   }
  //   Copy.PCs.pop_back();
  // }

  // llvm::errs() << "Relations : " << Relations.size() << "\n";

  if (auto RelV = VerifyWithRels(IC, S, Copy, Relations)) {
    return RelV;
  }

  Refresh("Direct + simple rel constraints");

  // Step 2 : Symbolize LHS Consts with SimpleDF constrains
  // if (RHSFresh.empty()) {
    Copy = Replace(Input, IC, JustLHSSymConstMap);

    auto Clone = SimplePreconditionsAndVerifyGreedy(Copy, IC, S, SymCS);
    if (Clone) {
      return Clone;
    }

    if (Relations.size() < 100) {
      for (auto &&R : Relations) {
        Copy.PCs.push_back({R, IC.getConst(llvm::APInt(1, 1))});

        // InfixPrinter IP(Copy, true);
        // IP(llvm::errs());

        // Copy.print(llvm::errs(), true);

        auto Clone = SimplePreconditionsAndVerifyGreedy(Copy, IC, S, SymCS);
        if (Clone) {
          return Clone;
        }
        Copy.PCs.pop_back();
      }
    }
    Refresh("LHS with Rels");

  // }

  Refresh("All LHS Constraints");
  // Step 3 : Special RHS constant exprs, no constants

  if (!RHSFresh.empty()) {

  std::vector<std::vector<Inst *>> UnitaryCandidates =
    InferSpecialConstExprsAllSym(RHSFresh, ConstMap, IC, /*depth*/1);

  // llvm::errs() << "Unitary candidates: " << UnitaryCandidates[0].size() << "\n";

  if (!UnitaryCandidates.empty()) {
    // if (Nested && DebugLevel > 4) {
    //   llvm::errs() << "Rels " << Relations.size() << "\n";
    //   llvm::errs() << "Unitary candidates: " << UnitaryCandidates[0].size() << "\n";
    //   llvm::errs() << "FOO: " << UnitaryCandidates[0][0]->Name << "\n";
    // }

    // llvm::errs() << "Rels: " << Relations.size() << "\n";
    // for (auto I : Relations) {
    //   ReplacementContext RC;
    //   RC.printInst(I, llvm::errs(), true);
    //   llvm::errs() << "\n";
    // }
    auto Clone = FirstValidCombination(Input, RHSFresh, UnitaryCandidates,
                                  InstCache, IC, S, SymCS, true, false, false, Relations);
    if (Clone) {
      return Clone;
    }
    Refresh("Unitary cands, rel constraints");
  }

  // Step 4 : Enumerated expressions

  std::set<Inst *> Components;
  for (auto C : ConstMap) {
    Components.insert(C.first);
  }
  auto EnumeratedCandidates = Enumerate(RHSFresh, Components, IC, ConstMap);
  // if (DebugLevel > 4) {
  //   llvm::errs() << "ConstMap: " << ConstMap.size() << "\n";
  //   llvm::errs() << "RHSFresh: " << RHSFresh.size() << "\n";
  //   llvm::errs() << "Components: " << Components.size() << "\n";
  //   llvm::errs() << "EnumeratedCandidates: " << EnumeratedCandidates[0].size() << "\n";
  //   for (auto &&C : EnumeratedCandidates[0]) {
  //     ReplacementContext RC;
  //     RC.printInst(C, llvm::errs(), true);
  //   }

  //   llvm::errs() << "\n\nEnumeratedCandidates: " << EnumeratedCandidates[1].size() << "\n";
  //   for (auto &&C : EnumeratedCandidates[1]) {
  //     ReplacementContext RC;
  //     RC.printInst(C, llvm::errs(), true);
  //   }

  // }

  if (!EnumeratedCandidates.empty()) {
    auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidates,
                                  InstCache, IC, S, SymCS, true, false, false);
    if (Clone) {
      return Clone;
    }
    Refresh("Enumerated cands, no constraints");
  }

    // Step 4.75 : Enumerate 2 instructions when single RHS Constant.
  std::vector<std::vector<Inst *>> EnumeratedCandidatesTwoInsts;
  if (RHSFresh.size() == 1) {
    EnumeratedCandidatesTwoInsts = Enumerate(RHSFresh, Components, IC, ConstMap, 2);

    // llvm::errs() << "Guesses: " << EnumeratedCandidatesTwoInsts[0].size() << "\n";

    auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidatesTwoInsts,
                                  InstCache, IC, S, SymCS, true, false, false);
    if (Clone) {
      return Clone;
    }
  }
  Refresh("Enumerated 2 insts for single RHS const cases");

  if (!SimpleCandidates.empty()) {
    auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidates,
                                       InstCache, IC, S, SymCS,
                                       false, true, false);
    if (Clone) {
      return Clone;
    }
  }
  Refresh("Special expressions, simpledf constraints");

  if (!EnumeratedCandidates.empty()) {
    auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidates,
                                  InstCache, IC, S, SymCS, false, true, false);
    if (Clone) {
      return Clone;
    }

    // Enumerated Expressions with some relational constraints
    if (ConstMap.size() == 2) {
      // llvm::errs() << "Relations: " << Relations.size() << "\n";
      // llvm::errs() << "Guesses: " << EnumeratedCandidates[0].size() << "\n";

      auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidates,
                                          InstCache, IC, S, SymCS, true, false, false, Relations);
      if (Clone) {
        return Clone;
      }
    }
    Refresh("Relational constraints for enumerated cands.");

  }
  Refresh("Enumerated exprs with constraints");

  if (RHSFresh.size() == 1 && !Nested) {
    // Enumerated Expressions with some relational constraints
    if (ConstMap.size() == 2) {
      // llvm::errs() << "Enum2 : " << EnumeratedCandidatesTwoInsts.back().size()
      //              << "\tRels: " << Relations.size() << "\n";
      // for (auto I : Relations) {
      //   ReplacementContext RC;
      //   RC.printInst(I, llvm::errs(), true);
      // }

      // for (auto I : EnumeratedCandidatesTwoInsts.back()) {
      //   ReplacementContext RC;
      //   RC.printInst(I, llvm::errs(), true);
      //   llvm::errs() << "\n";
      // }

      auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidatesTwoInsts,
                                          InstCache, IC, S, SymCS, true, false, false, Relations);
      if (Clone) {
        return Clone;
      }
    }
  }
  Refresh("Enumerated 2 insts exprs with relations");

  // Step 4.8 : Special RHS constant exprs, with constants

  // std::vector<std::vector<Inst *>> SimpleCandidatesWithConsts =
  //   InferSpecialConstExprsWithConcretes(RHSFresh, ConstMap, IC, /*depth=*/ 2);

  // if (!SimpleCandidatesWithConsts.empty() && !Nested) {
  //   auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidatesWithConsts,
  //                                       InstCache, IC, S, SymCS,
  //                                       true, false, false);
  //   if (Clone) {
  //     return Clone;
  //   }
  // }

  // Refresh("Special expressions, with constants");


  // Enumerated exprs with constraints

  if (!EnumeratedCandidates.empty() && !Nested) {
    auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidates,
                                        InstCache, IC, S, SymCS, true, true, false, Relations);
    if (Clone) {
      return Clone;
    }
    Refresh("Enumerated exprs with constraints and relations");
  }

  if (!SimpleCandidates.empty()) {
    // Input.print(llvm::errs(), true);
    // llvm::errs() << SimpleCandidates.size() << "\n";
    // llvm::errs() << SimpleCandidates[0].size() << "\n";

    // for (auto &&C : SimpleCandidates[0]) {
    //   ReplacementContext RC;
    //   RC.printInst(C, llvm::errs(), true);
    //   llvm::errs() << "\n";
    // }

    auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidates,
                                       InstCache, IC, S, SymCS, false, true, false);
    if (Clone) {
      return Clone;
    }
    Refresh("Simple cands with constraints");

    Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidates,
                                        InstCache, IC, S, SymCS, true, false, false, Relations);
    if (Clone) {
      return Clone;
    }
    Refresh("Simple cands with constraints and relations");
  }

  // // Step 5.5 : Simple exprs with constraints

  // if (!SimpleCandidatesWithConsts.empty() && !Nested) {
  //   auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidatesWithConsts,
  //                                      InstCache, IC, S, SymCS, false, true, false);
  //   if (Clone) {
  //     return Clone;
  //   }
  //   Refresh("Simple cands+consts with constraints");

  //   Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidatesWithConsts,
  //                                       InstCache, IC, S, SymCS, true, true, false, Relations);
  //   if (Clone) {
  //     return Clone;
  //   }

  //   Refresh("Simple cands+consts with constraints and relations");
  // }

  // {
  //   if (!RHSFresh.empty()) {
  //     std::vector<std::vector<Inst *>> SimpleCandidatesMoreInsts =
  //       InferSpecialConstExprsAllSym(RHSFresh, ConstMap, IC, /*depth =*/ 5);

  //     if (!SimpleCandidates.empty()) {
  //       auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidatesMoreInsts,
  //                                         InstCache, IC, S, SymCS,
  //                                         true, false, false);
  //       if (Clone.Mapping.LHS && Clone.Mapping.RHS) {
  //         return Clone;
  //       }
  //     }

  //     Refresh("Special expressions, no constants");
  //   }
  // }

  std::vector<std::vector<Inst *>> SketchyCandidates =
    InferSketchExprs(RHSFresh, Input, IC, SymConstMap, ConstMap);

  if (!SketchyCandidates.empty()) {
    auto Clone = FirstValidCombination(Input, RHSFresh, SketchyCandidates,
                                       InstCache, IC, S, SymCS,
                                       true, false, false);
    if (Clone) {
      return Clone;
    }
  }
  Refresh("Sketches, no constraints");

  if (!SketchyCandidates.empty()) {
    auto Clone = FirstValidCombination(Input, RHSFresh, SketchyCandidates,
                                        InstCache, IC, S, SymCS, true, false, false, Relations);
    if (Clone) {
      return Clone;
    }
    Refresh("Sketchy cands with relations");
  }

  // if (!EnumeratedCandidates.empty()) {
  //   auto Clone = FirstValidCombination(Input, RHSFresh, EnumeratedCandidates,
  //                                       InstCache, IC, S, SymCS, true, true, false, ConstantLimits);
  //   if (Clone) {
  //     return Clone;
  //   }
  //   Refresh("Enumerated expressions+consts and constant limits");
  // }

  // if (!SimpleCandidates.empty()) {
  //     auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidates,
  //                                 InstCache, IC, S, SymCS, true, false, false, ConstantLimits);
  //   if (Clone) {
  //     return Clone;
  //   }
  // }
  // if (!SimpleCandidatesWithConsts.empty()) {
  //   auto Clone = FirstValidCombination(Input, RHSFresh, SimpleCandidatesWithConsts,
  //                                       InstCache, IC, S, SymCS, true, false, false, ConstantLimits);
  //   if (Clone) {
  //     return Clone;
  //   }
  //   Refresh("Simple expressions+consts and constant limits");
  // }

  }

  // {
  //   auto ConstantLimits = InferConstantLimits(ConstMap, IC, Input, CounterExamples);
  //   auto Copy = Replace(Input, IC, JustLHSSymConstMap);
  //   if (auto VRel = VerifyWithRels(IC, S, Copy, ConstantLimits)) {
  //     return VRel.value();
  //   }
  //   Refresh("Constant limit constraints on LHS");
  // }

  Refresh("END");
  Changed = false;
  return Input;
}


InstMapping GetEqWidthConstraint(Inst *I, size_t Width, InstContext &IC) {
  return {Builder(I, IC).BitWidth().Eq(Width)(), IC.getConst(llvm::APInt(1, 1))};
}

InstMapping GetLessThanWidthConstraint(Inst *I, size_t Width, InstContext &IC) {
  // Don't need to check for >0.
  return {Builder(I, IC).BitWidth().Ule(Width)(), IC.getConst(llvm::APInt(1, 1))};
}

InstMapping GetWidthRangeConstraint(Inst *I, size_t Min, size_t Max, InstContext &IC) {
  auto Right = Builder(I, IC).BitWidth().Ule(Max);
  auto Left = Builder(IC, llvm::APInt(I->Width, Min)).BitWidth().Ule(Builder(I, IC).BitWidth());
  return {Left.And(Right)(), IC.getConst(llvm::APInt(1, 1))};
}

// TODO: More as needed.

Inst *CombinePCs(const std::vector<InstMapping> &PCs, InstContext &IC) {
  Inst *Ante = IC.getConst(llvm::APInt(1, true));
  for (auto PC : PCs ) {
    Inst *Eq = IC.getInst(Inst::Eq, 1, {PC.LHS, PC.RHS});
    Ante = IC.getInst(Inst::And, 1, {Ante, Eq});
  }
  return Ante;
}

bool IsStaticallyWidthIndependent(ParsedReplacement Input) {
  std::vector<Inst *> Consts;
  auto Pred = [](Inst *I) {return I->K == Inst::Const;};
  findInsts(Input.Mapping.LHS, Consts, Pred);
  findInsts(Input.Mapping.RHS, Consts, Pred);
  for (auto M : Input.PCs) {
    findInsts(M.LHS, Consts, Pred);
    findInsts(M.RHS, Consts, Pred);
  }

  std::vector<Inst *> WidthChanges;
  auto WPred = [](Inst *I) {return I->K == Inst::Trunc || I->K == Inst::SExt
                                                 || I->K == Inst::ZExt;};

  findInsts(Input.Mapping.LHS, WidthChanges, WPred);
  findInsts(Input.Mapping.RHS, WidthChanges, WPred);
  for (auto M : Input.PCs) {
    findInsts(M.LHS, WidthChanges, WPred);
    findInsts(M.RHS, WidthChanges, WPred);
  }

  if (!WidthChanges.empty()) {
    return false;
  }

  for (auto &&C : Consts) {
    if (C->K == Inst::Const) {
      if (C->Val != 0 && !C->Val.isAllOnes() && C->Val != 1) {
        return false;
      }
    }
  }

  std::vector<Inst *> Vars;
  findVars(Input.Mapping.LHS, Vars);
  for (auto &&V : Vars) {
    if (V->Width == 1) {
      return false;
    }
  }

  return true;
}

void GetWidthChangeInsts(Inst *I, std::vector<Inst *> &WidthChanges) {
  findInsts(I, WidthChanges, [](Inst *I) {
    return I->K == Inst::Trunc || I->K == Inst::SExt || I->K == Inst::ZExt;});
}

bool hasConcreteDataflowConditions(ParsedReplacement &Input) {
  std::vector<Inst *> Inputs;
  findVars(Input.Mapping.LHS, Inputs);

  for (auto &&V : Inputs) {
    if (!V->Range.isFullSet()) {
      return true;
    }
    if (V->KnownOnes.getBitWidth() == V->Width && V->KnownOnes != 0) {
      return true;
    }

    if (V->KnownZeros.getBitWidth() == V->Width && V->KnownZeros != 0) {
      return true;
    }
  }

  if (Input.Mapping.LHS->DemandedBits.getBitWidth() == Input.Mapping.LHS->Width &&
      !Input.Mapping.LHS->DemandedBits.isAllOnesValue()) {
    return true;
  }
  return false;
}

ParsedReplacement ReplaceMinusOneAndFamily(InstContext &IC, ParsedReplacement Input) {
  std::map<Inst *, Inst *> Map;
  for (size_t i = 2; i <= 64; ++i) {
    Map[IC.getConst(llvm::APInt::getAllOnesValue(i))] =
      Builder(IC, llvm::APInt(1, 1)).SExt(i)();
    Map[IC.getConst(llvm::APInt::getAllOnesValue(i) - 1)] =
      Builder(IC, llvm::APInt(1, 1)).SExt(i).Sub(1)();
    Map[IC.getConst(llvm::APInt::getSignedMaxValue(i))] =
      Builder(IC, llvm::APInt(1, 1)).SExt(i).LShr(1)();
    Map[IC.getConst(llvm::APInt::getSignedMinValue(i))] =
      Builder(IC, llvm::APInt(1, 1)).SExt(i).LShr(1).Flip()();
  }
  return Replace(Input, IC, Map);
}

std::pair<ParsedReplacement, bool>
InstantiateWidthChecks(InstContext &IC,
  Solver *S, ParsedReplacement Input) {

  // llvm::errs() << "A\n";
  // {InfixPrinter IP(Input); IP(llvm::errs()); llvm::errs() << "\n";}

  Input = ReplaceMinusOneAndFamily(IC, Input);

  // llvm::errs() << "B\n";
  // {InfixPrinter IP(Input); IP(llvm::errs()); llvm::errs() << "\n";}

  if (IsStaticallyWidthIndependent(Input)) {
    return {Input, true};
  }

  if (!NoWidth && !hasMultiArgumentPhi(Input.Mapping.LHS) && !hasConcreteDataflowConditions(Input)) {
    // Instantiate Alive driver with Symbolic width.
    AliveDriver Alive(Input.Mapping.LHS,
    Input.PCs.empty() ? nullptr : CombinePCs(Input.PCs, IC),
    IC, {}, true);

    // Find set of valid widths.
    if (Alive.verify(Input.Mapping.RHS)) {
      if (DebugLevel > 4) {
        llvm::errs() << "WIDTH: Generalized opt is valid for all widths.\n";
      }
      // Completely width independent.

      // Only width == 1 checks needed
      std::set<Inst *> Visited;
      std::vector<Inst *> Stack{Input.Mapping.LHS, Input.Mapping.RHS};
      // DFS to visit all instructions.

      std::vector<Inst *> WidthChangeInsts;
      std::set<Inst *> WISet;
      GetWidthChangeInsts(Input.Mapping.LHS, WidthChangeInsts);
      for (auto &&I : WidthChangeInsts) {
        WISet.insert(I);
      }

      while (!Stack.empty()) {
        auto I = Stack.back();
        Stack.pop_back();
        if (Visited.count(I)) {
          continue;
        }

        if (I->Width == 1 && WISet.find(I) != WISet.end()) {
          Input.PCs.push_back(GetEqWidthConstraint(I, I->Width, IC));
        }

        Visited.insert(I);
        for (auto Op : I->Ops) {
          Stack.push_back(Op);
        }
      }

      return {Input, true};
    }

    auto &&ValidTypings = Alive.getValidTypings();
    if (ValidTypings.empty() && !Alive.getInvalidTypings().empty()) {
      // Something went wrong, generalized opt is not valid at any width.
      if (DebugLevel > 4) {
        llvm::errs() << "WIDTH: Generalized opt is not valid for any width.\n";
      }
      Input.Mapping.LHS = nullptr;
      Input.Mapping.RHS = nullptr;
      return {Input, false};
    }

    if (ValidTypings.empty() && Alive.getInvalidTypings().empty()) {
      // Something went wrong, Alive didn't generate typing assignments.
      if (DebugLevel > 4) {
        llvm::errs() << "Alive didn't generate typing assignments.\n";
      }

    }


  // Abstract width to a range or relational precondition
  // TODO: Abstraction

    std::vector<Inst *> Inputs;
    findVars(Input.Mapping.LHS, Inputs);
    if (Inputs.size() == 1 && ValidTypings.size() > 1) {
      auto I = Inputs[0];
      auto Width = I->Width;

      std::vector<size_t> Widths;
      for (auto &&V : ValidTypings) {
        Widths.push_back(V[I]);
      }

      size_t MaxWidth = *std::max_element(Widths.begin(), Widths.end());
      size_t MinWidth = *std::min_element(Widths.begin(), Widths.end());

      if (ValidTypings.size() == (MaxWidth - MinWidth + 1)) {
        Input.PCs.push_back(GetWidthRangeConstraint(I, MinWidth, MaxWidth, IC));
        return {Input, false};
      }
    }

  }
  // If abstraction fails, insert checks for existing widths.
  std::vector<Inst *> Inputs;
  findVars(Input.Mapping.LHS, Inputs);
  for (auto &&I : Inputs) {
    Input.PCs.push_back(GetEqWidthConstraint(I, I->Width, IC));
  }
  std::vector<Inst *> WidthChangeInsts;
  GetWidthChangeInsts(Input.Mapping.LHS, WidthChangeInsts);
  for (auto &&I : WidthChangeInsts) {
    if (I->K != Inst::Const) {
      Input.PCs.push_back(GetEqWidthConstraint(I, I->Width, IC));
    }
  }
  return {Input, false};
}

std::optional<ParsedReplacement> ShrinkRep(ParsedReplacement &Input,
                                            InstContext &IC,
                                            Solver *S) {
  if (hasMultiArgumentPhi(Input.Mapping.LHS)) {
    return std::nullopt;
  }
  ShrinkWrap Shrink(IC, S, Input, 8);
  return Shrink();
}

std::optional<ParsedReplacement> GeneralizeShrinked(
  ParsedReplacement Input, InstContext &IC, Solver *S) {

  if (hasMultiArgumentPhi(Input.Mapping.LHS)) {
    return std::nullopt;
  }

  ShrinkWrap Shrink(IC, S, Input, 8);

  // Input.print(llvm::errs(), true);

  auto Smol = Shrink();

  if (Smol) {
    if (DebugLevel > 2) {
      llvm::errs() << "Shrinked: \n";
      InfixPrinter P(Smol.value());
      P(llvm::errs());
      Smol->print(llvm::errs(), true);
      llvm::errs() << "\n";
      if (DebugLevel > 4) {
        Smol.value().print(llvm::errs(), true);
      }
    }
    Input = Smol.value();

    // Input.print(llvm::errs(), true);

  } else {
    if (DebugLevel > 2) {
      llvm::errs() << "Shrinking failed\n";
    }
    return std::nullopt;
  }

  bool Changed = false;

  auto Gen = SuccessiveSymbolize(IC, S, Smol.value(), Changed);

  if (!Changed || !Gen) {
    if (DebugLevel > 2) {
      llvm::errs() << "Shrinking failed\n";
    }
    return std::nullopt; // Generalization failed.
  }

  auto [GenWidth, WidthChanged] = InstantiateWidthChecks(IC, S, Gen.value());

  if (!WidthChanged) {
    return std::nullopt; // Width independence check failed.
  }
  return Gen;
}

void PrintInputAndResult(ParsedReplacement Input, ParsedReplacement Result) {
  ReplacementContext RC;
  Result.printLHS(llvm::outs(), RC, true);
  Result.printRHS(llvm::outs(), RC, true);
  llvm::outs() << "\n";

  if (DebugLevel > 1) {
      llvm::errs() << "IR Input: \n";
    ReplacementContext RC;
    Input.printLHS(llvm::errs(), RC, true);
    Input.printRHS(llvm::errs(), RC, true);
    llvm::errs() << "\n";
    llvm::errs() << "\n\tInput (profit=" << profit(Input) <<  "):\n\n";
    InfixPrinter IP(Input);
    IP(llvm::errs());
    llvm::errs() << "\n\tGeneralized (profit=" << profit(Result) << "):\n\n";
    InfixPrinter IP2(Result, NoWidth);
    IP2(llvm::errs());
    llvm::errs() << "\n";
    // Result.print(llvm::errs(), true);
  }
  llvm::outs().flush();
}

std::optional<ParsedReplacement> GeneralizeRep(ParsedReplacement &Input,
                                            InstContext &IC, Solver *S) {

    if (Input.Mapping.LHS == Input.Mapping.RHS) {
    if (DebugLevel > 4)  llvm::errs() << "Input == Output\n";
      return std::nullopt;
    } else if (profit(Input) < 0 && !IgnoreCost) {
      if (DebugLevel > 4) llvm::errs() << "Not an optimization\n";
      return std::nullopt;
    } else if (!Verify(Input, IC, S)) {
      if (DebugLevel > 4) llvm::errs() << "Invalid Input.\n";
      return std::nullopt;
    }

  ParsedReplacement Result = ReduceBasic(IC, S, Input);

  bool Changed = false;
  size_t MaxTries = 1; // Increase this if we ever run with 10/100x timeout.
  bool FirstTime = true;
  if (!OnlyWidth) {
    if (Changed) {
      Result = ReduceBasic(IC, S, Result);
    }

    std::optional<ParsedReplacement> Opt;
    if (!NoWidth) {
      Opt = GeneralizeShrinked(Result, IC, S);
    }

    if (!Opt) {
      Opt = SuccessiveSymbolize(IC, S, Result, Changed);
    } else {
      Changed = true;
    }

    if (Opt) {
      Result = *Opt;
    }

    // if (Changed && Opt) {
    //   PrintInputAndResult(Input, Result);
    // }

    if (SymbolicDF) {
      if (DebugLevel > 4) {
        Result.print(llvm::errs(), true);
      }

      if (DebugLevel > 4) llvm::errs() << "PUSH SYMDF_KB_DB\n";
      auto [CM, Aug] = AugmentForSymKBDB(Result, IC);

      if (DebugLevel > 4) {
        Aug.print(llvm::errs(), true);
      }

      // auto [CM2, Aug2] = AugmentForSymKB(Aug1, IC);
      if (!CM.empty()) {
        bool SymDFChanged = false;

        auto Clone = Verify(Aug, IC, S);
        if (Clone) {
          Result = ReduceBasic(IC, S, Clone.value());
          Result = DeAugment(IC, S, Result);
          SymDFChanged = true;
          if (DebugLevel > 4) llvm::errs() << "MSG Unconstrained SYMDF\n";
        } else {
          auto Generalized = SuccessiveSymbolize(IC, S, Aug, SymDFChanged, CM);
          if (Generalized && SymDFChanged) {
            Result = DeAugment(IC, S, Generalized.value());
            Changed = true;
            if (DebugLevel > 4) llvm::errs() << "MSG Synth SYMDF\n";
          }
        }
      }
      if (DebugLevel > 4) llvm::errs() << "POP SYMDF_KB_DB\n";
    }

  }
  bool Indep = false;
  if (!NoWidth) {
    std::tie(Result, Indep) = InstantiateWidthChecks(IC, S, Result);
  }
  return Result;
}
}