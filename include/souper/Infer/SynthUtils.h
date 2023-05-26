#ifndef SOUPER_SYNTH_UTILS_H
#define SOUPER_SYNTH_UTILS_H

#include "souper/Inst/Inst.h"
#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/ConstantSynthesis.h"
#include "souper/Parser/Parser.h"
#include "souper/Infer/Pruning.h"
#include <sstream>
namespace souper {

// TODO: Lazy construction instead of eager.
// eg: Instead of Builder(I, IC).Add(1)()
// we could do Builder(I).Add(1)(IC)
class Builder {
public:
  Builder(Inst *I_, InstContext &IC_) : I(I_), IC(IC_) {}
  Builder(InstContext &IC_, Inst *I_) : I(I_), IC(IC_) {}
  Builder(InstContext &IC_, llvm::APInt Value) : IC(IC_) {
    I = IC.getConst(Value);
  }
  Builder(Inst *I_, InstContext &IC_, uint64_t Value) : IC(IC_) {
    I = IC.getConst(llvm::APInt(I_->Width, Value));
  }

  Inst *operator()() {
    assert(I);
    return I;
  }

#define BINOP(K)                                                 \
  template<typename T> Builder K(T t) {                          \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::K, L->Width, {L, R}), IC);   \
  }

  BINOP(Add) BINOP(Sub) BINOP(Mul)
  BINOP(And) BINOP(Xor) BINOP(Or)
  BINOP(Shl) BINOP(LShr) BINOP(UDiv)
  BINOP(SDiv)
#undef BINOP

  template<typename T> Builder Ugt(T t) {                        \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::Ult, 1, {R, L}), IC); \
  }

#define BINOPW(K)                                                \
  template<typename T> Builder K(T t) {                          \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::K, 1, {L, R}), IC);          \
  }
  BINOPW(Slt) BINOPW(Ult) BINOPW(Sle) BINOPW(Ule)
  BINOPW(Eq) BINOPW(Ne)
#undef BINOPW

#define UNOP(K)                                                  \
  Builder K() {                                                  \
    auto L = I;                                                  \
    return Builder(IC.getInst(Inst::K, L->Width, {L}), IC);      \
  }
  UNOP(LogB) UNOP(BitReverse) UNOP(BSwap) UNOP(Cttz) UNOP(Ctlz)
  UNOP(BitWidth) UNOP(CtPop)
#undef UNOP

  Builder Flip() {
    auto L = I;
    auto AllOnes = IC.getConst(llvm::APInt::getAllOnesValue(L->Width));
    return Builder(IC.getInst(Inst::Xor, L->Width, {L, AllOnes}), IC);
  }
  Builder Negate() {
    auto L = I;
    auto Zero = IC.getConst(llvm::APInt(L->Width, 0));
    return Builder(IC.getInst(Inst::Sub, L->Width, {Zero, L}), IC);
  }

#define UNOPW(K)                                                 \
  Builder K(size_t W) {                                          \
    auto L = I;                                                  \
    return Builder(IC.getInst(Inst::K, W, {L}), IC);             \
  }
  UNOPW(ZExt) UNOPW(SExt) UNOPW(Trunc)
#undef UNOPW

private:
  Inst *I = nullptr;
  InstContext &IC;

  Inst *i(Builder A, Inst *I) {
    assert(A.I);
    return A.I;
  }

  template<typename N>
  Inst *i(N Number, Builder B) {
    return B.IC.getConst(llvm::APInt(B.I->Width, Number, false));
  }

  template<>
  Inst *i<Inst *>(Inst *I, Builder B) {
    assert(I);
    return I;
  }

  template<>
  Inst *i<Builder>(Builder A, Builder B) {
    assert(A.I);
    return A.I;
  }

  template<>
  Inst *i<std::string>(std::string Number, Builder B) {
    return B.IC.getConst(llvm::APInt(B.I->Width, Number, 10));
  }

  template<>
  Inst *i<llvm::APInt>(llvm::APInt Number, Builder B) {
    return B.IC.getConst(Number);
  }
};

Inst *Replace(Inst *R, InstContext &IC, std::map<Inst *, Inst *> &M);
ParsedReplacement Replace(ParsedReplacement I, InstContext &IC,
                          std::map<Inst *, Inst *> &M);

Inst *Replace(Inst *R, InstContext &IC, std::map<Inst *, llvm::APInt> &ConstMap);
ParsedReplacement Replace(ParsedReplacement I, InstContext &IC,
                          std::map<Inst *, llvm::APInt> &ConstMap);

Inst *Clone(Inst *R, InstContext &IC);

InstMapping Clone(InstMapping In, InstContext &IC);

ParsedReplacement Clone(ParsedReplacement In, InstContext &IC);

// Also Synthesizes given constants
// Returns clone if verified, nullptrs if not
std::optional<ParsedReplacement> Verify(ParsedReplacement Input, InstContext &IC, Solver *S);
// bool IsValid(ParsedReplacement Input, InstContext &IC, Solver *S);

std::map<Inst *, llvm::APInt> findOneConstSet(ParsedReplacement Input, const std::set<Inst *> &SymCS, InstContext &IC, Solver *S);

std::vector<std::map<Inst *, llvm::APInt>> findValidConsts(ParsedReplacement Input, const std::set<Inst *> &Insts, InstContext &IC, Solver *S, size_t MaxCount);

ValueCache GetCEX(const ParsedReplacement &Input, InstContext &IC, Solver *S);

std::vector<ValueCache> GetMultipleCEX(ParsedReplacement Input, InstContext &IC, Solver *S, size_t MaxCount);

int profit(const ParsedReplacement &P);

struct InfixPrinter {
  InfixPrinter(ParsedReplacement P_, bool ShowImplicitWidths = true);

  void registerWidthConstraints();

  void registerSymDBVar();

  bool registerSymDFVars(Inst *I);

  void countUses(Inst *I);

  template<typename Stream>
  void operator()(Stream &S) {
    if (!P.PCs.empty()) {
      printPCs(S);
      S << "\n  |= \n";
    }
    S << printInst(P.Mapping.LHS, S, true);
    if (!P.Mapping.LHS->DemandedBits.isAllOnesValue()) {
      S << " (" << "demandedBits="
       << Inst::getDemandedBitsString(P.Mapping.LHS->DemandedBits)
       << ")";
    }
    S << "\n  =>\n";

    S << printInst(P.Mapping.RHS, S, true) << "\n";
  }

  template<typename Stream>
  std::string printInst(Inst *I, Stream &S, bool Root = false) {
    if (Syms.count(I)) {
      return Syms[I];
    }

    std::ostringstream OS;

    if (UseCount[I] > 1) {
      std::string Name = "var" + std::to_string(varnum++);
      Syms[I] = Name;
      OS << "let " << Name << " = ";
    }

    // x ^ -1 => ~x
    if (I->K == Inst::Xor && I->Ops[1]->K == Inst::Const &&
        I->Ops[1]->Val.isAllOnesValue()) {
      return "~" + printInst(I->Ops[0], S);
    }
    if (I->K == Inst::Xor && I->Ops[0]->K == Inst::Const &&
        I->Ops[0]->Val.isAllOnesValue()) {
      return "~" + printInst(I->Ops[1], S);
    }

    if (I->K == Inst::Const) {
      if (I->Val.ule(16)) {
        return llvm::toString(I->Val, 10, false);
      } else {
        return "0x" + llvm::toString(I->Val, 16, false);
      }
    } else if (I->K == Inst::Var) {
      auto Name = I->Name;
      if (isdigit(Name[0])) {
        Name = "x" + Name;
      }
      if (I->Name.starts_with("symconst_")) {
        Name = "C" + I->Name.substr(9);
      }
      if (VisitedVars.count(I->Name)) {
        return Name;
      } else {
        VisitedVars.insert(I->Name);
        Inst::getKnownBitsString(I->KnownZeros, I->KnownOnes);

        std::string Buf;
        llvm::raw_string_ostream Out(Buf);

        if (I->KnownZeros.getBoolValue() || I->KnownOnes.getBoolValue())
          Out << " (knownBits=" << Inst::getKnownBitsString(I->KnownZeros, I->KnownOnes)
              << ")";
        if (I->NonNegative)
          Out << " (nonNegative)";
        if (I->Negative)
          Out << " (negative)";
        if (I->NonZero)
          Out << " (nonZero)";
        if (I->PowOfTwo)
          Out << " (powerOfTwo)";
        if (I->NumSignBits > 1)
          Out << " (signBits=" << I->NumSignBits << ")";
        if (!I->Range.isFullSet())
          Out << " (range=[" << I->Range.getLower()
              << "," << I->Range.getUpper() << "))";

        std::string W = ShowImplicitWidths ? ":i" + std::to_string(I->Width) : "";

        if (WidthConstraints.count(I)) {
          W = ":i" + std::to_string(WidthConstraints[I]);
        }

        return Name + W + Out.str();
      }
    } else {
      std::string Op;
      switch (I->K) {
      case Inst::Add: Op = "+"; break;
      case Inst::AddNSW: Op = "+nsw"; break;
      case Inst::AddNUW: Op = "+nuw"; break;
      case Inst::AddNW: Op = "+nw"; break;
      case Inst::Sub: Op = "-"; break;
      case Inst::SubNSW: Op = "-nsw"; break;
      case Inst::SubNUW: Op = "-nuw"; break;
      case Inst::SubNW: Op = "-nw"; break;
      case Inst::Mul: Op = "*"; break;
      case Inst::MulNSW: Op = "*nsw"; break;
      case Inst::MulNUW: Op = "*nuw"; break;
      case Inst::MulNW: Op = "*nw"; break;
      case Inst::UDiv: Op = "/u"; break;
      case Inst::SDiv: Op = "/s"; break;
      case Inst::URem: Op = "\%u"; break;
      case Inst::SRem: Op = "\%s"; break;
      case Inst::And: Op = "&"; break;
      case Inst::Or: Op = "|"; break;
      case Inst::Xor: Op = "^"; break;
      case Inst::Shl: Op = "<<"; break;
      case Inst::ShlNSW: Op = "<<nsw"; break;
      case Inst::ShlNUW: Op = "<<nuw"; break;
      case Inst::ShlNW: Op = "<<nw"; break;
      case Inst::LShr: Op = ">>l"; break;
      case Inst::AShr: Op = ">>a"; break;
      case Inst::Eq: Op = "=="; break;
      case Inst::Ne: Op = "!="; break;
      case Inst::Ult: Op = "<u"; break;
      case Inst::Slt: Op = "<s"; break;
      case Inst::Ule: Op = "<=u"; break;
      case Inst::Sle: Op = "<=s"; break;
      case Inst::KnownOnesP : Op = "<<=1"; break;
      case Inst::KnownZerosP : Op = "<<=0"; break;
      default: Op = Inst::getKindName(I->K); break;
      }

      std::string Result;

      std::vector<Inst *> Ops = I->orderedOps();

      if (Inst::isCommutative(I->K)) {
        std::sort(Ops.begin(), Ops.end(), [](Inst *A, Inst *B) {
          if (A->K == Inst::Const) {
            return false; // c OP expr
          } else if (B->K == Inst::Const) {
            return true; // expr OP c
          } else if (A->K == Inst::Var && B->K != Inst::Var) {
            return true; // var OP expr
          } else if (A->K != Inst::Var && B->K == Inst::Var) {
            return false; // expr OP var
          } else if (A->K == Inst::Var && B->K == Inst::Var) {
            return A->Name > B->Name; // Tends to put vars before symconsts
          } else {
            return A->K < B->K; // expr OP expr
          }
        });
      }

      if (Ops.size() == 2) {
        auto Meat = printInst(Ops[0], S) + " " + Op + " " + printInst(Ops[1], S);
        Result = Root ? Meat : "(" + Meat + ")";
      } else if (Ops.size() == 1) {
        Result = Op + "(" + printInst(Ops[0], S) + ")";
      }
      else {
        std::string Ret = Root ? "" : "(";
        Ret += Op;
        Ret += " ";
        for (auto &&Op : Ops) {
          Ret += printInst(Op, S) + " ";
        }
        while (Ret.back() == ' ') {
          Ret.pop_back();
        }
        if (!Root) {
          Ret += ")";
        }
        Result = Ret;
      }
      if (UseCount[I] > 1) {
        OS << Result << ";\n";
        S << OS.str();
        return Syms[I];
      } else {
        return Result;
      }
    }
  }

  template<typename Stream>
  void printPCs(Stream &S) {
    bool first = true;
    for (auto &&PC : P.PCs) {
      // if (PC.LHS->K == Inst::KnownOnesP || PC.LHS->K == Inst::KnownZerosP) {
      //   continue;
      // }
      if (first) {
        first = false;
      } else {
        S << " && \n";
      }
      if (PC.RHS->K == Inst::Const && PC.RHS->Val == 0) {
        S << "!(" << printInst(PC.LHS, S, true) << ")";
      } else if (PC.RHS->K == Inst::Const && PC.RHS->Val == 1) {
        S << printInst(PC.LHS, S, true);
      } else {
        S << printInst(PC.LHS, S, true) << " == " << printInst(PC.RHS, S);
      }
    }
  }

  ParsedReplacement P;
  std::set<std::string> VisitedVars;
  std::map<Inst *, std::string> Syms;
  size_t varnum;
  std::map<Inst *, size_t> UseCount;
  std::map<Inst *, size_t> WidthConstraints;
  bool ShowImplicitWidths;
};


}
#endif
