#ifndef SOUPER_SYNTH_UTILS_H
#define SOUPER_SYNTH_UTILS_H

#include "souper/Inst/Inst.h"
#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/ConstantSynthesis.h"
#include "souper/Parser/Parser.h"
#include "souper/Infer/Pruning.h"
#include <sstream>
#include "llvm/ADT/StringExtras.h"
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

  template<typename T, typename F> Builder Select(T t, F f) {
    auto left = i(t, *this);
    auto right = i(f, *this);
    return Builder(IC.getInst(Inst::Select, 1, {I, left, right}), IC);
  }

#define BINOP(K)                                                 \
  template<typename T> Builder K(T t) {                          \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::K, L->Width, {L, R}), IC);   \
  }

  BINOP(Add) BINOP(Sub) BINOP(Mul)
  BINOP(And) BINOP(Xor) BINOP(Or)
  BINOP(Shl) BINOP(LShr) BINOP(UDiv)
  BINOP(SDiv) BINOP(AShr) BINOP(URem)
  BINOP(SRem)
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
    // auto AllOnes = IC.getConst(llvm::APInt::getAllOnes(L->Width));
    auto AllOnes = Builder(IC, llvm::APInt(1, 1)).SExt(L->Width)();
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

struct GoPrinter {
  GoPrinter(ParsedReplacement P_) : P(P_) {}

  template<typename Stream>
  void operator()(Stream &S) {

    bool first = true;
    for (auto &&PC : P.PCs) {
      if (first) {
        first = false;
      } else {
        S << " && \n";
      }
      if (PC.RHS->K == Inst::Const && PC.RHS->Val == 0) {
        S << "!(" << printInst(PC.LHS) << ")";
      } else if (PC.RHS->K == Inst::Const && PC.RHS->Val == 1) {
        S << printInst(PC.LHS);
      } else {
        S << "(= " << printInst(PC.LHS) << " " << printInst(PC.RHS) << ")";
      }
    }

    if (!P.PCs.empty()) {
      S << " |= ";
    }


    S << printInst(P.Mapping.LHS) << " -> "
      << printInst(P.Mapping.RHS) << "\n\n";
  }

  std::string printInst(Inst *I) {
    std::string Result = "";
    if (I->K == Inst::Var) {
      if (I->Name.starts_with("symconst_")) {
        auto Name = "C" + I->Name.substr(9);
        Result += Name;
      } else {
        Result += I->Name;
      }
      std::ostringstream Out;
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
        Out << " (range=[" << llvm::toString(I->Range.getLower(), 10, false)
            << "," << llvm::toString(I->Range.getUpper(), 10, false) << "))";

      Result += Out.str();
    } else if (I->K == Inst::Const) {
      Result += llvm::toString(I->Val, 10, false);
    } else {
      Result = "(";
      Result += Inst::getKindName(I->K);
      Result += ' ';
      for (auto Child : I->Ops) {
        Result += printInst(Child);
        Result += ' ';
      }
      Result += ')';
    }
    return Result;
  }
  ParsedReplacement P;
};

struct InfixPrinter {
  InfixPrinter(ParsedReplacement P_, bool ShowImplicitWidths = true);

  void registerWidthConstraints();

  void registerSymDBVar();

  bool registerSymDFVars(Inst *I);

  void countUses(Inst *I);

  virtual void operator()(llvm::raw_ostream &S) {
    if (!P.PCs.empty()) {
      printPCs(S);
      S << "\n  |= \n";
    }
    S << printInst(P.Mapping.LHS, S, true);
    if (!P.Mapping.LHS->DemandedBits.isAllOnes()) {
      S << " (" << "demandedBits="
       << Inst::getDemandedBitsString(P.Mapping.LHS->DemandedBits)
       << ")";
    }
    S << "\n  =>";
    if (!P.Mapping.RHS) {
      S << " ? \n";
    } else {
      S << "\n";
      S << printInst(P.Mapping.RHS, S, true) << "\n";
    }
  }

  virtual std::string printInst(Inst *I, llvm::raw_ostream &S, bool Root = false) {
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
        I->Ops[1]->Val.isAllOnes()) {
      return "~" + printInst(I->Ops[0], S);
    }
    if (I->K == Inst::Xor && I->Ops[0]->K == Inst::Const &&
        I->Ops[0]->Val.isAllOnes()) {
      return "~" + printInst(I->Ops[1], S);
    }

    if (I->K == Inst::Const) {
      if (I->Val.ule(64)) {
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

  virtual void printPCs(llvm::raw_ostream &S) {
    bool first = true;
    for (auto &&PC : P.PCs) {
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

struct LatexPrinter : public InfixPrinter {
  LatexPrinter(ParsedReplacement P, bool ShowImplicitWidths = true) : InfixPrinter(P, ShowImplicitWidths) {}
  void operator() (llvm::raw_ostream &S) override {
    if (!P.PCs.empty()) {
      printPCs(S);
      S << " \\models ";
    }
    S << printInst(P.Mapping.LHS, S, true);
    if (!P.Mapping.LHS->DemandedBits.isAllOnes()) {
      S << " (" << "\\text{demandedBits} ="
       << Inst::getDemandedBitsString(P.Mapping.LHS->DemandedBits)
       << ")";
    }
    S << " \\Rightarrow ";
    if (!P.Mapping.RHS) {
      S << " ?";
    } else {
      S << "";
      S << printInst(P.Mapping.RHS, S, true) << "\n";
    }
  }

  void printPCs(llvm::raw_ostream &S) override {
    bool first = true;
    for (auto &&PC : P.PCs) {
      if (first) {
        first = false;
      } else {
        S << " \\land ";
      }
      if (PC.RHS->K == Inst::Const && PC.RHS->Val == 0) {
        S << "(" << printInst(PC.LHS, S, true) << ") = 0";
      } else if (PC.RHS->K == Inst::Const && PC.RHS->Val == 1) {
        S << printInst(PC.LHS, S, true);
      } else {
        S << printInst(PC.LHS, S, true) << " = " << printInst(PC.RHS, S);
      }
    }
  }

  virtual std::string printInst(Inst *I, llvm::raw_ostream &S, bool Root = false) override {

    std::ostringstream OS;

    // if (UseCount[I] > 1) {
    //   std::string Name = "var" + std::to_string(varnum++);
    //   Syms[I] = Name;
    //   OS << "let " << Name << " = ";
    // }

    // // x ^ -1 => ~x
    // if (I->K == Inst::Xor && I->Ops[1]->K == Inst::Const &&
    //     I->Ops[1]->Val.isAllOnes()) {
    //   return "~" + printInst(I->Ops[0], S);
    // }
    // if (I->K == Inst::Xor && I->Ops[0]->K == Inst::Const &&
    //     I->Ops[0]->Val.isAllOnes()) {
    //   return "~" + printInst(I->Ops[1], S);
    // }

    if (I->K == Inst::Const) {
      if (I->Val.ule(64)) {
        return llvm::toString(I->Val, 10, false);
      } else {
        return "\\text{0x" + llvm::toString(I->Val, 16, false)+ "}";
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

        std::string W = ShowImplicitWidths ? "\\iN{" + std::to_string(I->Width) + "}" : "";

        if (WidthConstraints.count(I)) {
          W = "\\iN{" + std::to_string(WidthConstraints[I]) + "}";
        }

        return Name + W + Out.str();
      }
    } else {
      std::string Op;
      switch (I->K) {
      case Inst::Add: Op = "+"; break;
      case Inst::AddNSW: Op = "+_\\text{nsw}"; break;
      case Inst::AddNUW: Op = "+_\\text{nuw}"; break;
      case Inst::AddNW: Op = "+_\\text{nw}"; break;
      case Inst::Sub: Op = "-"; break;
      case Inst::SubNSW: Op = "-_\\text{nsw}"; break;
      case Inst::SubNUW: Op = "-_\\text{nuw}"; break;
      case Inst::SubNW: Op = "-_\\text{nw}"; break;
      case Inst::Mul: Op = "\\times"; break;
      case Inst::MulNSW: Op = "\\times_\\text{nsw}"; break;
      case Inst::MulNUW: Op = "\\times_\\text{nuw}"; break;
      case Inst::MulNW: Op = "\\times_\\text{nw}"; break;
      case Inst::UDiv: Op = "\\: /_u \\:"; break;
      case Inst::SDiv: Op = "\\: /_s \\:"; break;
      case Inst::URem: Op = "\\: \\\%_u \\:"; break;
      case Inst::SRem: Op = "\\: \\\%_s \\:"; break;
      case Inst::And: Op = "\\: \\& \\:"; break;
      case Inst::Or: Op = "\\: | \\:"; break;
      case Inst::Xor: Op = "\\oplus"; break;
      case Inst::Shl: Op = "\\ll"; break;
      case Inst::ShlNSW: Op = "\\ll_\\text{nsw}"; break;
      case Inst::ShlNUW: Op = "\\ll_\\text{nuw}"; break;
      case Inst::ShlNW: Op = "\\ll_\\text{nw}"; break;
      case Inst::LShr: Op = "\\gg_u"; break;
      case Inst::AShr: Op = "\\gg_s"; break;
      case Inst::Eq: Op = "="; break;
      case Inst::Ne: Op = "\\ne"; break;
      case Inst::Ult: Op = "<_u"; break;
      case Inst::Slt: Op = "<_s"; break;
      case Inst::Ule: Op = "\\le_u"; break;
      case Inst::Sle: Op = "\\le_s"; break;
      case Inst::UAddSat: Op = "+_\\text{u}^\\text{sat}"; break;
      case Inst::SAddSat: Op = "+_\\text{s}^\\text{sat}"; break;
      case Inst::USubSat: Op = "-_\\text{u}^\\text{sat}"; break;
      case Inst::SSubSat: Op = "-_\\text{s}^\\text{sat}"; break;
      case Inst::AShrExact: Op = "\\gg_\\text{s}^\\text{exact}"; break;
      default: Op = std::string("\\text{") + Inst::getKindName(I->K) + "}"; break;
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
      } else if (I->K == Inst::Select) {
        Result = printInst(Ops[0], S) + " \\: ? \\: " + printInst(Ops[1], S) + "\\: : \\:" + printInst(Ops[2], S);
      } else {
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
      // if (UseCount[I] > 1) {
      //   OS << Result << ";\n";
      //   S << OS.str();
      //   return Syms[I];
      // } else {
        return Result;
      // }
    }
  }



};

// TODO print types in preamble (Alex)
// TODO print type info for each instruction (Alex)
// TODO handle constraints on symbolic constants (Alex)
// TODO incorporate width checks (MM)

static const std::map<Inst::Kind, std::string> ArithDialectMap = {
  {Inst::Add, "arith.addi"},
  {Inst::Sub, "arith.subi"},
  {Inst::And, "arith.andi"},
  {Inst::Or, "arith.ori"},
  {Inst::Xor, "arith.xori"},
};

struct PDLGenerator {
  PDLGenerator(ParsedReplacement P_, std::string Name_)
    : P(P_), Name(Name_), Indent(0) {}

  template <typename Stream>
  bool operator()(Stream &S) {

    std::ostringstream OS; // to bail out early without printing if needed
    if (!pre(OS)) return false;
    if (!LHS(OS)) return false;
    if (!RHS(OS)) return false;
    if (!post(OS)) return false;
    S << OS.str();
    return true;
  }

  template <typename Stream>
  bool LHS(Stream &S) {
    if (!printInsts(P.Mapping.LHS, S)) return false;
    return true;
  }

  template <typename Stream>
  bool RHS(Stream &S) {
    if (!rhspre(S)) return false;
    if (!printInsts(P.Mapping.LHS, S)) return false;
    if (!rhspost(S)) return false;
    return true;
  }

  template <typename Stream>
  bool rhspre(Stream &S) {
    if (SymbolTable.find(P.Mapping.LHS) == SymbolTable.end()) {
      llvm::errs() << "LHS Root not found in SymbolTable\n";
      return false;
    }
    indent(S);
    S << "rewrite " << SymbolTable[P.Mapping.LHS] << " {\n";
    Indent++;
    return true;
  }

  template <typename Stream>
  bool rhspost(Stream &S) {
    if (SymbolTable.find(P.Mapping.LHS) == SymbolTable.end()) {
      llvm::errs() << "LHS Root not found in SymbolTable\n";
      return false;
    }

    if (SymbolTable.find(P.Mapping.RHS) == SymbolTable.end()) {
      llvm::errs() << "RHS Root not found in SymbolTable\n";
      return false;
    }

    indent(S);
    S << "replace " << SymbolTable[P.Mapping.LHS] <<
         " with " << SymbolTable[P.Mapping.RHS] << "\n";
    Indent--;
    indent(S);
    S << "}\n";
    return true;
  }

  template <typename Stream>
  bool pre(Stream &S) {
    S << "pdl.pattern @" << Name << " : benefit("
      << souper::benefit(P.Mapping.LHS, P.Mapping.RHS) << ") {\n";
    Indent++;
    // Type declarations go here

    std::vector<Inst *> Vars; // Operands
    findVars(P.Mapping.LHS, Vars);

    for (auto &&Var : Vars) {
      if (SymbolTable.find(Var) == SymbolTable.end()) {
        SymbolTable[Var] = "%v" + std::to_string(SymbolTable.size());
      }
      indent(S);
      S << SymbolTable[Var] << " = operand\n";
      Visited.insert(Var);
    }
    return true;
  }

  template <typename Stream>
  bool post(Stream &S) {
    S << "}\n";
    return true;
  }

  template <typename Stream>
  bool printInsts(Inst *I, Stream &S) {
    for (auto &&Op : I->Ops) {
      if (!printInsts(Op, S)) return false;
    }
    if (!printSingleInst(I, S)) return false;
    return true;
  }

  template <typename Stream>
  bool printSingleInst(Inst *I, Stream &S) {
    static size_t extraSyms = 0;
    if (Visited.find(I) != Visited.end()) return true;
    Visited.insert(I);

    if (SymbolTable.find(I) == SymbolTable.end()) {
      SymbolTable[I] = "%i" + std::to_string(SymbolTable.size());
    }

    if (I->K == Inst::Const) {
      indent(S);
      S << "%" << extraSyms++ << " = attribute = " << llvm::toString(I->Val, 10, false)
               << ":i" << I->Width << "\n";
      indent(S);
      S << SymbolTable[I] << " = operation \"arith.constant\" {\"value\" = %"
                          << extraSyms - 1 << "}\n";
      return true;
      // TODO: This seems sketchy, figure out how a better way to write literal constants
    }

    if (ArithDialectMap.find(I->K) == ArithDialectMap.end()) {
      llvm::errs() << Inst::getKindName(I->K) << " instruction not found in ArithDialectMap\n";
      return false;
    }

    indent(S);
    S << "%" << extraSyms++ << " = pdl.operation \"" << ArithDialectMap.at(I->K) << "\"(";

    bool first = true;
    for (auto &&Op : I->Ops) {
      if (first) {
        first = false;
      } else {
        S << ", ";
      }
      if (SymbolTable.find(Op) == SymbolTable.end()) {
        llvm::errs() << "Operand not found in SymbolTable\n";
        return false;
      }
      S << SymbolTable[Op];
    }

    // TODO: print type info
    S << ")\n";

    indent(S);
    S << SymbolTable[I] << " = result 0 of %" << extraSyms - 1 << "\n";

    return true;
  }

  template <typename Stream>
  void indent(Stream &S) {
    for (size_t i = 0; i < Indent; ++i) {
      S << "  ";
    }
  }
  std::set<Inst *> Visited;
  std::map<Inst *, std::string> SymbolTable;
  ParsedReplacement P;
  std::string Name;
  size_t Indent;
};

}
#endif
