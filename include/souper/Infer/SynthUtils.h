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

class Builder {
public:
  Builder(Inst *I_) : I(I_), IC(*I_->IC) {}
  Builder(Inst *I_, llvm::APInt Value) : IC(*I_->IC) {
    I = IC.getConst(Value);
  }
  Builder(Inst *I_, uint64_t Value) : IC(*I_->IC) {
    I = IC.getConst(llvm::APInt(I_->Width, Value));
  }

  Inst *operator()() {
    assert(I);
    return I;
  }

  template<typename T, typename F> Builder Select(T t, F f) {
    auto left = i(t, *this);
    auto right = i(f, *this);
    return Builder(IC.getInst(Inst::Select, 1, {I, left, right}));
  }

#define BINOP(K)                                                 \
  template<typename T> Builder K(T t) {                          \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::K, L->Width, {L, R}));   \
  }

  BINOP(Add) BINOP(Sub) BINOP(Mul)
  BINOP(And) BINOP(Xor) BINOP(Or)
  BINOP(Shl) BINOP(LShr) BINOP(UDiv)
  BINOP(SDiv) BINOP(AShr) BINOP(URem)
  BINOP(SRem)
#undef BINOP

  template<typename T> Builder Ugt(T t) {                        \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::Ult, 1, {R, L})); \
  }

#define BINOPW(K)                                                \
  template<typename T> Builder K(T t) {                          \
    auto L = I; auto R = i(t, *this);                            \
    return Builder(IC.getInst(Inst::K, 1, {L, R}));          \
  }
  BINOPW(Slt) BINOPW(Ult) BINOPW(Sle) BINOPW(Ule)
  BINOPW(Eq) BINOPW(Ne)
#undef BINOPW

#define UNOP(K)                                                  \
  Builder K() {                                                  \
    auto L = I;                                                  \
    return Builder(IC.getInst(Inst::K, L->Width, {L}));      \
  }
  UNOP(LogB) UNOP(BitReverse) UNOP(BSwap) UNOP(Cttz) UNOP(Ctlz)
  UNOP(BitWidth) UNOP(CtPop)
#undef UNOP

  Builder Flip() {
    auto L = I;
    // auto AllOnes = IC.getConst(llvm::APInt::getAllOnes(L->Width));
    auto AllOnes = Builder(IC.getConst(llvm::APInt(1, 1))).SExt(L->Width)();
    return Builder(IC.getInst(Inst::Xor, L->Width, {L, AllOnes}));
  }
  Builder Negate() {
    auto L = I;
    auto Zero = IC.getConst(llvm::APInt(L->Width, 0));
    return Builder(IC.getInst(Inst::Sub, L->Width, {Zero, L}));
  }

#define UNOPW(K)                                                 \
  Builder K(size_t W) {                                          \
    auto L = I;                                                  \
    return Builder(IC.getInst(Inst::K, W, {L}));             \
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

  Inst *i(Inst *I, Builder B) {
    assert(I);
    return I;
  }

  Inst *i(Builder A, Builder B) {
    assert(A.I);
    return A.I;
  }

  Inst *i(std::string Number, Builder B) {
    return B.IC.getConst(llvm::APInt(B.I->Width, Number, 10));
  }

  Inst *i(llvm::APInt Number, Builder B) {
    return B.IC.getConst(Number);
  }
};

Inst *Replace(Inst *R, std::map<Inst *, Inst *> &M);
ParsedReplacement Replace(ParsedReplacement I, std::map<Inst *, Inst *> &M);

Inst *Replace(Inst *R, std::map<Inst *, llvm::APInt> &ConstMap);
ParsedReplacement Replace(ParsedReplacement I, std::map<Inst *, llvm::APInt> &ConstMap);

ParsedReplacement Make(Inst *LHS, Inst *RHS);
ParsedReplacement Make(Inst *Precondition, Inst *LHS, Inst *RHS);

ParsedReplacement AddPC(ParsedReplacement P, Inst *PC);


ParsedReplacement ToSymConst(ParsedReplacement P, int64_t x);

Inst *Clone(Inst *R);

// Width-related helper functions (moved from Generalize.cpp)
Inst *CombinePCs(const std::vector<InstMapping> &PCs, InstContext &IC);
ParsedReplacement ReplaceMinusOneAndFamily(InstContext &IC, ParsedReplacement Input);
bool hasMultiArgumentPhi(Inst *I);
bool hasConcreteDataflowConditions(ParsedReplacement &Input);
size_t CountWidthAssignments(ParsedReplacement Input);

InstMapping Clone(InstMapping In);

ParsedReplacement Clone(ParsedReplacement In);

// Also Synthesizes given constants
// Returns clone if verified, nullptrs if not
std::optional<ParsedReplacement> Verify(ParsedReplacement Input);
// bool IsValid(ParsedReplacement Input);

// Verify a transformation in width-independent mode using Alive2
// Returns true if valid for all widths, false otherwise
// If ValidTypings is provided, returns the valid width assignments
// If InvalidTypings is provided, returns the invalid width assignments
bool VerifyWidthIndependent(ParsedReplacement Input,
                            std::vector<std::map<const Inst *, size_t>> *ValidTypings = nullptr,
                            std::vector<std::map<const Inst *, size_t>> *InvalidTypings = nullptr);

// Result of width-independent verification with detailed typing information
struct WidthVerificationResult {
  bool IsValid;                    // True if valid for all widths
  bool IsPartiallyValid;           // True if some widths valid, some invalid
  bool CouldNotDetermine;          // True if verification couldn't complete
  std::vector<std::map<const Inst *, size_t>> ValidTypings;
  std::vector<std::map<const Inst *, size_t>> InvalidTypings;
  
  // Print a summary to the given stream
  void printSummary(llvm::raw_ostream &OS) const;
  
  // Print all valid typings
  void printValidTypings(llvm::raw_ostream &OS) const;
  
  // Print all invalid typings  
  void printInvalidTypings(llvm::raw_ostream &OS) const;
  
  // Print a single typing
  static void printTyping(llvm::raw_ostream &OS, 
                          const std::map<const Inst *, size_t> &Typing);
};

// Verify with full result information
WidthVerificationResult VerifyWidthIndependentWithDetails(ParsedReplacement Input);

bool VerifyInvariant(ParsedReplacement Input);

std::map<Inst *, llvm::APInt> findOneConstSet(ParsedReplacement Input, const std::set<Inst *> &SymCS);

std::vector<std::map<Inst *, llvm::APInt>> findValidConsts(ParsedReplacement Input, const std::set<Inst *> &Insts, size_t MaxCount);

ValueCache GetCEX(const ParsedReplacement &Input);

std::vector<ValueCache> GetMultipleCEX(ParsedReplacement Input, size_t MaxCount);

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
      if (I->K == Inst::Custom) {
        Result += I->Name;
      } else {
        Result += Inst::getKindName(I->K);
      }
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
      case Inst::ZExt: Op = ShowImplicitWidths ? "zext-i" + std::to_string(I->Width) : "zext"; break;
      case Inst::SExt: Op = ShowImplicitWidths ? "sext-i" + std::to_string(I->Width) : "sext"; break;
      case Inst::Trunc: Op = ShowImplicitWidths ? "trunc-i" + std::to_string(I->Width) : "trunc"; break;
      case Inst::Custom: Op = I->Name; break;
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
      case Inst::ZExt: Op = ShowImplicitWidths ? "\\text{zext}^{\\iN{" + std::to_string(I->Width) + "}}" : "\\text{zext}"; break;
      case Inst::SExt: Op = ShowImplicitWidths ? "\\text{sext}^{\\iN{" + std::to_string(I->Width) + "}}" : "\\text{sext}"; break;
      case Inst::Trunc: Op = ShowImplicitWidths ? "\\text{trunc}^{\\iN{" + std::to_string(I->Width) + "}}" : "\\text{trunc}"; break;
      default: {
        if (I->K == Inst::Custom) {
          Op = "\\text{" + I->Name + "}";
        } else {
          Op = std::string("\\text{") + Inst::getKindName(I->K) + "}";
        }
        break;
      }
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

// S-expression printer for Souper transformations
// Format: (rewrite lhs rhs) or (rewritepre pre lhs rhs)
// Let bindings at root level
struct SExprPrinter {
  // ShowWidths: if true, add width annotations like x:i32 (for concrete widths)
  //             if false, omit widths (for generalized/symbolic width output)
  SExprPrinter(ParsedReplacement P_, bool ShowWidths_ = false) 
    : P(P_), varnum(0), ShowWidths(ShowWidths_) {}

  // Check for dataflow facts and error if present
  bool hasDataflowFacts(Inst *I) {
    if (!I) return false;
    if (I->K == Inst::Var) {
      if (I->KnownZeros.getBoolValue() || I->KnownOnes.getBoolValue())
        return true;
      if (I->NonNegative || I->Negative || I->NonZero || I->PowOfTwo)
        return true;
      if (I->NumSignBits > 1)
        return true;
      if (!I->Range.isFullSet())
        return true;
    }
    for (auto *Op : I->Ops) {
      if (hasDataflowFacts(Op)) return true;
    }
    return false;
  }

  void countUses(Inst *I) {
    if (!I) return;
    UseCount[I]++;
    if (UseCount[I] == 1) {
      for (auto *Op : I->Ops) {
        countUses(Op);
      }
    }
  }

  // Collect dataflow facts as precondition strings
  std::vector<std::string> DataflowPCs;
  std::set<Inst *> DataflowVisited;
  
  void collectDataflowFacts(Inst *I) {
    if (!I) return;
    if (DataflowVisited.count(I)) return;  // Already processed this instruction
    DataflowVisited.insert(I);
    
    if (I->K == Inst::Var) {
      std::string varName = printInst(I);
      if (I->PowOfTwo) {
        DataflowPCs.push_back("(powerOfTwo " + varName + ")");
      }
      if (I->NonZero) {
        DataflowPCs.push_back("(nonZero " + varName + ")");
      }
      if (I->NonNegative) {
        DataflowPCs.push_back("(nonNegative " + varName + ")");
      }
      if (I->Negative) {
        DataflowPCs.push_back("(negative " + varName + ")");
      }
      // Note: KnownZeros, KnownOnes, NumSignBits, Range not yet supported in sexpr format
    }
    for (auto *Op : I->Ops) {
      collectDataflowFacts(Op);
    }
  }

  void operator()(llvm::raw_ostream &S) {
    // Count uses for let bindings
    countUses(P.Mapping.LHS);
    if (P.Mapping.RHS) countUses(P.Mapping.RHS);
    for (auto &PC : P.PCs) {
      countUses(PC.LHS);
      countUses(PC.RHS);
    }

    // Collect let bindings (assigns names but doesn't print)
    collectLetBindings(P.Mapping.LHS);
    if (P.Mapping.RHS) collectLetBindings(P.Mapping.RHS);
    for (auto &PC : P.PCs) {
      collectLetBindings(PC.LHS);
      collectLetBindings(PC.RHS);
    }
    
    // Collect dataflow facts as preconditions
    DataflowPCs.clear();
    DataflowVisited.clear();
    collectDataflowFacts(P.Mapping.LHS);
    collectDataflowFacts(P.Mapping.RHS);

    // Build the rewrite expression
    std::string RewriteExpr;
    bool hasPCs = !P.PCs.empty() || !DataflowPCs.empty();
    if (!hasPCs) {
      RewriteExpr = "(rewrite " + printInst(P.Mapping.LHS) + "\n" +
                    "         " + printInst(P.Mapping.RHS) + ")";
    } else {
      std::string PCStr;
      llvm::raw_string_ostream PCOS(PCStr);
      // Combine existing PCs and dataflow fact PCs
      std::vector<std::string> AllPCs;
      for (auto &pc : DataflowPCs) {
        AllPCs.push_back(pc);
      }
      if (!P.PCs.empty()) {
        for (auto &PC : P.PCs) {
          if (PC.RHS->K == Inst::Const && PC.RHS->Val == 1) {
            AllPCs.push_back(printInst(PC.LHS));
          } else if (PC.RHS->K == Inst::Const && PC.RHS->Val == 0) {
            AllPCs.push_back("(not " + printInst(PC.LHS) + ")");
          } else {
            AllPCs.push_back("(eq " + printInst(PC.LHS) + " " + printInst(PC.RHS) + ")");
          }
        }
      }
      if (AllPCs.size() == 1) {
        PCStr = AllPCs[0];
      } else {
        PCStr = "(and";
        for (auto &pc : AllPCs) {
          PCStr += " " + pc;
        }
        PCStr += ")";
      }
      RewriteExpr = "(rewritepre " + PCStr + "\n" +
                    "            " + printInst(P.Mapping.LHS) + "\n" +
                    "            " + printInst(P.Mapping.RHS) + ")";
    }

    // If we have let bindings, wrap in let expression
    if (!LetBindings.empty()) {
      S << "(let (";
      for (size_t i = 0; i < LetBindings.size(); ++i) {
        if (i > 0) S << "\n      ";
        S << "(" << LetBindings[i].first << " " << LetBindings[i].second << ")";
      }
      S << ")\n  " << RewriteExpr << ")\n";
    } else {
      S << RewriteExpr << "\n";
    }
  }

  void collectLetBindings(Inst *I) {
    if (!I || Visited.count(I)) return;
    Visited.insert(I);

    // Visit children first
    for (auto *Op : I->Ops) {
      collectLetBindings(Op);
    }

    // If this needs a let binding and we haven't assigned one yet
    if (UseCount[I] > 1 && !Syms.count(I) && I->K != Inst::Var && I->K != Inst::Const) {
      std::string Name = "t" + std::to_string(varnum++);
      Syms[I] = Name;
      LetBindings.push_back({Name, printInstDirect(I)});
    }
  }

  std::string printInst(Inst *I) {
    if (!I) return "?";
    
    // If we have a symbol for this, use it
    if (Syms.count(I)) {
      return Syms[I];
    }

    return printInstDirect(I);
  }

  std::string printInstDirect(Inst *I) {
    if (!I) return "?";

    if (I->K == Inst::Const) {
      std::string valStr;
      if (I->Val.isNegative() && I->Val.sge(-1000)) {
        valStr = std::to_string(I->Val.getSExtValue());
      } else if (I->Val.ule(1000)) {
        valStr = llvm::toString(I->Val, 10, false);
      } else {
        valStr = "#x" + llvm::toString(I->Val, 16, false);
      }
      // Add width annotation if ShowWidths is enabled
      if (ShowWidths) {
        return valStr + ":i" + std::to_string(I->Width);
      }
      return valStr;
    } else if (I->K == Inst::Var) {
      std::string Name = I->Name;
      if (Name.empty()) Name = "v";
      if (isdigit(Name[0])) {
        Name = "x" + Name;
      }
      if (Name.starts_with("symconst_")) {
        Name = "C" + Name.substr(9);
      }
      // Add width annotation only if ShowWidths is enabled
      if (ShowWidths) {
        return Name + ":i" + std::to_string(I->Width);
      }
      return Name;
    }

    // Get operation name
    std::string Op = getOpName(I->K);

    // Handle width-changing operations with explicit width argument
    if (I->K == Inst::ZExt || I->K == Inst::SExt || I->K == Inst::Trunc) {
      // Format: (zext <width> <operand>)
      // For generalized output (no ShowWidths), use _ for any width
      std::string widthArg = ShowWidths ? std::to_string(I->Width) : "_";
      std::string Result = "(" + Op + " " + widthArg;
      for (auto *Operand : I->orderedOps()) {
        Result += " " + printInst(Operand);
      }
      Result += ")";
      return Result;
    }

    // Build s-expression for other operations
    std::string Result = "(" + Op;
    for (auto *Operand : I->orderedOps()) {
      Result += " " + printInst(Operand);
    }
    Result += ")";
    return Result;
  }

  std::string getOpName(Inst::Kind K) {
    switch (K) {
    case Inst::Add: return "add";
    case Inst::AddNSW: return "add.nsw";
    case Inst::AddNUW: return "add.nuw";
    case Inst::AddNW: return "add.nw";
    case Inst::Sub: return "sub";
    case Inst::SubNSW: return "sub.nsw";
    case Inst::SubNUW: return "sub.nuw";
    case Inst::SubNW: return "sub.nw";
    case Inst::Mul: return "mul";
    case Inst::MulNSW: return "mul.nsw";
    case Inst::MulNUW: return "mul.nuw";
    case Inst::MulNW: return "mul.nw";
    case Inst::UDiv: return "udiv";
    case Inst::SDiv: return "sdiv";
    case Inst::URem: return "urem";
    case Inst::SRem: return "srem";
    case Inst::And: return "and";
    case Inst::Or: return "or";
    case Inst::Xor: return "xor";
    case Inst::Shl: return "shl";
    case Inst::ShlNSW: return "shl.nsw";
    case Inst::ShlNUW: return "shl.nuw";
    case Inst::ShlNW: return "shl.nw";
    case Inst::LShr: return "lshr";
    case Inst::LShrExact: return "lshr.exact";
    case Inst::AShr: return "ashr";
    case Inst::AShrExact: return "ashr.exact";
    case Inst::Select: return "select";
    case Inst::ZExt: return "zext";
    case Inst::SExt: return "sext";
    case Inst::Trunc: return "trunc";
    case Inst::Eq: return "eq";
    case Inst::Ne: return "ne";
    case Inst::Ult: return "ult";
    case Inst::Slt: return "slt";
    case Inst::Ule: return "ule";
    case Inst::Sle: return "sle";
    case Inst::CtPop: return "ctpop";
    case Inst::Ctlz: return "ctlz";
    case Inst::Cttz: return "cttz";
    case Inst::LogB: return "logb";
    case Inst::BitWidth: return "width";
    case Inst::BSwap: return "bswap";
    case Inst::BitReverse: return "bitreverse";
    case Inst::FShl: return "fshl";
    case Inst::FShr: return "fshr";
    case Inst::ExtractValue: return "extractvalue";
    case Inst::SAddWithOverflow: return "sadd.overflow";
    case Inst::UAddWithOverflow: return "uadd.overflow";
    case Inst::SSubWithOverflow: return "ssub.overflow";
    case Inst::USubWithOverflow: return "usub.overflow";
    case Inst::SMulWithOverflow: return "smul.overflow";
    case Inst::UMulWithOverflow: return "umul.overflow";
    case Inst::SAddO: return "sadd.o";
    case Inst::UAddO: return "uadd.o";
    case Inst::SSubO: return "ssub.o";
    case Inst::USubO: return "usub.o";
    case Inst::SMulO: return "smul.o";
    case Inst::UMulO: return "umul.o";
    case Inst::SAddSat: return "sadd.sat";
    case Inst::UAddSat: return "uadd.sat";
    case Inst::SSubSat: return "ssub.sat";
    case Inst::USubSat: return "usub.sat";
    case Inst::Freeze: return "freeze";
    case Inst::Lop3: return "lop3";
    default: return Inst::getKindName(K);
    }
  }

  void printPCs(llvm::raw_ostream &S) {
    if (P.PCs.size() == 1) {
      printPC(P.PCs[0], S);
    } else {
      S << "(and";
      for (auto &PC : P.PCs) {
        S << " ";
        printPC(PC, S);
      }
      S << ")";
    }
  }

  void printPC(const InstMapping &PC, llvm::raw_ostream &S) {
    if (PC.RHS->K == Inst::Const && PC.RHS->Val == 1) {
      S << printInst(PC.LHS);
    } else if (PC.RHS->K == Inst::Const && PC.RHS->Val == 0) {
      S << "(not " << printInst(PC.LHS) << ")";
    } else {
      S << "(eq " << printInst(PC.LHS) << " " << printInst(PC.RHS) << ")";
    }
  }

  ParsedReplacement P;
  std::map<Inst *, std::string> Syms;
  std::map<Inst *, size_t> UseCount;
  std::set<Inst *> Visited;
  std::vector<std::pair<std::string, std::string>> LetBindings;
  size_t varnum;
  bool ShowWidths;
};

// S-expression parser for Souper transformations
// Parses format: (let ((name expr)...) (rewrite lhs rhs)) or (rewritepre pre lhs rhs)
// Variables can have width annotations like x:i32, c1:i8
// Missing width annotation means symbolic width (for width-independent verification)
// Width-changing ops use: (zext <width> x) where <width> is number, _, or variable name
class SExprParser {
public:
  static const unsigned DefaultWidth = 32;  // Default width for unspecified widths
  
  SExprParser(InstContext &IC_) : IC(IC_), pos(0), AllWidthsExplicit(true) {}

  std::optional<ParsedReplacement> parse(const std::string &input) {
    this->input = input;
    pos = 0;
    LetEnv.clear();
    VarCache.clear();
    AllWidthsExplicit = true;  // Reset for each parse
    
    skipWhitespace();
    if (pos >= input.size()) {
      error = "Empty input";
      return std::nullopt;
    }
    
    return parseTopLevel();
  }
  
  std::string getError() const { return error; }
  
  // Returns true if all variables and constants had explicit width annotations
  bool allWidthsExplicit() const { return AllWidthsExplicit; }

private:
  InstContext &IC;
  std::string input;
  size_t pos;
  std::string error;
  std::map<std::string, Inst *> LetEnv;      // let-bound names -> Inst
  std::map<std::string, Inst *> VarCache;    // variable names -> Inst (for dedup)
  bool AllWidthsExplicit;                    // True if all vars/consts have explicit widths
  
  void skipWhitespace() {
    while (pos < input.size() && (isspace(input[pos]) || input[pos] == ';')) {
      if (input[pos] == ';') {
        // Skip comment to end of line
        while (pos < input.size() && input[pos] != '\n') pos++;
      } else {
        pos++;
      }
    }
  }
  
  bool match(char c) {
    skipWhitespace();
    if (pos < input.size() && input[pos] == c) {
      pos++;
      return true;
    }
    return false;
  }
  
  bool peek(char c) {
    skipWhitespace();
    return pos < input.size() && input[pos] == c;
  }
  
  std::string parseSymbol() {
    skipWhitespace();
    std::string result;
    while (pos < input.size() && !isspace(input[pos]) && 
           input[pos] != '(' && input[pos] != ')') {
      result += input[pos++];
    }
    return result;
  }
  
  std::optional<ParsedReplacement> parseTopLevel() {
    if (!match('(')) {
      error = "Expected '(' at start";
      return std::nullopt;
    }
    
    std::string keyword = parseSymbol();
    
    if (keyword == "let") {
      return parseLetExpr();
    } else if (keyword == "rewrite") {
      return parseRewrite();
    } else if (keyword == "rewritepre") {
      return parseRewritePre();
    } else {
      error = "Expected 'let', 'rewrite', or 'rewritepre', got: " + keyword;
      return std::nullopt;
    }
  }
  
  std::optional<ParsedReplacement> parseLetExpr() {
    // Parse bindings: ((name1 expr1) (name2 expr2) ...)
    if (!match('(')) {
      error = "Expected '(' for let bindings";
      return std::nullopt;
    }
    
    while (!peek(')')) {
      if (!match('(')) {
        error = "Expected '(' for let binding";
        return std::nullopt;
      }
      
      std::string name = parseSymbol();
      if (name.empty()) {
        error = "Expected binding name";
        return std::nullopt;
      }
      
      auto expr = parseExpr();
      if (!expr) return std::nullopt;
      
      LetEnv[name] = *expr;
      
      if (!match(')')) {
        error = "Expected ')' after let binding";
        return std::nullopt;
      }
    }
    
    if (!match(')')) {
      error = "Expected ')' after let bindings list";
      return std::nullopt;
    }
    
    // Parse the body (should be rewrite or rewritepre)
    auto result = parseTopLevel();
    
    if (!match(')')) {
      error = "Expected ')' at end of let expression";
      return std::nullopt;
    }
    
    return result;
  }
  
  std::optional<ParsedReplacement> parseRewrite() {
    auto lhs = parseExpr();
    if (!lhs) return std::nullopt;
    
    auto rhs = parseExpr();
    if (!rhs) return std::nullopt;
    
    if (!match(')')) {
      error = "Expected ')' at end of rewrite";
      return std::nullopt;
    }
    
    ParsedReplacement PR;
    PR.Mapping.LHS = *lhs;
    PR.Mapping.RHS = *rhs;
    return PR;
  }
  
  std::optional<ParsedReplacement> parseRewritePre() {
    auto pre = parseExpr();
    if (!pre) return std::nullopt;
    
    auto lhs = parseExpr();
    if (!lhs) return std::nullopt;
    
    auto rhs = parseExpr();
    if (!rhs) return std::nullopt;
    
    if (!match(')')) {
      error = "Expected ')' at end of rewritepre";
      return std::nullopt;
    }
    
    ParsedReplacement PR;
    PR.Mapping.LHS = *lhs;
    PR.Mapping.RHS = *rhs;
    // Add precondition: pre == 1
    PR.PCs.push_back({*pre, IC.getConst(llvm::APInt(1, 1))});
    return PR;
  }
  
  std::optional<Inst *> parseExpr() {
    skipWhitespace();
    if (pos >= input.size()) {
      error = "Unexpected end of input";
      return std::nullopt;
    }
    
    if (input[pos] == '(') {
      return parseCompoundExpr();
    } else if (input[pos] == '-' || isdigit(input[pos])) {
      return parseNumber();
    } else if (input[pos] == '#') {
      return parseHexNumber();
    } else {
      return parseAtom();
    }
  }
  
  std::optional<Inst *> parseAtom() {
    std::string sym = parseSymbol();
    if (sym.empty()) {
      error = "Expected symbol";
      return std::nullopt;
    }
    
    // Check if it's a let-bound name
    if (LetEnv.count(sym)) {
      return LetEnv[sym];
    }
    
    // Parse variable with optional width annotation: name or name:iN
    // Missing width means symbolic width (for width-independent verification)
    size_t colonPos = sym.find(':');
    std::string name;
    unsigned width;
    
    if (colonPos == std::string::npos) {
      // No width annotation - symbolic width, use placeholder and mark for width-independent verification
      name = sym;
      width = DefaultWidth;  // Placeholder - actual width determined by width-independent verification
      AllWidthsExplicit = false;
    } else {
      name = sym.substr(0, colonPos);
      std::string widthStr = sym.substr(colonPos + 1);
      
      if (widthStr.empty() || widthStr[0] != 'i') {
        error = "Invalid width annotation: " + widthStr;
        return std::nullopt;
      }
      
      width = std::stoul(widthStr.substr(1));
    }
    
    // Convert CN back to symconst_N for symbolic constants (accept both C and c)
    std::string instName = name;
    if (name.size() > 1 && (name[0] == 'C' || name[0] == 'c') && isdigit(name[1])) {
      instName = "symconst_" + name.substr(1);
    } else if (name.size() > 1 && name[0] == 'x' && isdigit(name[1])) {
      // x0 -> 0 (variable naming convention)
      instName = name.substr(1);
    }
    
    // Check cache for existing variable with same name
    std::string cacheKey = instName + ":" + std::to_string(width);
    if (VarCache.count(cacheKey)) {
      return VarCache[cacheKey];
    }
    
    Inst *V = IC.createVar(width, instName);
    VarCache[cacheKey] = V;
    return V;
  }
  
  std::optional<Inst *> parseNumber() {
    std::string numStr;
    if (input[pos] == '-') {
      numStr += input[pos++];
    }
    while (pos < input.size() && isdigit(input[pos])) {
      numStr += input[pos++];
    }
    
    // Width annotation is optional
    unsigned width;
    if (pos < input.size() && input[pos] == ':') {
      pos++; // skip ':'
      if (pos >= input.size() || input[pos] != 'i') {
        error = "Invalid width annotation for constant '" + numStr + "'";
        return std::nullopt;
      }
      pos++; // skip 'i'
      std::string widthStr;
      while (pos < input.size() && isdigit(input[pos])) {
        widthStr += input[pos++];
      }
      if (widthStr.empty()) {
        error = "Missing width value in annotation for constant '" + numStr + "'";
        return std::nullopt;
      }
      width = std::stoul(widthStr);
    } else {
      // No width annotation - symbolic width, use placeholder for width-independent verification
      width = DefaultWidth;
      AllWidthsExplicit = false;
    }
    
    int64_t val = std::stoll(numStr);
    return IC.getConst(llvm::APInt(width, val, true));
  }
  
  std::optional<Inst *> parseHexNumber() {
    pos++; // skip '#'
    if (pos >= input.size() || input[pos] != 'x') {
      error = "Expected 'x' after '#'";
      return std::nullopt;
    }
    pos++; // skip 'x'
    
    std::string hexStr;
    while (pos < input.size() && isxdigit(input[pos])) {
      hexStr += input[pos++];
    }
    
    // Width annotation is optional
    unsigned width;
    if (pos < input.size() && input[pos] == ':') {
      pos++; // skip ':'
      if (pos >= input.size() || input[pos] != 'i') {
        error = "Invalid width annotation for hex constant '#x" + hexStr + "'";
        return std::nullopt;
      }
      pos++; // skip 'i'
      std::string widthStr;
      while (pos < input.size() && isdigit(input[pos])) {
        widthStr += input[pos++];
      }
      if (widthStr.empty()) {
        error = "Missing width value in annotation for hex constant '#x" + hexStr + "'";
        return std::nullopt;
      }
      width = std::stoul(widthStr);
    } else {
      // No width annotation - symbolic width, use placeholder for width-independent verification
      width = DefaultWidth;
      AllWidthsExplicit = false;
    }
    
    llvm::APInt val(width, hexStr, 16);
    return IC.getConst(val);
  }
  
  // Parse width argument for width-changing operations
  // Returns: {width, isSymbolic, widthVarName}
  // width=0 means "any width" (_), isSymbolic=true means it's a variable
  struct WidthArg {
    unsigned width;
    bool isSymbolic;
    std::string varName;
  };
  
  std::optional<WidthArg> parseWidthArg() {
    skipWhitespace();
    if (pos >= input.size()) {
      error = "Expected width argument";
      return std::nullopt;
    }
    
    // Check for _ (any width)
    if (input[pos] == '_') {
      pos++;
      return WidthArg{0, false, ""};
    }
    
    // Check for numeric width
    if (isdigit(input[pos])) {
      std::string numStr;
      while (pos < input.size() && isdigit(input[pos])) {
        numStr += input[pos++];
      }
      return WidthArg{(unsigned)std::stoul(numStr), false, ""};
    }
    
    // Otherwise it's a variable name (symbolic width)
    std::string varName;
    while (pos < input.size() && !isspace(input[pos]) && 
           input[pos] != '(' && input[pos] != ')') {
      varName += input[pos++];
    }
    if (varName.empty()) {
      error = "Expected width argument";
      return std::nullopt;
    }
    return WidthArg{0, true, varName};
  }
  
  std::optional<Inst *> parseCompoundExpr() {
    if (!match('(')) {
      error = "Expected '('";
      return std::nullopt;
    }
    
    std::string op = parseSymbol();
    if (op.empty()) {
      error = "Expected operation name";
      return std::nullopt;
    }
    
    // Check if this is a width-changing operation
    bool isWidthChanging = (op == "zext" || op == "sext" || op == "trunc");
    WidthArg widthArg{0, false, ""};
    
    if (isWidthChanging) {
      // Parse width argument first
      auto wa = parseWidthArg();
      if (!wa) return std::nullopt;
      widthArg = *wa;
    }
    
    // Parse operands
    std::vector<Inst *> operands;
    while (!peek(')')) {
      auto operand = parseExpr();
      if (!operand) return std::nullopt;
      operands.push_back(*operand);
    }
    
    if (!match(')')) {
      error = "Expected ')'";
      return std::nullopt;
    }
    
    return makeInst(op, operands, widthArg);
  }
  
  std::optional<Inst *> makeInst(const std::string &op, const std::vector<Inst *> &operands, 
                                  WidthArg widthArg = {0, false, ""}) {
    // Map operation name to Inst::Kind
    static const std::map<std::string, Inst::Kind> OpMap = {
      {"add", Inst::Add}, {"add.nsw", Inst::AddNSW}, {"add.nuw", Inst::AddNUW}, {"add.nw", Inst::AddNW},
      {"sub", Inst::Sub}, {"sub.nsw", Inst::SubNSW}, {"sub.nuw", Inst::SubNUW}, {"sub.nw", Inst::SubNW},
      {"mul", Inst::Mul}, {"mul.nsw", Inst::MulNSW}, {"mul.nuw", Inst::MulNUW}, {"mul.nw", Inst::MulNW},
      {"udiv", Inst::UDiv}, {"sdiv", Inst::SDiv},
      {"urem", Inst::URem}, {"srem", Inst::SRem},
      {"and", Inst::And}, {"or", Inst::Or}, {"xor", Inst::Xor},
      {"shl", Inst::Shl}, {"shl.nsw", Inst::ShlNSW}, {"shl.nuw", Inst::ShlNUW}, {"shl.nw", Inst::ShlNW},
      {"lshr", Inst::LShr}, {"lshr.exact", Inst::LShrExact},
      {"ashr", Inst::AShr}, {"ashr.exact", Inst::AShrExact},
      {"select", Inst::Select},
      {"zext", Inst::ZExt}, {"sext", Inst::SExt}, {"trunc", Inst::Trunc},
      {"eq", Inst::Eq}, {"ne", Inst::Ne},
      {"ult", Inst::Ult}, {"slt", Inst::Slt}, {"ule", Inst::Ule}, {"sle", Inst::Sle},
      {"ctpop", Inst::CtPop}, {"ctlz", Inst::Ctlz}, {"cttz", Inst::Cttz}, {"logb", Inst::LogB},
      {"bswap", Inst::BSwap}, {"bitreverse", Inst::BitReverse},
      {"fshl", Inst::FShl}, {"fshr", Inst::FShr},
      {"sadd.sat", Inst::SAddSat}, {"uadd.sat", Inst::UAddSat},
      {"ssub.sat", Inst::SSubSat}, {"usub.sat", Inst::USubSat},
      {"freeze", Inst::Freeze},
      {"width", Inst::BitWidth},
      {"not", Inst::Xor}, // Special case: (not x) -> (xor x -1)
    };
    
    // Handle dataflow fact predicates (before OpMap lookup)
    
    // (powerOfTwo x) => (x != 0) && ((x & (x - 1)) == 0)
    if (op == "powerOfTwo" && operands.size() == 1) {
      Inst *X = operands[0];
      unsigned w = X->Width;
      Inst *Zero = IC.getConst(llvm::APInt(w, 0));
      Inst *One = IC.getConst(llvm::APInt(w, 1));
      // x != 0
      Inst *NonZeroCond = IC.getInst(Inst::Ne, 1, {X, Zero});
      // x & (x - 1)
      Inst *XMinusOne = IC.getInst(Inst::Sub, w, {X, One});
      Inst *AndExpr = IC.getInst(Inst::And, w, {X, XMinusOne});
      // (x & (x-1)) == 0
      Inst *IsPow2 = IC.getInst(Inst::Eq, 1, {AndExpr, Zero});
      // nonzero && ispow2
      return IC.getInst(Inst::And, 1, {NonZeroCond, IsPow2});
    }
    
    // (nonZero x) => x != 0
    if (op == "nonZero" && operands.size() == 1) {
      Inst *X = operands[0];
      Inst *Zero = IC.getConst(llvm::APInt(X->Width, 0));
      return IC.getInst(Inst::Ne, 1, {X, Zero});
    }
    
    // (nonNegative x) => x >= 0 (signed)
    if (op == "nonNegative" && operands.size() == 1) {
      Inst *X = operands[0];
      Inst *Zero = IC.getConst(llvm::APInt(X->Width, 0));
      return IC.getInst(Inst::Sle, 1, {Zero, X});
    }
    
    // (negative x) => x < 0 (signed)
    if (op == "negative" && operands.size() == 1) {
      Inst *X = operands[0];
      Inst *Zero = IC.getConst(llvm::APInt(X->Width, 0));
      return IC.getInst(Inst::Slt, 1, {X, Zero});
    }
    
    auto it = OpMap.find(op);
    if (it == OpMap.end()) {
      error = "Unknown operation: " + op;
      return std::nullopt;
    }
    
    if (operands.empty()) {
      error = "Operation " + op + " requires operands";
      return std::nullopt;
    }
    
    Inst::Kind K = it->second;
    
    // Handle special case: not
    if (op == "not" && operands.size() == 1) {
      unsigned w = operands[0]->Width;
      Inst *MinusOne = IC.getConst(llvm::APInt::getAllOnes(w));
      return IC.getInst(Inst::Xor, w, {operands[0], MinusOne});
    }
    
    // Handle width-changing operations
    if (K == Inst::ZExt || K == Inst::SExt || K == Inst::Trunc) {
      unsigned resultWidth;
      if (widthArg.isSymbolic) {
        // Symbolic width variable - use placeholder, triggers width-independent verification
        AllWidthsExplicit = false;
        unsigned opWidth = operands[0]->Width;
        if (K == Inst::Trunc) {
          resultWidth = opWidth > 1 ? opWidth / 2 : 1;
        } else {
          resultWidth = opWidth * 2;
        }
      } else if (widthArg.width == 0) {
        // _ means symbolic width - triggers width-independent verification
        // Use a fixed large placeholder width (64) so all _ placeholders
        // produce the same width, avoiding width mismatch in comparisons
        AllWidthsExplicit = false;
        unsigned opWidth = operands[0]->Width;
        if (K == Inst::Trunc) {
          // For trunc, use half of operand width as placeholder
          resultWidth = opWidth > 1 ? opWidth / 2 : 1;
        } else {
          // For zext/sext, use a large fixed width (64) as placeholder
          // This ensures all _ widths are the same for comparison operations
          resultWidth = 64;
        }
      } else {
        resultWidth = widthArg.width;
      }
      return IC.getInst(K, resultWidth, operands);
    }
    
    // Determine result width from first operand
    unsigned width = operands[0]->Width;
    
    // Comparison operations return i1
    if (K == Inst::Eq || K == Inst::Ne || K == Inst::Ult || K == Inst::Slt ||
        K == Inst::Ule || K == Inst::Sle) {
      width = 1;
    }
    
    // For select, the condition is i1 but result width comes from the other operands
    if (K == Inst::Select && operands.size() >= 2) {
      width = operands[1]->Width;
    }
    
    return IC.getInst(K, width, operands);
  }
};

// Helper function to parse S-expression string
// Returns parsed replacement and sets allWidthsExplicit to indicate if all widths were specified
inline std::optional<ParsedReplacement> ParseSExpr(InstContext &IC, const std::string &input, 
                                                    std::string &error, bool *allWidthsExplicit = nullptr) {
  SExprParser parser(IC);
  auto result = parser.parse(input);
  if (!result) {
    error = parser.getError();
  }
  if (allWidthsExplicit) {
    *allWidthsExplicit = parser.allWidthsExplicit();
  }
  return result;
}

// TODO print types in preamble (Alex)
// TODO print type info for each instruction (Alex)
// TODO handle constraints on symbolic constants (Alex)
// TODO incorporate width checks (MM)

static const std::map<Inst::Kind, std::string> ArithDialectMap = {
  {Inst::Add, "arith.addi"},
  {Inst::Sub, "arith.subi"},
  {Inst::And, "arith.andi"},
  {Inst::Or, "arith.ori"},
  {Inst::Mul, "arith.muli"},
  {Inst::MulNSW, "arith.muli"},
  {Inst::MulNUW, "arith.muli"},
  {Inst::MulNW, "arith.muli"},
  {Inst::Xor, "arith.xori"},
  {Inst::Shl, "arith.shli"},
  {Inst::LShr, "arith.shrui"},
  {Inst::AShr, "arith.shrsi"},
  {Inst::UDiv, "arith.divui"},
  {Inst::SDiv, "arith.divsi"},
  {Inst::URem, "arith.remui"},
  {Inst::SRem, "arith.remsi"},
  {Inst::Select, "arith.select"},
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
