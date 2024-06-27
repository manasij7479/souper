#include "llvm/Support/MemoryBuffer.h"

#include "souper/Infer/Preconditions.h"
#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/SynthUtils.h"
#include "souper/Parser/Parser.h"
#include "souper/Tool/GetSolver.h"

#include <fstream>
#include <deque>

using namespace llvm;
using namespace souper;

unsigned DebugLevel;

static cl::opt<unsigned, /*ExternalStorage=*/true>
DebugFlagParser("souper-debug-level",
     cl::desc("Control the verbose level of debug output (default=1). "
     "The larger the number is, the more fine-grained debug "
     "information will be printed."),
     cl::location(DebugLevel), cl::init(1));

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input souper optimization>"),
              cl::init("-"));

static llvm::cl::opt<bool> IgnorePCs("ignore-pcs",
    llvm::cl::desc("Ignore inputs which have souper path conditions."
                   "(default=false)"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> IgnoreDF("ignore-df",
    llvm::cl::desc("Ignore inputs with dataflow constraints."
                   "(default=false)"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> NoDispatch("no-dispatch",
    llvm::cl::desc("Do not generate code to dispatch on root instruction kind."
                   "(default=false)"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> OnlyExplicitWidths("explicit-width-checks",
    llvm::cl::desc("Only generate width checks when explicitly specified."
                   "(default=false)"),
    llvm::cl::init(true));

static llvm::cl::opt<bool> Sort("sortf",
    llvm::cl::desc("Sort matchers according to listfile"
                   "(default=false)"),
    llvm::cl::init(false));

static llvm::cl::opt<std::string> ListFile("listfile",
    llvm::cl::desc("List of optimization indexes to include.\n"
                   "(default=empty-string)"),
    llvm::cl::init(""));

static llvm::cl::opt<std::string> ListOutFile("listoutfile",
    llvm::cl::desc("List of optimization indexes to include.\n"
                   "(default=empty-string)"),
    llvm::cl::init(""));


static const std::map<Inst::Kind, std::string> MatchOps = {
  {Inst::Add, "m_c_Add("}, {Inst::Sub, "m_Sub("},
  {Inst::Mul, "m_c_Mul("},

  {Inst::Shl, "m_Shl("}, {Inst::LShr, "m_LShr("},
  {Inst::AShr, "m_AShr("},

  {Inst::AddNSW, "m_NSWAdd("}, {Inst::SubNSW, "m_NSWSub("}, // add _c_ too?
  {Inst::MulNSW, "m_NSWMul("}, {Inst::ShlNSW, "m_NSWShl("},
  {Inst::AddNUW, "m_NUWAdd("}, {Inst::SubNUW, "m_NUWSub("},
  {Inst::MulNUW, "m_NUWMul("}, {Inst::ShlNUW, "m_NUWShl("},
  {Inst::AddNW, "m_NWAdd("}, {Inst::SubNW, "m_NWSub("},
  {Inst::MulNW, "m_NWMul("}, {Inst::ShlNW, "m_NWShl("},

  {Inst::SDiv, "m_SDiv("}, {Inst::UDiv, "m_UDiv("},
  {Inst::SRem, "m_SRem("}, {Inst::URem, "m_URem("},

  {Inst::AShrExact, "m_AShrExact("}, {Inst::LShrExact, "m_LShrExact("},
  {Inst::UDivExact, "m_UDivExact("}, {Inst::SDivExact, "m_SDivExact("},

  {Inst::And, "m_c_And("}, {Inst::Or, "m_c_Or("},
  {Inst::Xor, "m_c_Xor("},

  {Inst::Freeze, "m_Freeze("},

  {Inst::Eq, "m_c_ICmp("},
  {Inst::Ne, "m_c_ICmp("},
  {Inst::Ule, "m_ICmp("},
  {Inst::Ult, "m_ICmp("},
  {Inst::Sle, "m_ICmp("},
  {Inst::Slt, "m_ICmp("},

  {Inst::SExt, "m_SExt("},
  {Inst::ZExt, "m_ZExt("},
  {Inst::Trunc, "m_Trunc("},
  {Inst::Select, "m_Select("},
  {Inst::Phi, "m_Phi("},
};

static const std::map<Inst::Kind, std::string> CreateOps = {
  {Inst::Shl, "CreateShl("}, {Inst::AShr, "CreateAShr("}, {Inst::LShr, "CreateLShr("},
  {Inst::Add, "CreateAdd("}, {Inst::Mul, "CreateMul("}, {Inst::Sub, "CreateSub("},
  {Inst::SDiv, "CreateSDiv("}, {Inst::UDiv, "CreateUDiv("}, {Inst::SRem, "CreateSRem("},
  {Inst::URem, "CreateURem("},
  {Inst::Or, "CreateOr("}, {Inst::And, "CreateAnd("}, {Inst::Xor, "CreateXor("},
  {Inst::AShrExact, "CreateAShrExact("},// {Inst::LShrExact, "CreateExactLShr("},
  // {Inst::UDivExact, "CreateExactUDiv("}, {Inst::SDivExact, "CreateExactSDiv("},
  //{Inst::AddNW, "CreateAddNW("}, {Inst::SubNW, "CreateSubNW("},

  // FakeOps
  {Inst::LogB, "CreateLogB("},

  {Inst::Eq, "CreateCmp(ICmpInst::ICMP_EQ, "},
  {Inst::Ne, "CreateCmp(ICmpInst::ICMP_NE, "},
  {Inst::Ule, "CreateCmp(ICmpInst::ICMP_ULE, "},
  {Inst::Ult, "CreateCmp(ICmpInst::ICMP_ULT, "},
  {Inst::Sle, "CreateCmp(ICmpInst::ICMP_SLE, "},
  {Inst::Slt, "CreateCmp(ICmpInst::ICMP_SLT, "},

  {Inst::Trunc, "CreateTrunc("},
  {Inst::SExt, "CreateSExt("},
  {Inst::ZExt, "CreateZExt("},
  {Inst::Freeze, "CreateFreeze("},

  {Inst::Select, "CreateSelect("},

  {Inst::FShl, "CreateFShl("},
  {Inst::FShr, "CreateFShr("},
  {Inst::BSwap, "CreateBSwap("},

  {Inst::Const, "dummy"},
};

static const std::map<Inst::Kind, std::string> PredNames = {
  {Inst::Eq, "ICmpInst::ICMP_EQ"},
  {Inst::Ne, "ICmpInst::ICMP_NE"},
  {Inst::Ule, "ICmpInst::ICMP_ULE"},
  {Inst::Ult, "ICmpInst::ICMP_ULT"},
  {Inst::Sle, "ICmpInst::ICMP_SLE"},
  {Inst::Slt, "ICmpInst::ICMP_SLT"},
};

struct Constraint {
  virtual std::string print() = 0;
};

struct VarEq : public Constraint {
  VarEq(std::string LHS_, std::string RHS_) : LHS(LHS_), RHS(RHS_) {}
  std::string LHS;
  std::string RHS;
  std::string print() override {
    return LHS + " == " + RHS;
  }
};

struct PredEq : public Constraint {
  PredEq(std::string P_, std::string K_) : P(P_), K(K_) {}
  std::string P;
  std::string K;
  std::string print() override {
    return P + " == " + K;
  }
};

struct WidthEq : public Constraint {
  WidthEq(std::string Name_, size_t W_) : Name(Name_) , W(W_){}
  std::string Name;
  size_t W;
  std::string print() override {
    return "util::check_width(" + Name + ',' + std::to_string(W) + ")";
  }
};

struct DomCheck : public Constraint {
  DomCheck(std::string Name_) : Name(Name_) {}
  std::string Name;

  std::string print() override {
    return "util::dc(DT, I, " + Name + ")";
  }
};

struct VC : public Constraint {
  VC(std::string Cons_, std::string Name_) : Cons(Cons_), Name(Name_)  {}
  std::string print() override {
    return "util::" + Cons + "(" + Name + ")";
  }
  std::string Name;
  std::string Cons;
};

struct NSB : public Constraint {
  NSB(std::string Name_, size_t Value_) : Name(Name_), Value(Value_)  {}
  std::string print() override {
    return "util::nsb(" + Name + ", " + std::to_string(Value) + ")";
  }
  std::string Name;
  size_t Value;
};

struct PC : public Constraint {
  PC(std::string LHS, std::string RHS) : L(LHS), R(RHS) {}
  std::string print() override {
    return "(" + L + " == " + R + ")";
  }
  std::string L, R;
};

struct DB : public Constraint {
  DB(std::string Val_, size_t W_) : Val(Val_), W(W_) {}
  std::string print() override {
    return "util::vdb(DB, I, \"" + Val + "\", " + std::to_string(W) + ")";
  }
  std::string Val;
  size_t W;
};

struct SymDB : public Constraint {
  SymDB(std::string Name_) : Name(Name_) {}
  std::string print() override {
    return "util::symdb(DB, I, " + Name + ", B)";
  }
  std::string Name;
};

struct K0 : public Constraint {
  K0(std::string Name_, std::string Val_, size_t W_) : Name(Name_), Val(Val_), W(W_) {}
  std::string print() override {
    return "util::k0(" + Name + ", \"" + Val + "\", " + std::to_string(W) + ")";
  }
  std::string Name, Val;
  size_t W;
};

struct K1 : public Constraint {
  K1(std::string Name_, std::string Val_, size_t W_) : Name(Name_), Val(Val_), W(W_) {}
  std::string print() override {
    return "util::k1(" + Name + ", \"" + Val + "\", " + std::to_string(W) + ")";
  }
  std::string Name, Val;
  size_t W;
};

struct SymK0Bind : public Constraint {
  SymK0Bind(std::string Name_, std::string Bind_) : Name(Name_), Bind(Bind_) {}
  std::string print() override {
    return "util::symk0bind(" + Name + ", " + Bind + ", B)";
  }
  std::string Name, Bind;
};

struct SymK1Bind : public Constraint {
  SymK1Bind(std::string Name_, std::string Bind_) : Name(Name_), Bind(Bind_) {}
  std::string print() override {
    return "util::symk1bind(" + Name + ", " + Bind + ", B)";
  }
  std::string Name, Bind;
};

struct SymK0Test : public Constraint {
  SymK0Test(std::string Name_, std::string Name2_) : Name(Name_), Name2(Name2_) {}
  std::string print() override {
    return "util::symk0test(" + Name + ", " + Name2 + ")";
  }
  std::string Name, Name2;
};

struct SymK1Test : public Constraint {
  SymK1Test(std::string Name_, std::string Name2_) : Name(Name_), Name2(Name2_) {}
  std::string print() override {
    return "util::symk1test(" + Name + ", " + Name2 + ")";
  }
  std::string Name, Name2;
};


struct CR : public Constraint {
  CR(std::string Name_, std::string L_, std::string H_) : Name(Name_), L(L_), H(H_) {}
  std::string print() override {
    return "util::cr(" + Name + ", \"" + L + "\", \"" + H + "\")";
  }
  std::string Name, L, H;
};

struct SymbolTable {
  std::map<Inst *, std::string> T;
  std::deque<Constraint *> Constraints;

  std::map<Inst *, std::string> Preds;
  std::vector<Inst *> Vars;
  std::set<Inst *> ConstRefs;

  std::set<Inst *> Used;

  void RegisterPred(Inst *I) {
    if (PredNames.find(I->K) == PredNames.end()) {
      return; // not a predicate
    }
    if (Preds.find(I) != Preds.end()) {
      return; // already registered
    }
    auto Name = "P" + std::to_string(Preds.size());
    Preds[I] = Name;
    Constraints.push_back(new PredEq(Name, PredNames.at(I->K)));
  }

  bool exists(Inst *I) {
    if (T.find(I) == T.end()) {
      return false;
    }
    return !T.at(I).empty();
  }

  template<typename Stream>
  void PrintPreds(Stream &Out) {
    if (Preds.empty()) {
      return;
    }
    Out << "ICmpInst::Predicate ";
    bool first = true;
    for (auto &&P : Preds) {
      if (first) {
        first = false;
      } else {
        Out << ", ";
      }
      Out << P.second;
    }
    Out << ";\n";
  }

  // Try to translate Souper expressions to APInt operations.
  std::pair<std::string, bool> Translate(souper::Inst *I) {
    std::vector<std::pair<std::string, bool>> Children;

    if (I->K == Inst::BitWidth) {
      if (I->Ops[0]->K != Inst::Var) {
        llvm::errs() << "Width of a non var.\n";
        return {"", false};
      }
      if (T.at(I->Ops[0]).empty()) {
        return {"", false};
      }
      auto Sym = T.at(I->Ops[0]);
      return {"util::W(" + Sym +  ")", true};
    }

    for (auto Op : I ->Ops) {
      Children.push_back(Translate(Op));
      if (!Children.back().second) {
        return {"", false};
      }
    }

    auto MET = [&](auto Str) {
      return Children[0].first + "." + Str + "(" + Children[1].first + ")";
    };

    auto WC64_HACK = [&](auto Str) {
      return Children[0].first + "." + Str + "(64)";
    };

    auto WC = [&](auto Str) {
      return Children[0].first + "." + Str + "(" + std::to_string(I->Width) + ")";
    };

    auto OP = [&](auto Str) {
      return "(" + Children[0].first + " " + Str + " " + Children[1].first + ")";
    };

    auto FUN = [&](auto Str) {
      return std::string(Str) + "(" + Children[0].first + ", " + Children[1].first + ")";
    };

    switch (I->K) {
    case Inst::Var :
    if (exists(I)) {
        return {"util::V(" + T.at(I) + ")", true};
      } else {
        return {"", false};
      }
    case Inst::Const : {

      std::string W = std::to_string(I->Width);

      if (I->Width <= 64) {
        return {"llvm::APInt(" + W + ", " + llvm::toString(I->Val, 10, false) + ")", true};
      } else {
        return {"util::V(" + W
          + ", \"" + llvm::toString(I->Val, 10, false) + "\")", true};
      }
    }

    case Inst::AddNW :
    case Inst::AddNUW :
    case Inst::AddNSW :
    case Inst::Add : return {FUN("add"), true};

    case Inst::SubNW :
    case Inst::SubNUW :
    case Inst::SubNSW :
    case Inst::Sub : return {FUN("sub"), true};

    case Inst::MulNW :
    case Inst::MulNUW :
    case Inst::MulNSW :
    case Inst::Mul : return {FUN("mul"), true};

    case Inst::Shl : {
      if (isdigit(Children[0].first[0])) {
        return {FUN("shl"), true};
      } else {
        return {FUN("shl"), true};
      }
    }
    case Inst::LShr : return {MET("lshr"), true};
    case Inst::AShr : return {MET("ashr"), true};

    case Inst::And : {
      if (I->Width == 1) {
        return {OP("&"), true};
      }
      return {FUN("and_"), true};
    }
    case Inst::Or : {
      if (I->Width == 1) {
        return {OP("|"), true};
      }
      return {FUN("or_"), true};
    }
    case Inst::Xor : {
      if (I->Width == 1) {
        return {OP("^"), true};
      }
      return {FUN("xor_"), true};
    }

    case Inst::URem : return {FUN("urem"), true};
    case Inst::SRem : return {FUN("srem"), true};
    case Inst::UDiv : return {FUN("udiv"), true};
    case Inst::SDiv : return {FUN("sdiv"), true};

    case Inst::Slt : {
      if (isdigit(Children[0].first[0])) {
        return {OP("<"), true};
      } else {
        return {FUN("slt"), true};
      }
    }
    case Inst::Sle : {
      if (isdigit(Children[0].first[0])) {
        return {OP("<="), true};
      } else {
        return {FUN("sle"), true};
      }
    }
    case Inst::Ult : {
      if (isdigit(Children[0].first[0])) {
        return {OP("<"), true};
      } else {
        return {FUN("ult"), true};
      }
    }
    case Inst::Ule : {
      if (isdigit(Children[0].first[0])) {
        return {OP("<="), true};
      } else {
        return {FUN("ule"), true};
      }
    }
    case Inst::Eq : {
      if (isdigit(Children[0].first[0])) {
        return {OP("=="), true};
      } else {
        return {FUN("eq"), true};
      }
    }
    case Inst::Ne : {
      if (isdigit(Children[0].first[0])) {
        return {OP("!="), true};
      } else {
        return {FUN("ne"), true};
      }
    }
    case Inst::ZExt : return {WC64_HACK("zext"), true};
    case Inst::SExt : return {WC64_HACK("sext"), true};
    case Inst::Trunc : return {WC("trunc"), true};

    default: {
      llvm::errs() << "Unimplemented op in PC: " << Inst::getKindName(I->K) << "\n";
      return {"", false};
    }
    }

  }

  Constraint *ConvertPCToWidthConstraint(InstMapping PC) {
    if (PC.LHS->K != Inst::Eq)
      return nullptr;
    if (PC.LHS->Ops[0]->K == Inst::BitWidth) {
      return new WidthEq(T.at(PC.LHS->Ops[0]->Ops[0]),
                                 PC.LHS->Ops[1]->Val.getLimitedValue());
    }
    if (PC.LHS->Ops.size() > 1 && PC.LHS->Ops[1]->K == Inst::BitWidth) {
      return new WidthEq(T.at(PC.LHS->Ops[1]->Ops[0]),
                                 PC.LHS->Ops[0]->Val.getLimitedValue());
    }
    return nullptr;
  }

  bool GenPCConstraints(std::vector<InstMapping> PCs) {
    for (auto M : PCs) {
      if (M.LHS->K == Inst::KnownZerosP) {
        if (M.LHS->Ops[0]->K == Inst::Var && M.LHS->Ops[1]->Name.starts_with("symDF_K")) {
          auto C = new SymK0Bind(T.at(M.LHS->Ops[0]),
                                 T.at(M.LHS->Ops[1]));
          Constraints.push_front(C);
          // Binds have side effects, have to go in front.
        } else {
          auto C = new SymK0Test(T.at(M.LHS->Ops[0]),
                                 T.at(M.LHS->Ops[1]));
          Constraints.push_back(C);
        }
      } else if (M.LHS->K == Inst::KnownOnesP) {
        if (M.LHS->Ops[0]->K == Inst::Var && M.LHS->Ops[1]->Name.starts_with("symDF_K")) {
          auto C = new SymK1Bind(T.at(M.LHS->Ops[0]),
                                 T.at(M.LHS->Ops[1]));
          Constraints.push_front(C);
          // Binds have side effects, have to go in front.
        } else {
          auto C = new SymK1Test(T.at(M.LHS->Ops[0]),
                                 T.at(M.LHS->Ops[1]));
          Constraints.push_back(C);
        }
      } else if (auto WC = ConvertPCToWidthConstraint(M)) {
        Constraints.push_back(WC);
      } else {
        auto L = Translate(M.LHS);
        auto R = Translate(M.RHS);
        if (!L.second || !R.second) {
          return false;
        }
        Constraints.push_back(new PC(L.first, R.first));
      }
    }
    return true;
  }

  void GenDomConstraints(Inst *RHS) {
    static std::set<Inst *> Visited;
    Visited.insert(RHS);
    for (auto Op : RHS->Ops) {
      if (Op->K == Inst::Const) {
        continue;
        // TODO: Find other cases
      }
      auto It = T.find(Op);
      if (It != T.end()) {
        if (Visited.find(Op) == Visited.end()) {
          Constraints.push_back(new DomCheck(It->second));
          GenDomConstraints(Op);
        }
      }
    }
  }

  void GenDFConstraints(Inst *LHS) {
    if (LHS->DemandedBits.getBitWidth()
        == LHS->Width && !LHS->DemandedBits.isAllOnesValue()) {
      Constraints.push_back(new DB(llvm::toString(LHS->DemandedBits, 2, false), LHS->Width));
    }

    std::vector<Inst *> Vars;
    findVars(LHS, Vars);

    std::set<Inst *> VarSet;
    for (auto &&V : Vars) {
      VarSet.insert(V);
    }

    for (auto &&V : VarSet) {
      auto Name = T.at(V);
      if (V->KnownOnes.getBitWidth() == V->Width &&
          V->KnownOnes != 0) {
        Constraints.push_back(new K1(Name, llvm::toString(V->KnownOnes, 2, false), V->Width));
      }
      if (V->KnownZeros.getBitWidth() == V->Width &&
          V->KnownZeros != 0) {
        Constraints.push_back(new K0(Name, llvm::toString(V->KnownZeros, 2, false), V->Width));
      }

      if (!V->Range.isFullSet()) {
        Constraints.push_back(new CR(Name, llvm::toString(V->Range.getLower(), 10, false), llvm::toString(V->Range.getUpper(), 10, false)));
      }
    }
  }

  void GenVarPropConstraints(Inst *LHS, bool WidthIndependent) {
    std::vector<Inst *> Vars;
    findVars(LHS, Vars);

    for (auto V : Vars) {
      auto Name = T.at(V);

      if (!WidthIndependent || V->Width == 1) {
        Constraints.push_back(new WidthEq(Name, V->Width));
      }

      if (V->PowOfTwo) {
        Constraints.push_back(new VC("pow2", Name));
      }
      if (V->NonZero) {
        Constraints.push_back(new VC("nz", Name));
      }
      if (V->NonNegative) {
        Constraints.push_back(new VC("nn", Name));
      }
      if (V->Negative) {
        Constraints.push_back(new VC("neg", Name));
      }
      if (V->NumSignBits) {
        Constraints.push_back(new NSB(Name, V->NumSignBits));
      }
    }
  }

  template <typename Stream>
  void PrintConstraintsPre(Stream &Out) {
    if (Constraints.empty()) {
      return;
    }
    Out << "if (";
    bool first = true;
    for (auto &&C : Constraints) {
      if (first) {
        first = false;
      } else {
        Out << " && ";
      }
      Out << C->print();
    }
    Out << ") {\n";
  }
  template <typename Stream>
  void PrintConstraintsPost(Stream &Out) {
    if (Constraints.empty()) {
      return;
    }
    Out << "}\n";
  }

  // Consts = consts found in LHS
  // ConstRefs = consts found in RHS
  template <typename Stream>
  void PrintConstDecls(Stream &Out) {
    size_t varnum = 0;

    auto Print = [&](SymbolTable &Syms, Inst *C){
      auto Name = "C" + std::to_string(varnum++);
      if (C->Width <= 64) {
        Out << "  auto " << Name << " = C("
            << C->Val.getBitWidth() <<", "
            << C->Val << ", B);\n";
      } else {
        Out << "  auto " << Name << " = C("
            << "APInt(" << C->Val.getBitWidth() << ", "
            << "\"" << llvm::toString(C->Val, 10, false) << "\", 10), B);\n";
      }
      Syms.T[C] = Name;
    };

    for (auto C : ConstRefs) {
      // if (Consts.find(C) == Consts.end()) {
        Print(*this, C);
      // }
    }
  }
};

template <typename Stream>
bool GenLHSMatcher(Inst *I, Stream &Out, SymbolTable &Syms, bool IsRoot = false) {
  if (!IsRoot) {
    if (I->K != souper::Inst::Var && Syms.Used.find(I) != Syms.Used.end()) {
      Out << "&" << Syms.T[I] << " <<= ";
    }
  }

  static std::set<Inst *> MatchedVals;
  if (IsRoot && I->K == Inst::Var) {
    if (MatchedVals.find(I) == MatchedVals.end()) {
      MatchedVals.insert(I);
      Out << "m_Value(" << Syms.T[I] << ")";
      return true;
    } else {
      Out << "m_Deferred(" << Syms.T[I] << ")";
    }
    return true;
  }

  auto It = MatchOps.find(I->K);
  if (It == MatchOps.end()) {
    llvm::errs() << "\nUnimplemented matcher:" << Inst::getKindName(I->K) << "\n";
    return false;
  }

  auto Op = It->second;

  Out << Op;

  if (!OnlyExplicitWidths) {
    if (I->K == Inst::SExt || I->K == Inst::ZExt || I->K == Inst::Trunc) {
      Out << I->Width << ", ";
    }
  }

  if (PredNames.find(I->K) != PredNames.end()) {
    Out << Syms.Preds[I] << ", ";
  }

  bool first = true;
  for (auto Child : I->Ops) {
    if (first) {
      first = false;
    } else {
      Out << ", ";
    }

    if (Child->K == Inst::Const) {
      if (Child->K != souper::Inst::Var && Syms.Used.find(Child) != Syms.Used.end()) {
        Out << "&" << Syms.T[Child] << " <<= ";
      }
      auto Str = llvm::toString(Child->Val, 10, false);
      if (Child->Width > 64) {
        Str = "\"" + Str + "\"";
      }
      if (OnlyExplicitWidths) {
        Out << "m_ExtInt(\"" << Str << "\", " << Child->Width << ")";
      } else {
        Out << "m_SpecificInt( " << Child->Width << "," << Str << ")";
      }
    } else if (Child->K == Inst::Var) {
      if (Child->Name.starts_with("symconst")) {
        if (MatchedVals.find(Child) == MatchedVals.end()) {
          MatchedVals.insert(Child);
          Out << "m_Constant(&" << Syms.T[Child] << ")";
        } else {
          Out << "m_Deferred(" << Syms.T[Child] << ")";
        }
      } else if (Child->Name.starts_with("constexpr")) {
        llvm::errs() << "FOUND A CONSTEXPR\n";
        return false;
      } else {
        if (MatchedVals.find(Child) == MatchedVals.end()) {
          MatchedVals.insert(Child);
          Out << "m_Value(" << Syms.T[Child] << ")";
        } else {
          Out << "m_Deferred(" << Syms.T[Child] << ")";
        }
      }
      // Syms.T[Child].pop_back();
    } else {
      if (!GenLHSMatcher(Child, Out, Syms)) {
        return false;
      }
    }

  }
  Out << ")";
  return true;
}

Inst *getSibling(Inst *Child, Inst *Parent) {
  if (!Child || !Parent) {
    return nullptr;
  }

  for (auto Op : Parent->Ops) {
    if (Op != Child && Op->Width == Child->Width) {
      return Op;
    }
  }
  return nullptr;
}

template <typename Stream>
bool GenRHSCreator(Inst *I, Stream &Out, SymbolTable &Syms, Inst *Parent = nullptr) {
//   if (!Parent && I->K == Inst::Const) {
//     Out << Syms.T[I];
//     if (Syms.T[I].starts_with("C")) {
//       Out << "(I)";
//     }
//     return true;
//   }

  auto It = CreateOps.find(I->K);
  if (It == CreateOps.end()) {
    llvm::errs() << "\nUnimplemented creator:" << Inst::getKindName(I->K) << "\n";
    return false;
  }
  auto Op = It->second;

  Out << "B->" << Op;
  bool first = true;
  for (auto Child : I->Ops) {
    if (first) {
      first = false;
    } else {
      Out << ", ";
    }
    // if (Child->K == Inst::BitWidth) {
    //   Out << "dummy";
    //   continue;
    // }
    if (Syms.T.find(Child) != Syms.T.end()) {
      Out << Syms.T[Child];
      if (Child->K == Inst::Const && Syms.T[Child].starts_with("C")) {
        auto Sib = getSibling(Child, I);
        std::string S;
        if (Syms.T.find(Sib) != Syms.T.end()) {
          if (Syms.T[Sib].starts_with("x")) {
            S = Syms.T[Sib];
          }
        }
        Out << "(" << S << ")"; // Ad-hoc type inference
      }
    } else {
      if (!GenRHSCreator(Child, Out, Syms, I)) {
        return false;
      }
    }

  }
  if (I->K == Inst::Trunc || I->K == Inst::SExt || I->K == Inst::ZExt) {
    if (!Parent) {
      Out << ", T(I)"; // Parent is rhs root
    } else {
      auto Cousin = getSibling(I, Parent);
      std::string S;
      if (Syms.T.find(Cousin) != Syms.T.end()) {
        if (Syms.T[Cousin].starts_with("x")) {
          S = Syms.T[Cousin];
        }
      }
      if (!S.empty()) {
        Out << ", T(" << S << ")"; // Ad-hoc type inference
      } else {
        Out << ", T(" << I->Width << ", B)";
      }
    }
  }
  Out << ")";

  return true;
}

template <typename Stream>
bool InitSymbolTable(ParsedReplacement Input, Stream &Out, SymbolTable &Syms) {
  auto Root = Input.Mapping.LHS;
  auto RHS = Input.Mapping.RHS;
  std::set<Inst *> LHSInsts;
   std::set<Inst *> Visited;

  std::vector<Inst *> Stack{Root};
  for (auto M : Input.PCs) {
    Stack.push_back(M.LHS);
    Stack.push_back(M.RHS);
  }

  int varnum = 0;
  while (!Stack.empty()) {
    auto I = Stack.back();
    Stack.pop_back();
    LHSInsts.insert(I);
    Visited.insert(I);
    if (I->K == Inst::Var) {
      if (Syms.T.find(I) == Syms.T.end()) {
        Syms.T[I] = ("x" + std::to_string(varnum++));
        // llvm::errs() << "Var1: " << I->Name << " -> " << Syms.T[I] << "\n";
      }
    }
//     if (I->K == Inst::Const) {
//       Syms.Consts.insert(I);
//     }
    for (int i = 0; i < I->Ops.size(); ++i) {
      if (Visited.find(I->Ops[i]) == Visited.end()) {
        Stack.push_back(I->Ops[i]);
      }
    }
  }

  Visited.clear();
  Stack = {Root};
  while (!Stack.empty()) {
    auto I = Stack.back();
    Stack.pop_back();
    Visited.insert(I);
    Syms.RegisterPred(I);
    for (int i = 0; i < I->Ops.size(); ++i) {
      if (Visited.find(I->Ops[i]) == Visited.end()) {
        Stack.push_back(I->Ops[i]);
      }
    }
  }

  Visited.clear();
  Stack.push_back(RHS);

  while (!Stack.empty()) {
    auto I = Stack.back();
    Stack.pop_back();
    Visited.insert(I);
    if (I->K == Inst::Const) {
      Syms.ConstRefs.insert(I);
    }

    if (LHSInsts.find(I) != LHSInsts.end() ) {
      if (Syms.Used.insert(I).second && Syms.T.find(I) == Syms.T.end()) {
        Syms.T[I] = ("x" + std::to_string(varnum++));
        // llvm::errs() << "Var0: " << I->Name << " -> " << Syms.T[I] << "\n";
      }
    }
    for (auto Child : I->Ops) {
      if (Visited.find(Child) == Visited.end()) {
        Stack.push_back(Child);
      }
    }
  }


  Visited.clear();
  for (auto M : Input.PCs) {
    Stack.push_back(M.LHS);
    Stack.push_back(M.RHS);
  }

  while (!Stack.empty()) {
    auto I = Stack.back();
    Stack.pop_back();
    Visited.insert(I);
    // if (I->K == Inst::Const) {
    //   Syms.ConstRefs.insert(I);
    // }

    if (LHSInsts.find(I) != LHSInsts.end()) {
      if (I->Width == 1 &&
        (I->K == Inst::SExt || I->K == Inst::ZExt || I->K == Inst::Trunc)) {
        if (Syms.T.find(I) == Syms.T.end() && Syms.Used.insert(I).second) {
          Syms.T[I] = ("x" + std::to_string(varnum++));
          // llvm::errs() << "Var0: " << I->Name << " -> " << Syms.T[I] << "\n";
        }
      }
    }

    for (auto Child : I->Ops) {
      if (Visited.find(Child) == Visited.end()) {
        Stack.push_back(Child);
      }
    }
  }

  if (!Syms.T.empty()) {
    Out << "llvm::Value ";
    bool first = true;
    for (auto &&S : Syms.T) {
      if (first) {
        first = false;
      } else {
        Out << ", ";
      }
      Out << "*" << S.second << " = nullptr";
    }
    Out << ";\n";
  }

//  varnum = 0;
//  for (auto &&P : Paths) {
//    if (P.first == Root || P.first->K == Inst::Var
//        || LHSRefs.find(P.first) == LHSRefs.end()) {
//      continue;
//    }
////    std::string Name = "I";
////    for (auto idx : P.second) {
////      auto NewName = "y" + std::to_string(varnum++);
////      Out << "auto " << NewName << " = cast<Instruction>(" << Name;
////      Out << ")->getOperand(" << idx << ");\n";
////      std::swap(Name, NewName);
////    }
////    Syms.T[P.first].push_back(Name);
//
//    auto Name = "y" + std::to_string(varnum++);
//    Out << "auto " << Name << " = util::node(I, ";
//    printPath(Out, P.second);
//    Out << ");\n";
//    Syms.T[P.first].push_back(Name);
//  }
  // Syms.T[Root].push_back("I");
  Syms.PrintPreds(Out);
  return true;
}

template <typename Stream>
bool GenMatcher(ParsedReplacement Input, Stream &Out, size_t OptID, bool WidthIndependent) {
  SymbolTable Syms;
  Out << "{\n";

  int prof = profit(Input);
  size_t LHSSize = souper::instCount(Input.Mapping.LHS);
  if (prof < 0 || LHSSize > 15) {
    llvm::errs() << "Skipping replacement profit < 0 or LHS size > 15\n";
    return false;
  }

  if (!InitSymbolTable(Input, Out, Syms)) {
    return false;
  }
//  Out << "  llvm::errs() << \"NOW \" << " << OptID << "<< \"\\n\";\n";

  auto F = "util::filter(F, " + std::to_string(OptID) + ") && ";
  Out << "if (" << F << "match(I, ";

  SymbolTable SymsCopy = Syms;
  if (Input.Mapping.LHS->K == Inst::DemandedMask) {
    if (!GenLHSMatcher(Input.Mapping.LHS->Ops[0], Out, SymsCopy, /*IsRoot = */true)) {
      return false;
    }
  } else {
    if (!GenLHSMatcher(Input.Mapping.LHS, Out, SymsCopy, /*IsRoot = */true)) {
      return false;
    }
  }
  Out << ")) {\n";

//  Input.print(llvm::errs(), true);
  Inst *DemandedMask = nullptr;
  if (Input.Mapping.LHS->K == Inst::DemandedMask) {
    DemandedMask = Input.Mapping.LHS->Ops[1];
    Syms.Constraints.push_back(new SymDB(Syms.T[Input.Mapping.LHS->Ops[1]]));
  }
  Syms.GenVarPropConstraints(Input.Mapping.LHS, WidthIndependent);
  Syms.GenDomConstraints(Input.Mapping.RHS);
  Syms.GenDFConstraints(Input.Mapping.LHS);
  if (!Syms.GenPCConstraints(Input.PCs)) {
    llvm::errs() << "Failed to generate PC constraints.\n";
    return false;
  }
  Syms.PrintConstraintsPre(Out);

  Syms.PrintConstDecls(Out);


  Out << "  auto ret";

  if (Syms.T.find(Input.Mapping.RHS) != Syms.T.end()) {
    Out << " = " << Syms.T[Input.Mapping.RHS];
    if (Syms.T[Input.Mapping.RHS].starts_with("C")) {
      Out << "(I)";
    }
    Out << ";";

  } else if (Input.Mapping.RHS->K == Inst::DemandedMask && Syms.T.find(Input.Mapping.RHS->Ops[0]) != Syms.T.end()) {
    assert(DemandedMask == Input.Mapping.RHS->Ops[1] && "DemandedMask mismatch");
    Out << " = " << Syms.T[Input.Mapping.RHS->Ops[0]];
    if (Syms.T[Input.Mapping.RHS->Ops[0]].starts_with("C")) {
      Out << "(I)";
    }
    Out << ";";
  } else if (Input.Mapping.RHS->K == Inst::Const) {
    Out << " APInt Result("
        << Input.Mapping.RHS->Width <<", "
        << Input.Mapping.RHS->Val << ");\n";
    Out << " = ConstantInt::get(TheContext, Result);";
  } else {
    Out << " = ";
    if (Input.Mapping.RHS->K == Inst::DemandedMask) {
      assert(DemandedMask == Input.Mapping.RHS->Ops[1] && "DemandedMask mismatch");

      if (!GenRHSCreator(Input.Mapping.RHS->Ops[0], Out, Syms)) {
        return false;
      }
    } else {
      if (!GenRHSCreator(Input.Mapping.RHS, Out, Syms)) {
        return false;
      }
    }
    Out << ";";
  }
  Out << "\nif (util::check_width(ret, I)) {\n";
  Out << "  St.hit(" << OptID << ", " << prof  << ");\n";
  Out << "  return ret;\n";
  Out << "\n}\n}\n}";

  Syms.PrintConstraintsPost(Out);

  return true;
}

std::string getLLVMInstKindName(Inst::Kind K) {
  StringRef str = MatchOps.find(K)->second;
  str.consume_front("m_");
  str.consume_back("(");
//  str.consume_front("NSW");
//  str.consume_front("NUW");
//  str.consume_front("NW");
  return str.str();
}

bool PCHasVar(const ParsedReplacement &Input) {
  std::vector<Inst *> Stack;
  for (auto &&PC : Input.PCs) {
    // if (PC.LHS->K == Inst::KnownOnesP || PC.LHS->K == Inst::KnownZerosP)
    //   continue;

    // if (PC.LHS->K == Inst::Eq && (PC.LHS->Ops[0]->K == Inst::BitWidth ||
    //                               PC.LHS->Ops[1]->K == Inst::BitWidth )) {
    //   continue;
    // }
    Stack.push_back(PC.LHS);
    Stack.push_back(PC.RHS);
  }

  std::set<Inst *> Visited;
  std::vector<Inst *> Vars;

  while (!Stack.empty()) {
    Inst *I = Stack.back();
    Stack.pop_back();

    if (Visited.count(I)) {
      continue;
    }
    Visited.insert(I);

    if (I->K == Inst::Var) {
      Vars.push_back(I);
    }

    for (auto &&Op : I->Ops) {
      if (I->K == Inst::KnownOnesP || I->K == Inst::KnownZerosP || I->K == Inst::BitWidth)
        continue;
      Stack.push_back(Op);
    }
  }


  for (auto &&V : Vars) {
    // llvm::errs() << V->Name << "\n";
    if (!V->Name.starts_with("sym")) {
      return true;
    }
  }

  return false;
}


int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);
  KVStore *KV = 0;

  std::unique_ptr<Solver> S = 0;
  S = GetSolver(KV);

  std::unordered_set<size_t> optnumbers;
  std::vector<size_t> Ordered;
  if (ListFile != "") {
    std::ifstream in(ListFile);
    size_t num;
    while (in >> num) {
      optnumbers.insert(num);
      if (Sort) {
        Ordered.push_back(num);
      }
    }
  }

  auto MB = MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (!MB) {
    llvm::errs() << MB.getError().message() << '\n';
    return 1;
  }

  InstContext IC;
  std::string ErrStr;

  auto &&Data = (*MB)->getMemBufferRef();
  auto Inputs = ParseReplacements(IC, Data.getBufferIdentifier(),
                                  Data.getBuffer(), ErrStr);

  std::set<Inst::Kind> Kinds;
  std::sort(Inputs.begin(), Inputs.end(),
            [&Kinds](const ParsedReplacement& A, const ParsedReplacement &B) {
    Kinds.insert(A.Mapping.LHS->K);
    Kinds.insert(B.Mapping.LHS->K);

//    if (A.Mapping.LHS->K < B.Mapping.LHS->K) {
//      return true;
//    } else if (A.Mapping.LHS->K == B.Mapping.LHS->K) {
//      return profitability(A) > profitability(B);
//    } else {
//      return false;
//    }
    return A.Mapping.LHS->K < B.Mapping.LHS->K;
  });

  if (!ErrStr.empty()) {
    llvm::errs() << ErrStr << '\n';
    return 1;
  }

  size_t optnumber = 0;

  Inst::Kind Last = Inst::Kind::None;

  bool first = true;
  bool outputs = false;

  std::map<size_t, std::string> Results;

  for (auto &&Input: Inputs) {
    auto SKIP = [&] (auto Msg) {
      Input.print(llvm::errs(), true);
      llvm::errs() << Msg << "\n\n\n";
      llvm::errs().flush();
    };

    if (PCHasVar(Input)) {
      SKIP("SKIP PC has var.");
      continue;
    }

    if (Input.Mapping.LHS == Input.Mapping.RHS) {
      SKIP("SKIP LHS = RHS.");
      continue;
    }
    if (IgnoreDF) {
      if (Input.Mapping.LHS->DemandedBits.getBitWidth()
          == Input.Mapping.LHS->Width && !Input.Mapping.LHS->DemandedBits.isAllOnesValue()) {

        continue;
      }
      std::vector<Inst *> Vars;
      findVars(Input.Mapping.LHS, Vars);
      findVars(Input.Mapping.RHS, Vars);
      bool found = false;
      for (auto V : Vars) {
        if (V->KnownOnes.getBitWidth() == V->Width && V->KnownOnes != 0) {
          found = true;
          break;
        }

        if (V->KnownZeros.getBitWidth() == V->Width && V->KnownZeros != 0) {
          found = true;
          break;
        }
//        if (!V->Range.isFullSet() || !V->Range.isEmptySet()) {
//          continue;
//        }
      }
      if (found) {
        SKIP("SKIP Unsupported DF.");
        continue;
      }
    }

    if (Input.Mapping.LHS->K != Last && !NoDispatch) {
      if (!first) {
        llvm::outs() << "}\n";
      }
      first = false;
      llvm::outs() << "if (";
      switch (Input.Mapping.LHS->K) {
        case Inst::AddNW:
        case Inst::AddNUW:
        case Inst::AddNSW:
        case Inst::Add: llvm::outs()
          << "I->getOpcode() == Instruction::Add"; break;

        case Inst::SubNW:
        case Inst::SubNUW:
        case Inst::SubNSW:
        case Inst::Sub: llvm::outs()
          << "I->getOpcode() == Instruction::Sub"; break;

        case Inst::MulNW:
        case Inst::MulNUW:
        case Inst::MulNSW:
        case Inst::Mul: llvm::outs()
          << "I->getOpcode() == Instruction::Mul"; break;

        case Inst::ShlNW:
        case Inst::ShlNUW:
        case Inst::ShlNSW:
        case Inst::Shl: llvm::outs()
          << "I->getOpcode() == Instruction::Shl"; break;

        case Inst::And: llvm::outs()
          << "I->getOpcode() == Instruction::And"; break;
        case Inst::Or: llvm::outs()
          << "I->getOpcode() == Instruction::Or"; break;
        case Inst::Xor: llvm::outs()
          << "I->getOpcode() == Instruction::Xor"; break;
        case Inst::SRem: llvm::outs()
          << "I->getOpcode() == Instruction::SRem"; break;
        case Inst::URem: llvm::outs()
          << "I->getOpcode() == Instruction::URem"; break;
        case Inst::SDiv: llvm::outs()
          << "I->getOpcode() == Instruction::SDiv"; break;
        case Inst::UDiv: llvm::outs()
          << "I->getOpcode() == Instruction::UDiv"; break;
        case Inst::ZExt: llvm::outs()
          << "I->getOpcode() == Instruction::ZExt"; break;
        case Inst::SExt: llvm::outs()
          << "I->getOpcode() == Instruction::SExt"; break;
        case Inst::Trunc: llvm::outs()
          << "I->getOpcode() == Instruction::Trunc"; break;
        case Inst::Select: llvm::outs()
          << "I->getOpcode() == Instruction::Select"; break;
        case Inst::Phi: llvm::outs()
          << "isa<PHINode>(I)"; break;
        case Inst::Eq:
        case Inst::Ne:
        case Inst::Ult:
        case Inst::Slt:
        case Inst::Ule:
        case Inst::Sle: llvm::outs()
          << "I->getOpcode() == Instruction::ICmp"; break;

        default: llvm::outs() << "true";
      }
      llvm::outs() << ") {\n";
      outputs = true;
    }
    Last = Input.Mapping.LHS->K;

    std::string Str;
    llvm::raw_string_ostream Out(Str);

    if (GenMatcher(Input, Out, optnumber, OnlyExplicitWidths)) {
      auto current = optnumber++;
      if (!optnumbers.empty()
          && optnumbers.find(current) == optnumbers.end()) {
        Out.flush();
        Str.clear();
        llvm::errs() << "Opt " << current <<  " skipped on demand.\n";
        SKIP("SKIP Filtered.");
        continue;
      } else {
        if (ListOutFile != "") {
          std::ofstream O(ListOutFile, std::ios::app);
          ReplacementContext RC;
          std::string IRComment =
          Input.getLHSString(RC, true) +
          Input.getRHSString(RC, true) + "\n";

          O << IRComment << '\n' << std::flush;
        }
      }

      InfixPrinter P(Input, false);
      std::string S;
      llvm::raw_string_ostream Out(S);
      P(Out);
      Out.flush();

      ReplacementContext RC;
      std::string IRComment =
        "/* Opt : " +
        std::to_string(current) + "\n" +
        Input.getLHSString(RC, true) +
        Input.getRHSString(RC, true) + "\n" + S + "*/\n";

      if (NoDispatch && Sort && !Ordered.empty()) {
        Results[current] = IRComment + Str + "\n";
      } else {

        llvm::outs() << IRComment << Str << "\n";
        llvm::outs().flush();
        outputs= true;
      }

    } else {
      SKIP("SKIP Failed to generate matcher.");
    }
  }
  if (outputs && !NoDispatch) {
    llvm::outs() << "}\n";
  }

  if (NoDispatch && Sort && !Ordered.empty()) {
    for (auto N : Ordered) {
      llvm::outs() << Results[N];
    }
  }

//  llvm::outs() << "end:\n";

  return 0;
}
