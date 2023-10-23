#define _LIBCPP_DISABLE_DEPRECATION_WARNINGS

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/KnownBits.h"
#include "souper/Generalize/Generalize.h"
#include "souper/Infer/AliveDriver.h"
#include "souper/Infer/Preconditions.h"
#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/ConstantSynthesis.h"
#include "souper/Infer/Pruning.h"
#include "souper/Infer/SynthUtils.h"
#include "souper/Inst/InstGraph.h"
#include "souper/Parser/Parser.h"
#include "souper/Generalize/Reducer.h"
#include "souper/Tool/GetSolver.h"
#include "souper/Util/DfaUtils.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"

#include <cstdlib>
#include <sstream>
#include <iostream>
#include <optional>



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



struct SymbolTable {

  // Every object is a list of strings
// Serialize through constructor
// deserialize through templated getter

struct StoredObject {
  std::vector<std::string> Data;
  enum class Attr {
    Type,
    WidthIndependent
  };
  std::unordered_map<Attr, std::string> Attributes;

  StoredObject() {
    Attributes[Attr::Type] = "none";
  }

  StoredObject(const ParsedReplacement &PR) {
    Data.push_back("");
    llvm::raw_string_ostream OS(Data.back());
    PR.print(OS);
    OS.flush();
    Attributes[Attr::Type] = "replacement";
  }

  StoredObject(std::unique_ptr<llvm::Module> M) {
    Data.push_back("");
    llvm::raw_string_ostream OS(Data.back());
    M->print(OS, nullptr);
    OS.flush();
    Attributes[Attr::Type] = "module";
  }

  template <typename T>
  std::optional<T> get(SymbolTable *S) {
    return std::nullopt;
  }

  template <>
  std::optional<ParsedReplacement> get(SymbolTable *S) {
    if (Data.size() != 1) return std::nullopt;
    std::string ErrStr;
    llvm::MemoryBufferRef MB(Data[0], "temp");
    auto Rep = ParseReplacement(S->IC, MB.getBufferIdentifier(),
                                MB.getBuffer(), ErrStr);
    if (!ErrStr.empty()) {
      llvm::errs() << ErrStr << '\n';
      return std::nullopt;
    }
    return Rep;
  }

  template <>
  std::optional<std::unique_ptr<llvm::Module>> get(SymbolTable *S) {
    if (Data.size() != 1) return std::nullopt;
    std::string ErrStr;
    llvm::MemoryBufferRef MB(Data[0], "temp");
    // auto M = getLazyIRModule(MB, ErrStr, S->LC,
    //                          /*ShouldLazyLoadMetadata=*/true);
    std::unique_ptr<llvm::Module> M;
    if (!M) {
      llvm::errs() << ErrStr << '\n';
      return std::nullopt;
    }
    return std::move(M);
  }

};

  SymbolTable(InstContext &IC_) : IC(IC_) {
    push();
  }

  InstContext &IC;
  LLVMContext LC;
  std::vector<std::unordered_map<std::string, StoredObject>> Tables;

  void push() {
    Tables.push_back({});
  }
  void pop() {
    if (Tables.size() > 1) {
      Tables.pop_back();
    } else {
      llvm::errs() << "Reached bottom of stack\n";
    }
  }

  std::optional<ParsedReplacement> get(const std::string &Name) {
    for (auto I = Tables.rbegin(), E = Tables.rend(); I != E; ++I) {
      auto It = I->find(Name);
      if (It != I->end())
        return It->second.get<ParsedReplacement>(this);
    }
    return std::nullopt;
  }

  std::optional<ParsedReplacement> warn_get(const std::string &Name) {
    if (auto Obj = get(Name)) {
      return Obj;
    } else {
      llvm::errs() << "Unknown name: " << Name << '\n';
      return std::nullopt;
    }
  }
  void put(const std::string &Name, const ParsedReplacement &PR) {
    // PR.print(llvm::errs(), true);
    Tables.back()[Name] = StoredObject(PR);
  }

  void current(const ParsedReplacement &PR, bool WIFlag = false) {
    if (Tables.empty()) push();
    Tables.back()["_"] = StoredObject(PR);
    Tables.back()["_"].Attributes[StoredObject::Attr::WidthIndependent] =
      WIFlag ? "true" : "false";
  }

  void current(const std::string &name) {
    if (name == "_") return;
    if (Tables.empty()) push();
    if (auto I = warn_get(name)) {
      Tables.back()["_"] = I.value();
    }
  }

};

void PrettyPrint(std::string Name, SymbolTable &Tab) {
  if (Name != "_") {
    llvm::outs() << Name << '\n';
    for (int i = 0; i < Name.size(); ++i) {
      llvm::outs() << '=';
    }
    llvm::outs() << '\n';
  }
  auto In = Tab.warn_get(Name);
  if (!In) return;
  InfixPrinter IP(In.value());
  IP(llvm::outs());
}

struct REPL {
  REPL(InstContext &IC, Solver *S, std::vector<ParsedReplacement> &Inputs)
      : IC(IC), S(S), Inputs(Inputs), Tab(IC) {
    for (size_t i = 0 ; i < Inputs.size(); ++i) {
      auto Name = "_" + std::to_string(i);
      Tab.put(Name, Inputs[i]);
    }
    // The current input is _ by default
    if (!Inputs.empty()) {
      Tab.put("_", Inputs[0]);
    }
  }
  InstContext &IC;
  Solver *S;
  std::vector<ParsedReplacement> &Inputs;
  SymbolTable Tab;

  bool match(std::string in, const std::set<std::string> &possibilities) {
    return possibilities.find(in) != possibilities.end();
  }

  bool dispatch(std::vector<std::string> Cmds) {
    if (Cmds.size() == 1) {
      Cmds.push_back("_");
    }

    // print
    if (match(Cmds[0], {"p", "print"})) {
      if (Cmds.size() != 2) {
        llvm::errs() << "Usage: print <name>\n";
        return true;
      }
      PrettyPrint(Cmds[1], Tab);

      return true;
    }

    // verify
    if (match(Cmds[0], {"v", "verify"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        if (Verify(In.value(), IC, S)) {
          llvm::outs() << "Valid\n";
        } else {
          llvm::outs() << "Invalid\n";
        }
      }
      Tab.current(Cmds[1]);
      return true;
    }

    // generalize
    if (match(Cmds[0], {"g", "gen", "generalize"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        if (auto Gen = GeneralizeRep(In.value(), IC, S)) {
          InfixPrinter IP(Gen.value());
          IP(llvm::outs());
          Tab.current(Gen.value(), true);
        } else {
          llvm::outs() << "No generalization found\n";
        }
      }
      return true;
    }

    // matcher-gen
    if (match(Cmds[0], {"mg", "matcher-gen"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        // execute the matcher-gen binary
        std::string MatcherGenOutput;
        if (auto In = Tab.warn_get(Cmds[1])) {
          std::string MatcherGenCommand = "./matcher-gen";
          FILE *MatcherGenPipe = popen(MatcherGenCommand.c_str(), "w");
          if (MatcherGenPipe) {
            // Write the contents of In to the pipe

            std::string data;
            llvm::raw_string_ostream OS(data);
            In.value().print(OS, true);

            fwrite(data.c_str(), sizeof(char), data.size(), MatcherGenPipe);
            pclose(MatcherGenPipe);
          } else {
            llvm::errs() << "Failed to execute matcher-gen\n";
          }
          char buffer[1024];
          while (fgets(buffer, sizeof(buffer), MatcherGenPipe) != NULL) {
            MatcherGenOutput += buffer;
          }
          pclose(MatcherGenPipe);

          // store the output as text
          llvm::outs() << MatcherGenOutput;
        }

      }
      return true;
    }


    // infer
    if (match(Cmds[0], {"i", "infer"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        std::vector<Inst *> RHSs;
        auto Rep = In.value();
        if (std::error_code EC = S->infer(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                        RHSs, false, IC)) {
        llvm::errs() << EC.message() << '\n';
      }
      if (!RHSs.empty()) {
        size_t i = 0;
        for (auto RHS : RHSs) {
          llvm::outs() << "Found RHS:\n";
          auto Out = Rep;
          Rep.Mapping.RHS = RHS;
          InfixPrinter IP(Rep);
          IP(llvm::outs());
          Tab.put("_" + std::to_string(i++), Rep);
        }
        Tab.current("_0");
      } else {
        llvm::errs() << "No RHS found\n";
      }

      }
      return true;
    }

    // push
    if (match(Cmds[0], {"push"})) {
      Tab.push();
      return true;
    }

    // pop
    if (match(Cmds[0], {"pop"})) {
      Tab.pop();
      return true;
    }

    // cp
    if (match(Cmds[0], {"cp"})) {
      // save to a variable
      // todo
    }

    // TODO: read, save.

    return false;
  }

  bool operator()() {
    std::string Line;
    do {
      llvm::outs() << "souper-repl> ";
      if (!std::getline(std::cin, Line)) break;

      std::istringstream SS(Line);
      std::vector<std::string> Cmds;
      std::string Cmd;
      while (SS >> Cmd) {
        Cmds.push_back(Cmd);
      }
      if (Cmds.empty()) continue;
      if (Cmds[0] == "exit" || Cmds[0] == "quit" || Cmds[0] == "q") break;
      if (dispatch(Cmds)) continue;
      if (auto Obj = Tab.get(Cmds[0])) {
        Cmds.push_back(Cmds[0]);
        Cmds[0] = "p";
        dispatch(Cmds);
        continue;
      } else {
        llvm::errs() << "Unknown command or name: " << Cmds[0] << '\n';
      }
    } while(std::cin.good());
    return true;
  }
};

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);
  KVStore *KV = 0;

  std::unique_ptr<Solver> S = 0;
  S = GetSolver(KV);

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


  if (!ErrStr.empty()) {
    std::vector<ReplacementContext> Contexts;
    Inputs = ParseReplacementLHSs(IC, Data.getBufferIdentifier(), Data.getBuffer(),
                                Contexts, ErrStr);
  }

  llvm::outs() << "Got " << Inputs.size() << " inputs\n";
  REPL SouperRepl(IC, S.get(), Inputs);
  return SouperRepl();
}
