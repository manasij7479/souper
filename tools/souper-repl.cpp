#define _LIBCPP_DISABLE_DEPRECATION_WARNINGS

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Interpreter/Interpreter.h"

#include "llvm/Support/ManagedStatic.h" // llvm_shutdown
#include "llvm/Support/TargetSelect.h"

llvm::ExitOnError ExitOnErr;

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/KnownBits.h"
#include "souper/Extractor/Candidates.h"
#include "souper/Generalize/Generalize.h"
#include "souper/Infer/AliveDriver.h"
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
#include <sys/wait.h>

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

  StoredObject(const std::string &Str, std::string Type = "string") {
    Data.push_back(Str);
    Attributes[Attr::Type] = "string";
  }

  StoredObject(const ParsedReplacement &PR) {
    Data.push_back("");
    llvm::raw_string_ostream OS(Data.back());

    if (PR.Mapping.RHS) {
      PR.print(OS, true);
      OS.flush();
      Attributes[Attr::Type] = "replacement";
    } else {
      ReplacementContext RC;
      PR.printLHS(OS, RC, true);
      OS.flush();
      Attributes[Attr::Type] = "lhs";
    }
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
  std::optional<std::string> get(SymbolTable *S) {
    if (Data.size() != 1) return std::nullopt;
    return Data[0];
  }

  template <>
  std::optional<ParsedReplacement> get(SymbolTable *S) {
    if (Attributes[Attr::Type] != "replacement" && Attributes[Attr::Type] != "lhs") {
      llvm::errs() << "Expected replacement, got " << Attributes[Attr::Type] << '\n';
      return std::nullopt;
    }
    if (Data.size() != 1) return std::nullopt;
    std::string ErrStr;
    llvm::MemoryBufferRef MB(Data[0], "temp");

    if (Attributes[Attr::Type] == "replacement") {
      auto Rep = ParseReplacement(S->IC, MB.getBufferIdentifier(),
                                  MB.getBuffer(), ErrStr);
      if (!ErrStr.empty()) {
        llvm::errs() << ErrStr << '\n';
        return std::nullopt;
      }
      return Rep;
    }
    if (Attributes[Attr::Type] == "lhs") {
      ReplacementContext RC;
      auto Rep = ParseReplacementLHS(S->IC, MB.getBufferIdentifier(),
                                  MB.getBuffer(), RC, ErrStr);
      if (!ErrStr.empty()) {
        llvm::errs() << ErrStr << '\n';
        return std::nullopt;
      }
      return Rep;
    }
    return std::nullopt;
  }

  template <>
  std::optional<std::unique_ptr<llvm::Module>> get(SymbolTable *S) {
    if (Data.size() != 1) return std::nullopt;
    std::string ErrStr;
    auto &&MB = llvm::MemoryBuffer::getMemBufferCopy(Data[0]);
    // std::make_unique<llvm::MemoryBuffer>(Data[0], "temp");
    llvm::SMDiagnostic Err;
    auto &&M = getLazyIRModule(std::move(MB), Err, S->LC,
                             /*ShouldLazyLoadMetadata=*/true);
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

  std::optional<StoredObject> get(const std::string &Name) {
    for (auto I = Tables.rbegin(), E = Tables.rend(); I != E; ++I) {
      auto It = I->find(Name);
      if (It != I->end())
        return It->second;
    }
    return std::nullopt;
  }

  // std::optional<std::string> getStr(const std::string &Name) {
  //   for (auto I = Tables.rbegin(), E = Tables.rend(); I != E; ++I) {
  //     auto It = I->find(Name);
  //     if (It != I->end())
  //       return It->second.get<std::string>(this);
  //   }
  //   return std::nullopt;
  // }

  std::optional<StoredObject> warn_get(const std::string &Name, std::string Type = "") {
    if (auto Obj = get(Name)) {
      if (Type != "" && Obj->Attributes[StoredObject::Attr::Type] != Type) {
        llvm::errs() << "Expected " << Type << ", got " << Obj->Attributes[StoredObject::Attr::Type] << '\n';
        return std::nullopt;
      }

      return Obj;
    } else {
      llvm::errs() << "Unknown name: " << Name << '\n';
      return std::nullopt;
    }
  }
  void put(const std::string &Name, const ParsedReplacement &PR) {
    Tables.back()[Name] = StoredObject(PR);
  }

  void put(const std::string &Name, std::string Str) {
    Tables.back()[Name] = StoredObject(Str);
  }

  void put(const std::string &Name, StoredObject Obj) {
    Tables.back()[Name] = Obj;
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

  if (In.value().Attributes[SymbolTable::StoredObject::Attr::Type] == "replacement" ||
      In.value().Attributes[SymbolTable::StoredObject::Attr::Type] == "lhs") {
    auto Rep = In.value().get<ParsedReplacement>(&Tab);

    bool WIFlag = In.value().Attributes[SymbolTable::StoredObject::Attr::WidthIndependent] == "true";
    InfixPrinter IP(Rep.value(), !WIFlag);
    IP(llvm::outs());
  } else if (In.value().Attributes[SymbolTable::StoredObject::Attr::Type] == "string") {
    llvm::outs() << In.value().Data[0] << '\n';
  }
}


// FIXME!!!!! Language Design and actual parser
// Think about the amb idea
// cmd1 (> save1) (| cmd2 (>save2)) ...
// write a real parser instead of this weird state machine if the dsl has to evolve further
std::vector<std::pair<std::vector<std::string>, std::string>> SplitCommands(std::vector<std::string> Input) {
  std::vector<std::pair<std::vector<std::string>, std::string>> Result;
  bool pre_redirect = true;
  bool expect_pipe = false;
  Result.push_back({});
  for (auto Atom : Input) {
    if (Atom  == ">") {
      pre_redirect = false;
      expect_pipe = false;
      continue;
    }
    if (Atom == "|") {
      pre_redirect = true;
      Result.push_back({});
      expect_pipe = false;
      continue;
    }

    if (expect_pipe && Atom != "|") {
      llvm::errs() << "Expected pipe, got " << Atom << '\n';
      return {};
    }

    if (!pre_redirect) {
      Result.back().second = Atom;
      expect_pipe = true;
    } else {
      Result.back().first.push_back(Atom);
    }

  }
  return Result;
}

std::optional<std::string> executeCommandWithInput(const std::string& command, const std::string& input) {
    int pipeToChild[2];
    int pipeToParent[2];

    if (pipe(pipeToChild) == -1 || pipe(pipeToParent) == -1) {
        perror("pipe");
        return "";
    }

    pid_t childPID = fork();

    if (childPID == -1) {
        perror("fork");
        return "";
    }

    if (childPID == 0) { // Child process
        close(pipeToChild[1]);
        close(pipeToParent[0]);

        // Redirect standard input and output
        dup2(pipeToChild[0], STDIN_FILENO);
        dup2(pipeToParent[1], STDOUT_FILENO);

        close(pipeToChild[0]);
        close(pipeToParent[1]);

        // Execute the command
        execl("/bin/sh", "sh", "-c", command.c_str(), NULL);
        _exit(1);
    } else { // Parent process
        close(pipeToChild[0]);
        close(pipeToParent[1]);

        // Write input to the child process
        if (!input.empty()) {
            if (write(pipeToChild[1], input.c_str(), input.size()) == -1) {
                perror("write");
                return "";
            }
        }

        close(pipeToChild[1]);

        // Read the output from the child process
        std::string result;
        char buffer[128];
        ssize_t bytesRead;
        while ((bytesRead = read(pipeToParent[0], buffer, sizeof(buffer))) > 0) {
            result.append(buffer, bytesRead);
        }

        close(pipeToParent[0]);

        // Wait for the child process to exit
        int status;
        waitpid(childPID, &status, 0);

        if (WIFEXITED(status)) {
            int exitStatus = WEXITSTATUS(status);
            return result;
        }

        return std::nullopt;
    }
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

    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    CB.SetCompilerArgs({"-std=c++20", "-O0", "-g0"});
    CI = ExitOnErr(CB.CreateCpp());
    Interp = ExitOnErr(clang::Interpreter::create(std::move(CI)));
  }

  InstContext &IC;
  ExprBuilderContext EBC;
  Solver *S;
  std::vector<ParsedReplacement> &Inputs;
  SymbolTable Tab;

  clang::IncrementalCompilerBuilder CB;
  std::unique_ptr<clang::CompilerInstance> CI;
  std::unique_ptr<clang::Interpreter> Interp;
  llvm::llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  std::vector<ParsedReplacement> Extract(llvm::Module *M) {
    std::vector<ParsedReplacement> Results;
    for (auto &&F : *M) {
      if (F.isDeclaration()) {
        continue;
      }
      auto Candidates = ExtractCandidates(F, IC, EBC);
      ParsedReplacement PR;
      for (auto &Cand : Candidates.Blocks) {
        PR.BPCs = Cand->BPCs;
        PR.PCs = Cand->PCs;
        for (auto &Rep : Cand->Replacements) {
          PR.Mapping = Rep.Mapping;
          Results.push_back(PR);
        }
      }
    }
    return Results;
  }

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
        return false;
      }

      PrettyPrint(Cmds[1], Tab);
      Tab.current(Cmds[1]);

      return true;
    }

    // dump string
    if (match(Cmds[0], {"dump", "dump-string"})) {
      if (Cmds.size() != 2) {
        llvm::errs() << "Usage: dump-string <name>\n";
        return false;
      }

      if (auto In = Tab.warn_get(Cmds[1])) {
        for (auto &Str : In->Data) {
          llvm::outs() << Str << '\n';
        }
        return true;
      }
      return false;
    }

    // verify
    if (match(Cmds[0], {"v", "verify"})) {
      if (auto In = Tab.warn_get(Cmds[1], "replacement")) {

        if (Verify(In->get<ParsedReplacement>(&Tab).value(), IC, S)) {
          llvm::outs() << "Valid\n";
          Tab.current(Cmds[1]);
          return true;
        } else {
          llvm::outs() << "Invalid\n";
          return false;
        }
      }
      return false;
    }

    // generalize
    if (match(Cmds[0], {"g", "gen", "generalize"})) {
      if (auto In = Tab.warn_get(Cmds[1], "replacement")) {

        ParsedReplacement Rep = In->get<ParsedReplacement>(&Tab).value();
        if (auto Gen = GeneralizeRep(Rep, IC, S)) {
          InfixPrinter IP(Gen.value(), false);
          IP(llvm::outs());
          Tab.current(Gen.value(), true);
          return true;
        } else {
          llvm::outs() << "No generalization found\n";
          return false;
        }
      }
      return false;
    }

    // reduce
    if (match(Cmds[0], {"r", "reduce"})) {
      if (auto In = Tab.warn_get(Cmds[1], "replacement")) {
        ParsedReplacement Rep = In->get<ParsedReplacement>(&Tab).value();
        auto Red = ReduceBasic(IC, S, Rep);
        InfixPrinter IP(Red);
        IP(llvm::outs());
        bool WIFlag = In->Attributes[SymbolTable::StoredObject::Attr::WidthIndependent] == "true";
        Tab.current(Red, WIFlag);
        return true;
      }
      return false;
    }

    // reduce-poison
    if (match(Cmds[0], {"rp", "reduce-poison"})) {
      if (auto In = Tab.warn_get(Cmds[1], "replacement")) {
        ParsedReplacement Rep = In->get<ParsedReplacement>(&Tab).value();
        auto Red = ReducePoison(IC, S, Rep);
        InfixPrinter IP(Red);
        IP(llvm::outs());
        bool WIFlag = In->Attributes[SymbolTable::StoredObject::Attr::WidthIndependent] == "true";
        Tab.current(Red, WIFlag);
        return true;
      }
      return false;
    }

    // matcher-gen
    if (match(Cmds[0], {"mg", "matcher-gen", "matcher"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        // execute the matcher-gen binary
        std::string MatcherGenOutput;
        if (auto In = Tab.warn_get(Cmds[1], "replacement")) {

          // get width indepdendent flag from In
          auto WIFlag = In->Attributes[SymbolTable::StoredObject::Attr::WidthIndependent] == "true";
          std::string MatcherGenCommand = "./matcher-gen";
          if (WIFlag) {
            MatcherGenCommand += " --explicit-width-checks ";
          }

          std::string data;
          llvm::raw_string_ostream OS(data);
          In->get<ParsedReplacement>(&Tab).value().print(OS, true);
          auto MatcherGenOutput = executeCommandWithInput(MatcherGenCommand, OS.str());

          if (MatcherGenOutput.has_value()) {
            llvm::outs() << "Generated matcher successfully.\n";
            Tab.put("_", SymbolTable::StoredObject(MatcherGenOutput.value(), "matcher"));
            return true;
          } else {
            llvm::errs() << "Matcher generation failed.\n";
            return false;
          }
        }
      }
      return false;
    }

    // shrink
    if (match(Cmds[0], {"s", "shrink"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        ParsedReplacement Rep = In->get<ParsedReplacement>(&Tab).value();
        // enforce that type of In is replacement

        if (In->Attributes[SymbolTable::StoredObject::Attr::Type] != "replacement") {
          llvm::errs() << "Expected replacement, got " << In->Attributes[SymbolTable::StoredObject::Attr::Type] << '\n';
          return false;
        }

        size_t Target = 8;
        if (Cmds.size() == 3) {
          Target = std::stoi(Cmds[2]);
        }

        if (auto Shr = ShrinkRep(Rep, IC, S, Target)) {
          InfixPrinter IP(Shr.value());
          IP(llvm::outs());
          Tab.current(Shr.value());
          return true;
        } else {
          llvm::outs() << "Could not shrink.\n";
          return false;
        }
      }
      return false;
    }

    // extract
    if (match(Cmds[0], {"e", "extract"})) {
      if (auto In = Tab.warn_get(Cmds[1], "module")) {
        auto M = In->get<std::unique_ptr<llvm::Module>>(&Tab).value();
        auto Results = Extract(M.get());
        for (size_t i = 0; i < Results.size(); ++i) {
          auto Name = "_" + std::to_string(i);
          Tab.put(Name, Results[i]);
          PrettyPrint(Name, Tab);
        }
        if (!Results.empty()) {
          Tab.current("_0");
        }
        return true;
      }
      return false;
    }

    // infer
    if (match(Cmds[0], {"i", "infer"})) {
      if (auto In = Tab.warn_get(Cmds[1])) {
        std::vector<Inst *> RHSs;
        auto Rep = In->get<ParsedReplacement>(&Tab).value();

        if (std::error_code EC = S->infer(Rep.BPCs, Rep.PCs, Rep.Mapping.LHS,
                                        RHSs, false, IC)) {
          llvm::errs() << EC.message() << '\n';
        }
        if (!RHSs.empty()) {
          size_t i = 0;
          for (auto RHS : RHSs) {
            // llvm::outs() << "Found RHS:\n";
            auto Out = Rep;
            Rep.Mapping.RHS = RHS;
            InfixPrinter IP(Rep);
            IP(llvm::outs());
            if (RHSs.size() > 1) {
              Tab.put("_" + std::to_string(i++), Rep);
            } else {
              Tab.current(Rep);
            }
          }
          if (RHSs.size() > 1) {
            Tab.current("_0");
          }
        } else {
          llvm::errs() << "No RHS found\n";
        }
      }
      return true;
    }

    // constant synthesis

    // Compile matcher

    // generic exec
    if (match(Cmds[0], {"exec"})) {
      std::string Command;
      std::string stdin;
      if (auto In = Tab.get(Cmds[1])) {
        for (size_t i = 2; i < Cmds.size(); ++i) {
          Command += Cmds[i] + " ";
        }
        stdin = In->get<std::string>(&Tab).value();
      } else {
        for (size_t i = 1; i < Cmds.size(); ++i) {
          Command += Cmds[i] + " ";
        }
      }

      auto ExecOutput = executeCommandWithInput(Command, stdin);

      if (ExecOutput.has_value()) {
        if (ExecOutput.value() != "") {
          llvm::outs() << ExecOutput.value();
          Tab.put("_", SymbolTable::StoredObject(ExecOutput.value(), "string"));
        }
        return true;
      } else {
        llvm::errs() << "Execution failed.\n";
        return false;
      }

      return false;
    }

    // undo
    if (match(Cmds[0], {"undo"})) {
      if (Interp->Undo()) {
        llvm::errs() << "Nothing to undo.\n";
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

    // save
    if (match(Cmds[0], {"save"})) {
      // save to a file

      if (auto In = Tab.warn_get("_")) {
        std::error_code EC;
        llvm::raw_fd_ostream OutFile(Cmds[1], EC);
        if (EC) {
          llvm::errs() << "Could not save to file " << Cmds[2] << '\n';
          return false;
        } else {
          OutFile << In->get<std::string>(&Tab).value();
          OutFile.close();
          llvm::outs() << "Saved to file " << Cmds[2] << '\n';
          return true;
        }
      }
      return false;
    }

    // read to _
    if (match(Cmds[0], {"read"})) {
      std::string ErrStr;
      auto MB = MemoryBuffer::getFileOrSTDIN(Cmds[1]);
      if (!MB) {
        llvm::errs() << MB.getError().message() << '\n';
        return false;
      }
      auto Data = std::string((*MB)->getMemBufferRef().getBuffer());
      llvm::outs() << Data << "\n";
      Tab.put("_", SymbolTable::StoredObject(Data, "string"));
      return true;
    }
    return false;
  }

  std::vector<std::string> split(const std::string &S) {
    std::istringstream SS(S);
    std::vector<std::string> Cmds;
    std::string Cmd;
    while (SS >> Cmd) {
      Cmds.push_back(Cmd);
    }
    return Cmds;
  }

  // TODO: Might have to implement context sensitive lookahead
  std::vector<std::string> expandMacro(std::string Atom) {
    if (Atom == "compile") {
      return split("save ../tools/pass-generator/src/gen.cpp.inc | exec ninja -C ../tools/pass-generator/build");
    }
    if (Atom == "optimize") {
      return split("exec _ opt -load-pass-plugin=../tools/pass-generator/build/src/SouperCombine.dylib -passes='souper-combine,adce,instsimplify' -S");
    }
    return {};
  }

  std::vector<std::string> expand(std::vector<std::string> Cmds) {
    std::vector<std::string> Result;
    for (auto Cmd : Cmds) {
      auto Expanded = expandMacro(Cmd);
      if (Expanded.empty()) {
        Result.push_back(Cmd);
      } else {
        for (auto Atom : Expanded) {
          Result.push_back(Atom);
        }
      }
    }

    return Result;
  }

  enum class Mode {
    clang,  // clang mode, behavior TBD
    command, // execute commands
    text,   // keep storing text line by line, until a command is issued
  };
  std::string getModeName(Mode M) {
    switch (M) {
      case Mode::clang:
        return "cling";
      case Mode::command:
        return "shell";
      case Mode::text:
        return "text";
    }
  }
  bool operator()() {
    std::string Line;
    Mode CurrentMode = Mode::command;

    do {
      llvm::outs() << "souper-repl [" + getModeName(CurrentMode) + "]> ";
      if (!std::getline(std::cin, Line)) break;
      if (Line == "") continue;

      if (Line[0] == ':') {
        if (Line == ":mode clang" || Line == ":c") {
          CurrentMode = Mode::clang;
          continue;
        }
        if (Line == ":mode text" || Line == ":t") {
          CurrentMode = Mode::text;
          continue;
        }
        if (Line == ":mode shell" || Line == ":s") {
          CurrentMode = Mode::command;
          continue;
        }

        // TODO : Treat the rest of the line as a command

        llvm::errs() << "Unknown mode.\n";
        continue;
      }

      if (CurrentMode == Mode::text) {
        auto Cur = Tab.get("_");
        if (Cur.has_value()) {
          if (Cur.value().Attributes[SymbolTable::StoredObject::Attr::Type] == "string") {
            Cur.value().Data[0] += Line + '\n';
            Tab.put("_", SymbolTable::StoredObject(Cur.value().Data[0], "string"));
            continue;
          } else {
            llvm::errs() << "Warning: _ is not a string, overwriting\n";
            Tab.put("_", SymbolTable::StoredObject(Line + "\n", "string"));
          }
        } else {
          Tab.put("_", SymbolTable::StoredObject(Line + "\n", "string"));
        }
        continue;
      }

      if (CurrentMode == Mode::command) {
        auto Cmds = split(Line);

        if (Cmds.empty()) continue;
        if (Cmds[0] == "exit" || Cmds[0] == "quit" || Cmds[0] == "q") break;

        auto Split = SplitCommands(expand(Cmds));
        size_t cmd_index = 0;

        for (auto SubCmds : Split) {

          if (!dispatch(SubCmds.first)) {
            if (auto Obj = Tab.get(SubCmds.first[0])) {
              Cmds.push_back(SubCmds.first[0]);
              Cmds[0] = "p";
              dispatch(Cmds);
            } else {
              llvm::errs() << "Error while trying to execute " << SubCmds.first[0] << '\n';
              break;
            }
          }

          if (SubCmds.second != "") {
            Tab.put(SubCmds.second, Tab.get("_").value());
          }

          if (cmd_index++ != Split.size() - 1) {
            llvm::outs() << "----------------------------\n";
          }
        }
      }

      if (CurrentMode == Mode::clang) {
        auto &&PTU = Interp->Parse(Line);
        if (!PTU) {
          llvm::errs() << "Failed to parse\n";
          continue;
        } else {
          if (DebugLevel > 2) {
            PTU->TheModule->print(llvm::outs(), nullptr);
          }
          Tab.put("_", SymbolTable::StoredObject(std::move(PTU->TheModule)));
        }
      }
    } while(std::cin.good());
    return true;
  }
};

// int test_repl() {
//   using namespace clang;

//   llvm::llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

//   // Allow low-level execution.
//   llvm::InitializeNativeTarget();
//   llvm::InitializeNativeTargetAsmPrinter();
//   // Initialize our builder class.
//   clang::IncrementalCompilerBuilder CB;
//   CB.SetCompilerArgs({"-std=c++20"});

//   // Create the incremental compiler instance.
//   std::unique_ptr<clang::CompilerInstance> CI;
//   CI = ExitOnErr(CB.CreateCpp());

//   // Create the interpreter instance.
//   std::unique_ptr<Interpreter> Interp
//       = ExitOnErr(Interpreter::create(std::move(CI)));

//   auto &&PTU = Interp->Parse(R"(
//     extern "C" int printf(const char*,...);
//     printf("Hello Interpreter World!\n");
//   )");

//   if (!PTU) {
//     llvm::errs() << "Failed to parse\n";
//     return 1;
//   }

//   PTU->TheModule->print(llvm::outs(), nullptr);
//   return 0;

  // // Parse and execute simple code.
  // ExitOnErr(Interp->ParseAndExecute(R"(extern "C" int printf(const char*,...);
  //                                      printf("Hello Interpreter World!\n");
  //                                     )"));

  // // Create a value to store the transport the execution result from the JIT.
  // clang::Value V;
  // ExitOnErr(Interp->ParseAndExecute(R"(extern "C" int square(int x){return x*x;}
  //                                      square(12)
  //                                     )", &V));
  // printf("From JIT: square(12)=%d\n", V.getInt());

  // // Or just get the function pointer and call it from compiled code:
  // auto SymAddr = ExitOnErr(Interp->getSymbolAddress("square"));
  // auto squarePtr = SymAddr.toPtr<int(*)(int)>();
  // printf("From compiled code: square(13)=%d\n", squarePtr(13));
// }

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

  // return test_repl();

  llvm::outs() << "Got " << Inputs.size() << " inputs\n";
  REPL SouperRepl(IC, S.get(), Inputs);
  return SouperRepl();
}

