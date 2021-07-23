// Copyright 2014 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "llvm/Support/KnownBits.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Format.h"

#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/Interpreter.h"
#include "souper/Infer/AbstractInterpreter.h"
#include "souper/Parser/Parser.h"
#include "souper/Tool/GetSolver.h"
#include "souper/Util/LLVMUtils.h"

using namespace llvm;
using namespace souper;

#include <stdio.h>

unsigned DebugLevel;

static cl::opt<unsigned, /*ExternalStorage=*/true>
DebugFlagParser("souper-debug-level",
     cl::desc("Control the verbose level of debug output (default=1). "
     "The larger the number is, the more fine-grained debug "
     "information will be printed."),
     cl::location(DebugLevel), cl::init(1));

// static cl::list<std::string>
// InputValueStrings("input-values", cl::desc("<input values>"),
//                   cl::CommaSeparated);

static cl::opt<size_t> NumInputs("bias-num-inputs",
    cl::desc("Number of inputs (default=1)"),
    cl::init(1));


static cl::opt<size_t> OutputWidth("output-width",
    cl::desc("Number of output bits (default=32)"),
    cl::init(32));

static cl::list<size_t> InputValues
    ("input-values", cl::desc("<input values>"),
    cl::CommaSeparated);
using namespace souper;

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  souper::InstContext IC;

  std::set<Inst* > InputVars;
  // inputs assumed to be 32 bits for now.
  // Do input widths even matter? I think not. TODO verify.
  // Does input counts matter? I think so. TODO verify.
  for (int i = 0; i < NumInputs; ++i) {
    InputVars.insert(IC.createVar(32, "var_" + std::to_string(i)));
  }

  EnumerativeSynthesis ES;

  auto Guesses = ES.generateGuesses(InputVars, OutputWidth, IC);

  llvm::outs() << OutputWidth << '\n';
  for (auto InputValue : InputValues) {
    ValueCache VC;
    for (auto I : InputVars) {
      VC[I] = EvalValue(llvm::APInt(I->Width, InputValue));
    }

    ConcreteInterpreter CI(VC);
    KnownBitsAnalysis KBA;

    int unknowns = 0;

    std::unordered_map<Inst::Kind, KBHistogram<int>> Map;

    int count = 0;
    int first_run = true;

    for (auto I : Guesses) {
      std::set<Inst *> SymConsts;
      getConstants(I, SymConsts);
      if (!SymConsts.empty()) {
        count++;
        std::map<Inst *, llvm::APInt> ConstMap;
        for (auto C : SymConsts) {
          ConstMap[C] = llvm::APInt(C->Width, 0);
        }
        std::map<Inst *, Inst *> INC;
        std::map<Block *, Block *> BLC;

  //      ReplacementContext RC;
  //      RC.printInst(I, llvm::outs(), true);

        I = getInstCopy(I, IC, INC, BLC, &ConstMap, false, false);
        // TODO Find a better solution for these.
        // current idea of analyzing known bits doesn't work that well

  //      ReplacementContext RC2;
  //      RC2.printInst(I, llvm::outs(), true);
  //      llvm::outs() << "\n...........\n";
      }


  //    std::unordered_map<Inst *, KnownBits> KBAssumptions;
  //    for (auto C : SymConsts) {
  //      KnownBits KB(C->Width);
  //      KB.One = llvm::APInt(C->Width, 0);
  //      KB.Zero = ~KB.One;
  //      KBAssumptions[C] = KB;
  //    }



      // ReplacementContext RC;
      // RC.printInst(I, llvm::outs(), true);
      // llvm::outs() << "\n";
      auto KB = KBA.findKnownBits(I, CI, true);
      if (KB.isUnknown()) {
        unknowns++;
      }
      // KBH.add(KB);
      Map[I->K].add(KB);
      // llvm::outs() << KnownBitsAnalysis::knownBitsString(KB);
      // llvm::outs() << "\n";
    }


    // KBH.print(llvm::outs());

  //  for (auto &&Pair : Map) {
  //    llvm::outs() << Inst::getKindName(Pair.first) << "\t";
  //    Pair.second.print(llvm::outs());
  //    llvm::outs() << "\n";
  //  }

    if (first_run) {
      first_run = false;
      llvm::outs() << Map.size() << "\n";
    }

    llvm::outs() << InputValue << '\n';
    for (auto &&Pair : Map) {
      llvm::outs() << Inst::getKindName(Pair.first) << "\n";

  //    for (int i = 0; i < Pair.second.Zero.size(); ++i) {
  //      printf("%.1f ", Pair.second.Zero[i]*1.0/Pair.second.Counter);
  //    }
  //    llvm::outs() << "\n";
  //    for (int i = 0; i < Pair.second.One.size(); ++i) {
  //      printf("%.1f ", Pair.second.One[i]*1.0/Pair.second.Counter);
  //    }

      for (int i = 0; i < Pair.second.Zero.size(); ++i) {
  //      printf("%d ", Pair.second.Zero[i]);
        llvm::outs() << llvm::format("%0.3f " , Pair.second.Zero[i]*1.0/Pair.second.Counter) << ' ';
      }
      llvm::outs() << "\n";
      for (int i = 0; i < Pair.second.One.size(); ++i) {
  //      printf("%d ", Pair.second.One[i]);
       llvm::outs() << llvm::format("%0.3f " , Pair.second.One[i]*1.0/Pair.second.Counter) << ' ';
      }

      llvm::outs() << "\n";
    }
    llvm::outs() << "\n";
  }
  return 0;
}
