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

#include "souper/Infer/EnumerativeSynthesis.h"
#include "souper/Infer/Interpreter.h"
#include "souper/Infer/AbstractInterpreter.h"
#include "souper/Parser/Parser.h"
#include "souper/Tool/GetSolver.h"
#include "souper/Util/LLVMUtils.h"

using namespace llvm;
using namespace souper;

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

static cl::opt<size_t> InputValue("input-value",
    cl::desc("Input value (default=0)"),
    cl::init(0));
// TODO Replace with comma separated list

using namespace souper;

struct KBHistogram {

void add(KnownBits KB) {
  auto Width = KB.Zero.getBitWidth();
  if (Zero.size() < Width) {
    for (int i = Zero.size(); i < Width; ++i) {
      Zero.push_back(0);
      One.push_back(0);
    }
  }

  for(int i = 0; i < Width; ++i) {
    if (KB.Zero[i]) {
      Zero[i]++;
    }
    if (KB.One[i]) {
      One[i]++;
    }
  }
}

template<typename Stream>
void print(Stream& Out) {
  Out << '[';
  for (int i = 0; i < Zero.size(); ++i) {
    Out << Zero[i] << ' ' << One[i] << ",";
  }
  Out << "\b]";
}

// size_t Width;
std::vector<int> Zero;
std::vector<int> One;
// keeping it int because ? might be considered negative at some point

};

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);

  souper::InstContext IC;

  std::set<Inst* > Inputs;
  // inputs assumed to be 32 bits for now.
  // Do input widths even matter? I think not. TODO verify.
  // Does input counts matter? I think so. TODO verify.
  for (int i = 0; i < NumInputs; ++i) {
    Inputs.insert(IC.createVar(32, "var_" + std::to_string(i)));
  }

  EnumerativeSynthesis ES;

  auto Guesses = ES.generateGuesses(Inputs, OutputWidth, IC);

  ValueCache VC;
  for (auto I : Inputs) {
    VC[I] = EvalValue(llvm::APInt(I->Width, InputValue));
  }

  ConcreteInterpreter CI(VC);
  KnownBitsAnalysis KBA;

  int unknowns = 0;

  // KBHistogram KBH;

  std::unordered_map<Inst::Kind, KBHistogram> Map;

  for (auto I : Guesses) {
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

  // llvm::outs() << "Number of guesses:\t" << Guesses.size() << "\n";
  // llvm::outs() << "unknowns:\t" << unknowns << "\n";
  // KBH.print(llvm::outs());

  for (auto &&Pair : Map) {
    llvm::outs() << Inst::getKindName(Pair.first) << "\t";
    Pair.second.print(llvm::outs());
    llvm::outs() << "\n";
  }


  return 0;
}
