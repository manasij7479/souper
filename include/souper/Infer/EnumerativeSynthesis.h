// Copyright 2018 The Souper Authors. All rights reserved.
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

#ifndef SOUPER_ENUMERATIVE_SYNTHESIS_H
#define SOUPER_ENUMERATIVE_SYNTHESIS_H

#include "llvm/ADT/APInt.h"
#include "llvm/Support/KnownBits.h"
#include "souper/Extractor/Solver.h"
#include "souper/Inst/Inst.h"

#include <utility>
#include <system_error>
#include <vector>

extern bool UseAlive;
extern unsigned DebugLevel;

namespace souper {

class EnumerativeSynthesis {
public:
  // Synthesize an instruction from the specification in LHS
  std::error_code synthesize(SMTLIBSolver *SMTSolver,
                             const BlockPCs &BPCs,
                             const std::vector<InstMapping> &PCs,
                             Inst *TargetLHS, std::vector<Inst *> &RHSs,
                             bool CheckAllGuesses,
                             InstContext &IC, unsigned Timeout);

std::vector<Inst *> generateGuesses(const std::set<Inst *> &Inputs,
                int Width, InstContext &IC);

};

template<typename T = int>
struct KBHistogram {
KBHistogram() {
  Counter = 0;
}
void add(llvm::KnownBits KB) {
  Counter++;
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
std::vector<T> Zero;
std::vector<T> One;
// keeping it int because ? might be considered negative at some point
size_t Counter;
};

struct KBHistogramCollection {
  KBHistogramCollection(std::string File);
  std::vector<std::unordered_map<Inst::Kind, KBHistogram<float>>> Data;
  std::vector<llvm::APInt> InputVals;
};

}


#endif  // SOUPER_ENUMERATIVE_SYNTHESIS_H
