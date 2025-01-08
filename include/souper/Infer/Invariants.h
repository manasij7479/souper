#ifndef SOUPER_INFER_INVARIANTS_H
#define SOUPER_INFER_INVARIANTS_H

#include "souper/Parser/Parser.h"

namespace souper {
  class Solver;
  std::vector<ParsedReplacement> InferInvariants(InstContext &IC, ParsedReplacement Inputs, Solver *S);
}

#endif