#ifndef SOUPER_GENERALIZE_H
#define SOUPER_GENERALIZE_H

#include "souper/Parser/Parser.h"
#include "souper/Extractor/Solver.h"
#include <optional>

extern unsigned DebugLevel;

namespace souper {
std::optional<ParsedReplacement> GeneralizeRep(ParsedReplacement &input,
                                            InstContext &IC,
                                            Solver *S);
void PrintInputAndResult(ParsedReplacement Input, ParsedReplacement Result);

ParsedReplacement ReduceBasic(
  InstContext &IC,
  Solver *S,
  ParsedReplacement Input);

ParsedReplacement ReducePoison(
  InstContext &IC,
  Solver *S,
  ParsedReplacement Input);

std::optional<ParsedReplacement> ShrinkRep(ParsedReplacement &Input,
                                            InstContext &IC,
                                            Solver *S);

}

#endif