#include "souper/Infer/Invariants.h"
#include "souper/Extractor/Solver.h"
#include "souper/Infer/SynthUtils.h"

namespace souper {



// Enforce commutativity to prune search space
bool C3(Inst *A, Inst *B, Inst *C) {
  return A > B && B > C;
}
bool C2(Inst *A, Inst *B) {
  return A > B;
}

std::vector<Inst *> GenerateInvariantCandidates(InstContext &IC, ParsedReplacement Input) {
  std::vector<Inst *> Guesses;

  std::vector<Inst *> SubExpressions;
  std::unordered_set<Inst *> RootSet;
  auto NotAConst = [](Inst *I) {return I->K != Inst::Const;};
  findInsts(Input.Mapping.LHS, SubExpressions, NotAConst);
  RootSet.insert(Input.Mapping.LHS);
  for (auto &&P : Input.PCs) {
    findInsts(P.LHS, SubExpressions, NotAConst);
    RootSet.insert(P.LHS);
    findInsts(P.RHS, SubExpressions, NotAConst);
    RootSet.insert(P.RHS);
  }

#define BIN(X, Y, OP)                       \
  {                                         \
    auto I = Builder(X, IC).OP(Y)();        \
    if (RootSet.find(I) == RootSet.end()) { \
      RootSet.insert(I);                    \
      Guesses.push_back(I);                 \
    }                                       \
  }
#define COMMUTATIVE_BIN(X, Y, OP) \
  {                               \
    if (C2(X, Y)) BIN(X, Y, OP);  \
  }

  for (auto X : SubExpressions) {
    for (auto Y : SubExpressions) {
      if (X == Y) {
        continue;
      }
      if (X == Input.Mapping.LHS || Y == Input.Mapping.LHS) {
        continue;
      }
      if (X->Width != Y->Width) {
        continue; // todo handle this
      }

      COMMUTATIVE_BIN(X, Y, Eq);
      COMMUTATIVE_BIN(X, Y, Ne);
      BIN(X, Y, Ult);
      BIN(X, Y, Ule);
      BIN(X, Y, Slt);
      BIN(X, Y, Sle);

      // Todo others
    }
  }

#undef BIN
#undef COMMUTATIVE_BIN

  return Guesses;
}

std::vector<ParsedReplacement> InferInvariants(InstContext &IC, ParsedReplacement Input, Solver *S) {
  std::vector<ParsedReplacement> Results;

  std::vector<Inst *> Guesses = GenerateInvariantCandidates(IC, Input);

  for (Inst *Guess : Guesses) {
    ParsedReplacement Inv = Input;
    Inv.Mapping.RHS = Guess;
    if (VerifyInvariant(Inv, IC, S)) {
      Results.push_back(Inv);
    }
  }

  return Results;
}
}