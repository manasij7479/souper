#include "llvm/ADT/APInt.h"

#include "souper/Infer/Interpreter.h"
#include "souper/Inst/Inst.h"
#include "souper/Extractor/Solver.h"

#include <unordered_map>

namespace souper {

typedef std::function<bool(Inst *, std::vector<Inst *> &)> PruneFunc;

class PruningManager {
public:
  PruningManager(SynthesisContext &SC_, std::vector< souper::Inst* >& Inputs_,
                 unsigned int StatsLevel_);
  PruneFunc getPruneFunc() {return DataflowPrune;}
  void printStats(llvm::raw_ostream &out) {
    out << "Dataflow Pruned " << NumPruned << "/" << TotalGuesses << "\n";
  }

  bool isInfeasible(Inst *RHS, unsigned StatsLevel);
  bool isInfeasibleWithSolver(Inst *RHS, unsigned StatsLevel);

  void init();
  // double init antipattern, required because init should
  // not be called when pruning is disabled
private:
  SynthesisContext &SC;
  std::vector<EvalValue> LHSValues;
  PruneFunc DataflowPrune;
  unsigned NumPruned;
  unsigned TotalGuesses;
  int StatsLevel;
  std::vector<ValueCache> InputVals;
  std::vector<Inst *> &InputVars;
  std::vector<ValueCache> generateInputSets(std::vector<Inst *> &Inputs);
  std::vector<ValueCache> generateInputSetsWithSolver(std::vector<Inst *> &Inputs);
};

}
