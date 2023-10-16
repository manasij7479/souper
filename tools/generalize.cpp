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
#include <cstdlib>
#include <sstream>
#include <optional>


unsigned DebugLevel;

static llvm::cl::opt<unsigned, /*ExternalStorage=*/true>
DebugFlagParser("souper-debug-level",
     llvm::cl::desc("Control the verbose level of debug output (default=1). "
     "The larger the number is, the more fine-grained debug "
     "information will be printed."),
     llvm::cl::location(DebugLevel), llvm::cl::init(1));

using namespace llvm;
using namespace souper;

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input souper optimization>"),
              cl::init("-"));

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
    llvm::errs() << ErrStr << '\n';
    return 1;
  }

  // TODO: Write default action which chooses what to do based on input structure

  for (auto &&Input: Inputs) {
    if (auto Result = GeneralizeRep(Input, IC, S.get())) {
      PrintInputAndResult(Input, Result.value());
    }
  }
  return 0;
}
