#define _LIBCPP_DISABLE_DEPRECATION_WARNINGS

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/KnownBits.h"

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

// Use the shared VerifyWidthIndependent from SynthUtils
#include <cstdlib>
#include <sstream>
#include <optional>

using namespace llvm;


unsigned DebugLevel;

static llvm::cl::opt<unsigned, /*ExternalStorage=*/true>
DebugFlagParser("souper-debug-level",
     llvm::cl::desc("Control the verbose level of debug output (default=1). "
     "The larger the number is, the more fine-grained debug "
     "information will be printed."),
     llvm::cl::location(DebugLevel), llvm::cl::init(1));

namespace souper {
  Solver *S;
}

using namespace souper;

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input souper optimization>"),
              cl::init("-"));

static cl::opt<bool> CountWidthAssignmentsFlag("count-width-assignments",
    cl::desc("Count the number of width assignments to check without verifying (default=false)"),
    cl::init(false));

static cl::opt<bool> WidthIndependentFlag("width-independent",
    cl::desc("Verify transformation in width-independent mode using Alive2 (default=false)"),
    cl::init(false));

static cl::opt<bool> PrintValidTypings("print-valid-typings",
    cl::desc("Print all valid width typings (default=false)"),
    cl::init(false));

static cl::opt<bool> PrintInvalidTypings("print-invalid-typings",
    cl::desc("Print all invalid width typings (default=false)"),
    cl::init(false));

static cl::opt<bool> PrintAllTypings("print-all-typings",
    cl::desc("Print both valid and invalid width typings (default=false)"),
    cl::init(false));

static cl::opt<bool> SExprOutput("sexpr",
    cl::desc("Output in S-expression format (default=false)"),
    cl::init(false));

static cl::opt<bool> SExprInput("sexpr-input",
    cl::desc("Parse input as S-expression format (default=false)"),
    cl::init(false));

int main(int argc, char **argv) {
  cl::ParseCommandLineOptions(argc, argv);
  
  // Check incompatible options
  if (SExprOutput && isNoWidthMode()) {
    llvm::errs() << "Error: --sexpr and --no-width cannot be used together\n";
    return 1;
  }
  
  KVStore *KV = 0;

  std::unique_ptr<Solver> S_ = 0;
  if (!CountWidthAssignmentsFlag) {
    S_ = GetSolver(KV);
  }
  S = S_.get();

  auto MB = MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (!MB) {
    llvm::errs() << MB.getError().message() << '\n';
    return 1;
  }

  InstContext IC;
  std::string ErrStr;

  auto &&Data = (*MB)->getMemBufferRef();
  
  std::vector<ParsedReplacement> Inputs;
  
  if (SExprInput) {
    // Parse as S-expression
    auto Result = ParseSExpr(IC, Data.getBuffer().str(), ErrStr);
    if (!Result) {
      llvm::errs() << "S-expression parse error: " << ErrStr << '\n';
      return 1;
    }
    Inputs.push_back(*Result);
  } else {
    // Parse as standard Souper format
    Inputs = ParseReplacements(IC, Data.getBufferIdentifier(),
                                    Data.getBuffer(), ErrStr);
  }

  if (!ErrStr.empty()) {
    llvm::errs() << ErrStr << '\n';
    return 1;
  }

  if (Inputs.empty()) {
    llvm::errs() << "No valid inputs found\n";
    return 1;
  }

  int ReturnCode = 0;
  size_t ProcessedCount = 0;
  
  for (auto &&Input : Inputs) {
    // Validate input
    if (!Input.Mapping.LHS) {
      if (DebugLevel > 0) {
        llvm::errs() << "; Skipping input " << ProcessedCount << ": no LHS\n";
      }
      ProcessedCount++;
      continue;
    }
    
    if (CountWidthAssignmentsFlag) {
      // Just count without verification
      size_t count = souper::CountWidthAssignments(Input);
      
      if (count == 0) {
        llvm::outs() << "0\n";
      } else if (count == 1) {
        llvm::outs() << "width-independent\n";
      } else {
        llvm::outs() << count << "\n";
      }
    } else if (WidthIndependentFlag) {
      // Verify using width-independent mode with detailed results
      if (!Input.Mapping.RHS) {
        llvm::errs() << "; Error: No RHS for width-independent verification\n";
        ReturnCode = 1;
        ProcessedCount++;
        continue;
      }
      
      auto Result = VerifyWidthIndependentWithDetails(Input);
      
      llvm::outs() << "; ";
      Result.printSummary(llvm::outs());
      
      if (Result.IsValid) {
        Input.print(llvm::outs(), true);
      } else if (Result.CouldNotDetermine) {
        llvm::outs() << "; Input:\n";
        Input.print(llvm::outs(), true);
      }
      
      // Print typings based on flags
      if (PrintAllTypings || PrintValidTypings) {
        Result.printValidTypings(llvm::outs());
      }
      if (PrintAllTypings || PrintInvalidTypings) {
        Result.printInvalidTypings(llvm::outs());
      }
    } else {
      // Use GeneralizeRepWithTypings to get typing information
      auto GR = GeneralizeRepWithTypings(Input);
      
      if (GR.Result) {
        if (SExprOutput) {
          SExprPrinter SP(GR.Result.value());
          SP(llvm::outs());
        } else {
          PrintInputAndResult(Input, GR.Result.value());
          
          // Print width summary
          llvm::outs() << "; ";
          GR.printWidthSummary(llvm::outs());
        }
        
        // Print typings based on flags
        if (PrintAllTypings || PrintValidTypings) {
          GR.printValidTypings(llvm::outs());
        }
        if (PrintAllTypings || PrintInvalidTypings) {
          GR.printInvalidTypings(llvm::outs());
        }
      } else {
        if (DebugLevel > 0) {
          llvm::errs() << "; Generalization failed for input " << ProcessedCount << "\n";
        }
      }
    }
    ProcessedCount++;
  }
  
  if (DebugLevel > 0 && ProcessedCount > 1) {
    llvm::errs() << "; Processed " << ProcessedCount << " inputs\n";
  }
  
  return ReturnCode;
}
