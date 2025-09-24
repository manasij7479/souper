// Minimal implementation of Klee solver command line support
// Provides necessary symbols without full solver infrastructure

#include "klee/Support/OptionCategories.h"
#include "klee/Solver/SolverCmdLine.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

namespace klee {

// Provide the SolvingCat category
cl::OptionCategory SolvingCat("Constraint solving options", "These options control the constraint solver.");

// Provide minimal implementations of required command line options
cl::opt<bool> UseFastCexSolver("use-fast-cex-solver", cl::init(false), cl::cat(SolvingCat));
cl::opt<bool> UseCexCache("use-cex-cache", cl::init(true), cl::cat(SolvingCat));
cl::opt<bool> UseBranchCache("use-branch-cache", cl::init(true), cl::cat(SolvingCat));
cl::opt<bool> UseIndependentSolver("use-independent-solver", cl::init(true), cl::cat(SolvingCat));
cl::opt<bool> DebugValidateSolver("debug-validate-solver", cl::init(false), cl::cat(SolvingCat));
cl::opt<std::string> MinQueryTimeToLog("min-query-time-to-log", cl::init("0s"), cl::cat(SolvingCat));
cl::opt<bool> LogTimedOutQueries("log-timed-out-queries", cl::init(false), cl::cat(SolvingCat));
cl::opt<std::string> MaxCoreSolverTime("max-solver-time", cl::init("0s"), cl::cat(SolvingCat));
cl::opt<bool> UseForkedCoreSolver("use-forked-solver", cl::init(true), cl::cat(SolvingCat));
cl::opt<bool> CoreSolverOptimizeDivides("solver-optimize-divides", cl::init(true), cl::cat(SolvingCat));
cl::opt<bool> UseAssignmentValidatingSolver("use-assignment-validating-solver", cl::init(false), cl::cat(SolvingCat));

cl::bits<QueryLoggingSolverType> QueryLoggingOptions("use-query-log", cl::cat(SolvingCat));

// Main solver selection option - default to Z3 since that's what Souper uses
cl::opt<CoreSolverType> CoreSolverToUse("solver-backend", 
    cl::desc("Specify the core solver backend to use"),
    cl::values(clEnumValN(Z3_SOLVER, "z3", "Z3 (default)"),
               clEnumValN(DUMMY_SOLVER, "dummy", "Dummy solver")),
    cl::init(Z3_SOLVER), cl::cat(SolvingCat));

cl::opt<CoreSolverType> DebugCrossCheckCoreSolverWith("debug-crosscheck-core-solver", 
    cl::init(NO_SOLVER), cl::cat(SolvingCat));

} // namespace klee