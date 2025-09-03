#ifndef SOUPER_GENERALIZE_H
#define SOUPER_GENERALIZE_H

#include "souper/Parser/Parser.h"
#include "souper/Extractor/Solver.h"
#include "souper/Infer/Interpreter.h"
#include <optional>

extern unsigned DebugLevel;

namespace souper {

  
std::optional<ParsedReplacement> GeneralizeRep(ParsedReplacement input);
void PrintInputAndResult(ParsedReplacement Input, ParsedReplacement Result);

ParsedReplacement ReduceBasic(
  ParsedReplacement Input);

ParsedReplacement ReducePoison(
  ParsedReplacement Input);

std::optional<ParsedReplacement> ShrinkRep(ParsedReplacement Input,
                                           size_t Target);

std::vector<std::vector<int>> GetCombinations(std::vector<int> Counts);

template <typename C, typename F>
bool All(const C &c, F f);

size_t InferWidth(Inst::Kind K, const std::vector<Inst *> &Ops);
std::pair<std::vector<std::pair<Inst *, llvm::APInt>>, ParsedReplacement>
AugmentForSymKBDB(ParsedReplacement Original, InstContext &IC);
bool typeCheck(Inst *I);
bool typeCheck(ParsedReplacement &R);
std::vector<Inst *> findConcreteConsts(const ParsedReplacement &Input);
std::vector<Inst *> FilterExprsByValue(const std::vector<Inst *> &Exprs,
                                       llvm::APInt TargetVal,
                                       const std::vector<std::pair<Inst *, llvm::APInt>> &CMap);

std::vector<Inst *> FilterRelationsByValue(const std::vector<Inst *> &Relations,
                                        const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
                                        std::vector<ValueCache> CEXs);

std::vector<Inst *> BitFuncs(Inst *I, InstContext &IC);
std::vector<Inst *> InferConstantLimits(const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
                                        InstContext &IC, const ParsedReplacement &Input);

std::vector<Inst *> InferPotentialRelations(
                                          const std::vector<std::pair<Inst *, llvm::APInt>> &CMap,
                                          InstContext &IC, const ParsedReplacement &Input, std::vector<ValueCache> CEXs,
                                          bool LatticeChecks);
struct Cmp;
std::set<Inst *, Cmp> findConcreteConsts(Inst *I);
std::optional<ParsedReplacement> DFPreconditionsAndVerifyGreedy(
    ParsedReplacement Input, std::map<Inst *, llvm::APInt> SymCS);
std::optional<ParsedReplacement> SimplePreconditionsAndVerifyGreedy(
    ParsedReplacement Input, std::map<Inst *, llvm::APInt> SymCS);
size_t BruteForceModelCount(Inst *Pred);
void SortPredsByModelCount(std::vector<Inst *> &Preds);
std::optional<ParsedReplacement> VerifyWithRels(
    ParsedReplacement Input, std::vector<Inst *> &Rels,
    std::map<Inst *, llvm::APInt> SymCS);
std::vector<Inst *> IOSynthesize(llvm::APInt Target,
                                 const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap,
                                 InstContext &IC, size_t Threshold, bool ConstMode,
                                 Inst *ParentConst);
// std::vector<std::vector<Inst *>> Enumerate(std::vector<Inst *> RHSConsts,
//                                            std::vector<Inst *> RHSFresh,
//                                            InstContext &IC, size_t MaxDepth,
//                                            bool AllowConst, bool AllowVar, bool AllowOp);
std::vector<Inst *> AllSubExprs(Inst *I, size_t W);
std::vector<Inst *> ExtractSketchesSimple(InstContext &IC, ParsedReplacement Input,
                                          const std::map<Inst *, Inst *> &SymConstMap,
                                          size_t Width);
std::optional<llvm::APInt> Fold(Inst *I);
bool OpsConstP(Inst *I);

Inst *ConstantFoldingLiteImpl(InstContext &IC, Inst *I, std::set<Inst *> &Visited);
Inst *ConstantFoldingLite(InstContext &IC, Inst *I);


std::vector<std::vector<Inst *>> InferSketchExprs(std::vector<Inst *> RHS,
  ParsedReplacement Input,
  InstContext &IC,
  const std::map<Inst *, Inst *> &SymConstMap,
  const std::vector<std::pair<Inst *, llvm::APInt>> &ConstMap);

void findDangerousConstants(Inst *I, std::set<Inst *> &Results);
bool hasMultiArgumentPhi(Inst *I);
std::optional<ParsedReplacement> SuccessiveSymbolize(ParsedReplacement Input, bool &Changed,
                                                    std::vector<std::pair<Inst *, llvm::APInt>> ConstMap);
std::optional<ParsedReplacement> GeneralizeShrinked(ParsedReplacement Input);
std::optional<ParsedReplacement> ReplaceWidthVars(ParsedReplacement &Input);

Inst *CombinePCs(const std::vector<InstMapping> &PCs, InstContext &IC);
bool IsStaticallyWidthIndependent(ParsedReplacement Input);
void GetWidthChangeInsts(Inst *I, std::vector<Inst *> &WidthChanges);
bool hasConcreteDataflowConditions(ParsedReplacement &Input);
ParsedReplacement ReplaceMinusOneAndFamily(InstContext &IC, ParsedReplacement Input);

}

#endif