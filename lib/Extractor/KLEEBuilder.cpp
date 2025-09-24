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

#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Expr/ExprSMTLIBPrinter.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/ArrayCache.h"
#include "souper/Extractor/ExprBuilder.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/CommandLine.h"

using namespace klee;
using namespace souper;

namespace {

static llvm::cl::opt<bool> DumpKLEEExprs(
    "dump-klee-exprs",
    llvm::cl::desc("Dump KLEE expressions after SMTLIB queries"),
    llvm::cl::init(false));

    
    // This vector contains 256 std::function objects, each representing
    // a unique 3-input logical operation as defined by the PTX lop3 instruction,
    // but adapted for KLEE's symbolic execution engine.
    // The index of the vector corresponds to the immLut value (0-255).
    const std::vector<std::function<klee::ref<klee::Expr>(klee::ref<klee::Expr>, klee::ref<klee::Expr>, klee::ref<klee::Expr>)>> LUT = {
        // n = 0 (0x00)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::ConstantExpr::create(0, a->getWidth());
        },
    
        // n = 1 (0x01)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)));
        },
    
        // n = 2 (0x02)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c));
        },
    
        // n = 3 (0x03)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 4 (0x04)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c)));
        },
    
        // n = 5 (0x05)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 6 (0x06)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 7 (0x07)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 8 (0x08)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c));
        },
    
        // n = 9 (0x09)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)));
        },
    
        // n = 10 (0x0A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)));
        },
    
        // n = 11 (0x0B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c))));
        },
    
        // n = 12 (0x0C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)));
        },
    
        // n = 13 (0x0D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c))));
        },
    
        // n = 14 (0x0E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c))));
        },
    
        // n = 15 (0x0F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)))));
        },
    
        // n = 16 (0x10)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)));
        },
    
        // n = 17 (0x11)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))));
        },
    
        // n = 18 (0x12)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))));
        },
    
        // n = 19 (0x13)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 20 (0x14)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))));
        },
    
        // n = 21 (0x15)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 22 (0x16)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 23 (0x17)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))))));
        },
    
        // n = 24 (0x18)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))));
        },
    
        // n = 25 (0x19)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 26 (0x1A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 27 (0x1B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))))));
        },
    
        // n = 28 (0x1C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))));
        },
    
        // n = 29 (0x1D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))))));
        },
    
        // n = 30 (0x1E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))))));
        },
    
        // n = 31 (0x1F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c)))))));
        },
    
        // n = 32 (0x20)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c));
        },
    
        // n = 33 (0x21)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 34 (0x22)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 35 (0x23)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 36 (0x24)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 37 (0x25)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 38 (0x26)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 39 (0x27)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 40 (0x28)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 41 (0x29)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 42 (0x2A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 43 (0x2B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 44 (0x2C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 45 (0x2D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 46 (0x2E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 47 (0x2F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))))));
        },
    
        // n = 48 (0x30)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)));
        },
    
        // n = 49 (0x31)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 50 (0x32)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 51 (0x33)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 52 (0x34)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 53 (0x35)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 54 (0x36)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 55 (0x37)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))))));
        },
    
        // n = 56 (0x38)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))));
        },
    
        // n = 57 (0x39)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 58 (0x3A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 59 (0x3B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))))));
        },
    
        // n = 60 (0x3C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))));
        },
    
        // n = 61 (0x3D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))))));
        },
    
        // n = 62 (0x3E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c))))));
        },
    
        // n = 63 (0x3F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)))))));
        },
    
        // n = 64 (0x40)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)));
        },
    
        // n = 65 (0x41)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 66 (0x42)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 67 (0x43)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 68 (0x44)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 69 (0x45)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 70 (0x46)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 71 (0x47)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 72 (0x48)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 73 (0x49)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 74 (0x4A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 75 (0x4B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 76 (0x4C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 77 (0x4D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 78 (0x4E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 79 (0x4F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 80 (0x50)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 81 (0x51)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 82 (0x52)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 83 (0x53)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 84 (0x54)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 85 (0x55)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 86 (0x56)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 87 (0x57)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 88 (0x58)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 89 (0x59)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 90 (0x5A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 91 (0x5B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 92 (0x5C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 93 (0x5D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 94 (0x5E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 95 (0x5F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 96 (0x60)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))));
        },
    
        // n = 97 (0x61)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 98 (0x62)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 99 (0x63)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 100 (0x64)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 101 (0x65)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 102 (0x66)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 103 (0x67)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 104 (0x68)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 105 (0x69)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 106 (0x6A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 107 (0x6B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 108 (0x6C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 109 (0x6D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 110 (0x6E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 111 (0x6F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 112 (0x70)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))));
        },
    
        // n = 113 (0x71)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 114 (0x72)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 115 (0x73)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 116 (0x74)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 117 (0x75)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 118 (0x76)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 119 (0x77)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 120 (0x78)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))));
        },
    
        // n = 121 (0x79)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 122 (0x7A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 123 (0x7B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 124 (0x7C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))));
        },
    
        // n = 125 (0x7D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 126 (0x7E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))))))));
        },
    
        // n = 127 (0x7F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c)))))))));
        },
    
        // n = 128 (0x80)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::AndExpr::create(a, klee::AndExpr::create(b, c));
        },
    
        // n = 129 (0x81)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 130 (0x82)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 131 (0x83)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 132 (0x84)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 133 (0x85)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 134 (0x86)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 135 (0x87)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 136 (0x88)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 137 (0x89)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 138 (0x8A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 139 (0x8B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 140 (0x8C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 141 (0x8D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 142 (0x8E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 143 (0x8F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 144 (0x90)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 145 (0x91)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 146 (0x92)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 147 (0x93)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 148 (0x94)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 149 (0x95)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 150 (0x96)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 151 (0x97)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 152 (0x98)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 153 (0x99)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 154 (0x9A)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 155 (0x9B)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 156 (0x9C)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 157 (0x9D)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 158 (0x9E)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 159 (0x9F)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 160 (0xA0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 161 (0xA1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 162 (0xA2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 163 (0xA3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 164 (0xA4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 165 (0xA5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 166 (0xA6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 167 (0xA7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 168 (0xA8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 169 (0xA9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 170 (0xAA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 171 (0xAB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 172 (0xAC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 173 (0xAD)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 174 (0xAE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 175 (0xAF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 176 (0xB0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 177 (0xB1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 178 (0xB2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 179 (0xB3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 180 (0xB4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 181 (0xB5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 182 (0xB6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 183 (0xB7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 184 (0xB8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 185 (0xB9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 186 (0xBA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 187 (0xBB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 188 (0xBC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 189 (0xBD)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 190 (0xBE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 191 (0xBF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 192 (0xC0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)));
        },
    
        // n = 193 (0xC1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 194 (0xC2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 195 (0xC3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 196 (0xC4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 197 (0xC5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 198 (0xC6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 199 (0xC7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 200 (0xC8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 201 (0xC9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 202 (0xCA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 203 (0xCB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 204 (0xCC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 205 (0xCD)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 206 (0xCE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 207 (0xCF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 208 (0xD0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 209 (0xD1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 210 (0xD2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 211 (0xD3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 212 (0xD4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 213 (0xD5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 214 (0xD6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 215 (0xD7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 216 (0xD8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 217 (0xD9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 218 (0xDA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 219 (0xDB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 220 (0xDC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 221 (0xDD)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 222 (0xDE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 223 (0xDF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 224 (0xE0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))));
        },
    
        // n = 225 (0xE1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 226 (0xE2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 227 (0xE3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 228 (0xE4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 229 (0xE5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 230 (0xE6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 231 (0xE7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 232 (0xE8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 233 (0xE9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 234 (0xEA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 235 (0xEB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 236 (0xEC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 237 (0xED)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 238 (0xEE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 239 (0xEF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 240 (0xF0)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))));
        },
    
        // n = 241 (0xF1)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 242 (0xF2)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 243 (0xF3)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 244 (0xF4)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 245 (0xF5)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 246 (0xF6)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 247 (0xF7)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 248 (0xF8)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))));
        },
    
        // n = 249 (0xF9)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 250 (0xFA)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 251 (0xFB)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 252 (0xFC)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))));
        },
    
        // n = 253 (0xFD)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 254 (0xFE)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c))))))));
        },
    
        // n = 255 (0xFF)
        [](klee::ref<klee::Expr> a, klee::ref<klee::Expr> b, klee::ref<klee::Expr> c) {
            return klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(klee::NotExpr::create(a), klee::AndExpr::create(b, c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), klee::NotExpr::create(c))), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(klee::NotExpr::create(b), c)), klee::OrExpr::create(klee::AndExpr::create(a, klee::AndExpr::create(b, klee::NotExpr::create(c))), klee::AndExpr::create(a, klee::AndExpr::create(b, c)))))))));
        }
    };

class KLEEBuilder : public ExprBuilder {
  UniqueNameSet ArrayNames;
  ArrayCache Cache;
  std::vector<const Array *> Arrays;
  std::map<Inst *, ref<Expr>> ExprMap;
  std::vector<Inst *> Vars;

public:
  KLEEBuilder(InstContext &IC) : ExprBuilder(IC) {}

  std::string GetExprStr(const BlockPCs &BPCs,
                         const std::vector<InstMapping> &PCs,
                         InstMapping Mapping,
                         std::vector<Inst *> *ModelVars, bool Negate, bool DropUB) override {
    Inst *Cand = GetCandidateExprForReplacement(BPCs, PCs, Mapping, /*Precondition=*/0, Negate, DropUB);
    if (!Cand)
      return std::string();
    prepopulateExprMap(Cand);
    ref<Expr> E = get(Cand);

    std::string SStr;
    llvm::raw_string_ostream SS(SStr);
    std::unique_ptr<ExprPPrinter> PP(ExprPPrinter::create(SS));
    PP->setForceNoLineBreaks(true);
    PP->scan(E);
    PP->print(E);

    return SS.str();
  }

  std::string BuildQuery(const BlockPCs &BPCs,
                         const std::vector<InstMapping> &PCs,
                         InstMapping Mapping,
                         std::vector<Inst *> *ModelVars,
                         Inst *Precondition, bool Negate, bool DropUB) override {
    std::string SMTStr;
    llvm::raw_string_ostream SMTSS(SMTStr);
    ConstraintSet constraints;
    Inst *Cand = GetCandidateExprForReplacement(BPCs, PCs, Mapping, Precondition, Negate, DropUB);
    if (!Cand)
      return std::string();
    prepopulateExprMap(Cand);
    ref<Expr> E = get(Cand);
    Query KQuery(constraints, E);
    ExprSMTLIBPrinter Printer;
    Printer.setOutput(SMTSS);
    Printer.setQuery(KQuery);
    std::vector<const klee::Array *> Arr;
    if (ModelVars) {
      for (unsigned I = 0; I != Vars.size(); ++I) {
        if (Vars[I]) {
          Arr.push_back(Arrays[I]);
          ModelVars->push_back(Vars[I]);
        }
      }
      Printer.setArrayValuesToGet(Arr);
    }
    Printer.generateOutput();

    if (DumpKLEEExprs) {
      SMTSS << "; KLEE expression:\n; ";
      std::unique_ptr<ExprPPrinter> PP(ExprPPrinter::create(SMTSS));
      PP->setForceNoLineBreaks(true);
      PP->scan(E);
      PP->print(E);
      SMTSS << '\n';
    }

    return SMTSS.str();
  }

private:
  ref<Expr> countOnes(ref<Expr> L) {
     Expr::Width Width = L->getWidth();
     ref<Expr> Count =  klee::ConstantExpr::alloc(llvm::APInt(Width, 0));
     for (unsigned i=0; i<Width; i++) {
       ref<Expr> Bit = ExtractExpr::create(L, i, Expr::Bool);
       ref<Expr> BitExt = ZExtExpr::create(Bit, Width);
       Count = AddExpr::create(Count, BitExt);
     }
     return Count;
  }

  ref<Expr> buildAssoc(
      std::function<ref<Expr>(ref<Expr>, ref<Expr>)> F,
      llvm::ArrayRef<Inst *> Ops) {
    ref<Expr> E = get(Ops[0]);
    for (Inst *I : llvm::ArrayRef<Inst *>(Ops.data()+1, Ops.size()-1)) {
      E = F(E, get(I));
    }
    return E;
  }

  ref<Expr> build(Inst *I) {
    const std::vector<Inst *> &Ops = I->orderedOps();
    switch (I->K) {
    case Inst::UntypedConst:
      assert(0 && "unexpected kind");
    case Inst::Const:
      return klee::ConstantExpr::alloc(I->Val);
    case Inst::Hole:
    case Inst::Var:
      return makeSizedArrayRead(I->Width, I->Name, I);
    case Inst::Phi: {
      const auto &PredExpr = I->B->PredVars;
      assert((PredExpr.size() || Ops.size() == 1) && "there must be block predicates");
      ref<Expr> E = get(Ops[0]);
      // e.g. P2 ? (P1 ? Op1_Expr : Op2_Expr) : Op3_Expr
      for (unsigned J = 1; J < Ops.size(); ++J) {
        E = SelectExpr::create(get(PredExpr[J-1]), E, get(Ops[J]));
      }
      return E;
    }
    case Inst::Freeze:
      return get(Ops[0]);
    case Inst::Add:
      return buildAssoc(AddExpr::create, Ops);
    case Inst::AddNSW: {
      ref<Expr> Add = AddExpr::create(get(Ops[0]), get(Ops[1]));
      return Add;
    }
    case Inst::AddNUW: {
      ref<Expr> Add = AddExpr::create(get(Ops[0]), get(Ops[1]));
      return Add;
    }
    case Inst::AddNW: {
      ref<Expr> Add = AddExpr::create(get(Ops[0]), get(Ops[1]));
      return Add;
    }
    case Inst::Sub:
      return SubExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::SubNSW: {
      ref<Expr> Sub = SubExpr::create(get(Ops[0]), get(Ops[1]));
      return Sub;
    }
    case Inst::SubNUW: {
      ref<Expr> Sub = SubExpr::create(get(Ops[0]), get(Ops[1]));
      return Sub;
    }
    case Inst::SubNW: {
      ref<Expr> Sub = SubExpr::create(get(Ops[0]), get(Ops[1]));
      return Sub;
    }
    case Inst::Mul:
      return buildAssoc(MulExpr::create, Ops);
    case Inst::MulNSW: {
      ref<Expr> Mul = MulExpr::create(get(Ops[0]), get(Ops[1]));
      return Mul;
    }
    case Inst::MulNUW: {
      ref<Expr> Mul = MulExpr::create(get(Ops[0]), get(Ops[1]));
      return Mul;
    }
    case Inst::MulNW: {
      ref<Expr> Mul = MulExpr::create(get(Ops[0]), get(Ops[1]));
      return Mul;
    }

    // We introduce these extra checks here because KLEE invokes llvm::APInt's
    // div functions, which crash upon divide-by-zero.
    case Inst::UDiv:
    case Inst::SDiv:
    case Inst::UDivExact:
    case Inst::SDivExact:
    case Inst::URem:
    case Inst::SRem: { // Fall-through
      // If the second oprand is 0, then it definitely causes UB.
      // There are quite a few cases where KLEE folds operations into zero,
      // e.g., "sext i16 0 to i32", "0 + 0", "2 - 2", etc.  In all cases,
      // we skip building the corresponding KLEE expressions and just return
      // a constant zero.
      ref<Expr> R = get(Ops[1]);
      if (R->isZero()) {
        return klee::ConstantExpr::create(0, Ops[1]->Width);
      }

      switch (I->K) {
      default:
        break;

      case Inst::UDiv: {
        ref<Expr> Udiv = UDivExpr::create(get(Ops[0]), R);
        return Udiv;
      }
      case Inst::SDiv: {
        ref<Expr> Sdiv = SDivExpr::create(get(Ops[0]), R);
        return Sdiv;
      }
      case Inst::UDivExact: {
        ref<Expr> Udiv = UDivExpr::create(get(Ops[0]), R);
        return Udiv;
      }
      case Inst::SDivExact: {
        ref<Expr> Sdiv = SDivExpr::create(get(Ops[0]), R);
        return Sdiv;
      }
      case Inst::URem: {
        ref<Expr> Urem = URemExpr::create(get(Ops[0]), R);
        return Urem;
      }
      case Inst::SRem: {
        ref<Expr> Srem = SRemExpr::create(get(Ops[0]), R);
        return Srem;
      }
      llvm_unreachable("unknown kind");
    }
    }

    case Inst::And:
      return buildAssoc(AndExpr::create, Ops);
    case Inst::Or:
      return buildAssoc(OrExpr::create, Ops);
    case Inst::Xor:
      return buildAssoc(XorExpr::create, Ops);
    case Inst::Shl: {
      ref<Expr> Result = ShlExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::ShlNSW: {
      ref<Expr> Result = ShlExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::ShlNUW: {
      ref<Expr> Result = ShlExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::ShlNW: {
      ref<Expr> Result = ShlExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::LShr: {
      ref<Expr> Result = LShrExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::LShrExact: {
      ref<Expr> Result = LShrExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::AShr: {
      ref<Expr> Result = AShrExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::AShrExact: {
      ref<Expr> Result = AShrExpr::create(get(Ops[0]), get(Ops[1]));
      return Result;
    }
    case Inst::Select:
      return SelectExpr::create(get(Ops[0]), get(Ops[1]), get(Ops[2]));
    case Inst::ZExt:
      return ZExtExpr::create(get(Ops[0]), I->Width);
    case Inst::SExt:
      return SExtExpr::create(get(Ops[0]), I->Width);
    case Inst::Trunc:
      return ExtractExpr::create(get(Ops[0]), 0, I->Width);
    case Inst::Eq:
      return EqExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::Ne:
      return NeExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::Ult:
      return UltExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::Slt:
      return SltExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::Ule:
      return UleExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::Sle:
      return SleExpr::create(get(Ops[0]), get(Ops[1]));
    case Inst::CtPop:
      return countOnes(get(Ops[0]));
    case Inst::BSwap: {
      ref<Expr> L = get(Ops[0]);
      constexpr unsigned bytelen = 8;
      ref<Expr> res = ExtractExpr::create(L, 0, bytelen);
      for (unsigned i = 1; i < L->getWidth() / bytelen; i++) {
        res = ConcatExpr::create(res, ExtractExpr::create(L, i * bytelen, bytelen));
      }

      return res;
    }
    case Inst::BitReverse: {
      ref<Expr> L = get(Ops[0]);
      auto res = ExtractExpr::create(L, 0, 1);
      for (unsigned i = 1; i < L->getWidth(); i++) {
        auto tmp = ExtractExpr::create(L, i, 1);
        res = ConcatExpr::create(res, tmp);
      }
      return res;
    }
    case Inst::Cttz: {
      ref<Expr> L = get(Ops[0]);
      unsigned Width = L->getWidth();
      ref<Expr> Val = L;
      for (unsigned i=0, j=0; j<Width/2; i++) {
        j = 1<<i;
        Val = OrExpr::create(Val, ShlExpr::create(Val,
                             klee::ConstantExpr::create(j, Width)));
      }
      return SubExpr::create(klee::ConstantExpr::create(Width, Width),
                             countOnes(Val));
    }
    case Inst::Ctlz: {
      ref<Expr> L = get(Ops[0]);
      unsigned Width = L->getWidth();
      ref<Expr> Val = L;
      for (unsigned i=0, j=0; j<Width/2; i++) {
        j = 1<<i;
        Val = OrExpr::create(Val, LShrExpr::create(Val,
                             klee::ConstantExpr::create(j, Width)));
      }
      return SubExpr::create(klee::ConstantExpr::create(Width, Width),
                             countOnes(Val));
    }
    case Inst::LogB: {
      ref<Expr> L = get(Ops[0]);
      unsigned Width = L->getWidth();
      ref<Expr> Val = L;
      for (unsigned i=0, j=0; j<Width/2; i++) {
        j = 1<<i;
        Val = OrExpr::create(Val, LShrExpr::create(Val,
                             klee::ConstantExpr::create(j, Width)));
      }
      auto W = klee::ConstantExpr::create(Width, Width);
      auto One = klee::ConstantExpr::create(1, Width);
      auto Ctlz = SubExpr::create(W, countOnes(Val));
      return SubExpr::create(SubExpr::create(W, Ctlz), One);
    }
    case Inst::BitWidth: {
      ref<Expr> L = get(Ops[0]);
      unsigned Width = L->getWidth();
      return klee::ConstantExpr::create(Width, Width);
    }

    case Inst::KnownOnesP: {
      auto VarAndOnes = klee::AndExpr::create(get(Ops[0]), get(Ops[1]));
      return klee::EqExpr::create(VarAndOnes, get(Ops[1]));
    }
    case Inst::KnownZerosP: {
      auto NotZeros = klee::NotExpr::create(get(Ops[1]));
      auto VarNotZero = klee::OrExpr::create(get(Ops[0]), NotZeros);
      return klee::EqExpr::create(VarNotZero, NotZeros);
    }
    case Inst::RangeP: {
      auto Var = get(Ops[0]);
      auto Lower = get(Ops[1]);
      auto Upper = get(Ops[2]);
      auto GELower = klee::SgeExpr::create(Var, Lower);
      auto LTUpper = klee::SltExpr::create(Var, Upper);
      auto Ordinary = klee::AndExpr::create(GELower, LTUpper);

      auto GEUpper = klee::SgeExpr::create(Var, Upper);
      auto LTLower = klee::SltExpr::create(Var, Lower);
      auto Wrapped = klee::OrExpr::create(GEUpper, LTLower);

      auto Cond = klee::SgtExpr::create(Upper, Lower);

      return klee::SelectExpr::create(Cond, Ordinary, Wrapped);
    }

    case Inst::DemandedMask: {
      return klee::AndExpr::create(get(Ops[0]), get(Ops[1]));
    }

    case Inst::Lop3: {
      uint8_t immlut = Ops[3]->Val.getZExtValue();
      return LUT[immlut](get(Ops[0]), get(Ops[1]), get(Ops[2]));
    }

    case Inst::FShl:
    case Inst::FShr: {
      unsigned IWidth = I->Width;
      ref<Expr> High = get(Ops[0]);
      ref<Expr> Low = get(Ops[1]);
      ref<Expr> ShAmt = get(Ops[2]);
      ref<Expr> ShAmtModWidth =
          URemExpr::create(ShAmt, klee::ConstantExpr::create(IWidth, IWidth));
      ref<Expr> Concatenated = ConcatExpr::create(High, Low);
      unsigned CWidth = Concatenated->getWidth();
      ref<Expr> ShAmtModWidthZExt = ZExtExpr::create(ShAmtModWidth, CWidth);
      ref<Expr> Shifted =
          I->K == Inst::FShl
              ? ShlExpr::create(Concatenated, ShAmtModWidthZExt)
              : LShrExpr::create(Concatenated, ShAmtModWidthZExt);
      unsigned BitOffset = I->K == Inst::FShr ? 0 : IWidth;
      return ExtractExpr::create(Shifted, BitOffset, IWidth);
    }
    case Inst::SAddO:
      return XorExpr::create(get(addnswUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::UAddO:
      return XorExpr::create(get(addnuwUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::SSubO:
      return XorExpr::create(get(subnswUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::USubO:
      return XorExpr::create(get(subnuwUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::SMulO:
      return XorExpr::create(get(mulnswUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::UMulO:
      return XorExpr::create(get(mulnuwUB(I)), klee::ConstantExpr::create(1, Expr::Bool));
    case Inst::ExtractValue: {
      unsigned Index = Ops[1]->Val.getZExtValue();
      return get(Ops[0]->Ops[Index]);
    }
    case Inst::SAddSat: {
      ref<Expr> add = AddExpr::create(get(Ops[0]), get(Ops[1]));
      auto sextL = SExtExpr::create(get(Ops[0]), I->Width + 1);
      auto sextR = SExtExpr::create(get(Ops[1]), I->Width + 1);
      auto addExt = AddExpr::create(sextL, sextR);
      auto smin = klee::ConstantExpr::alloc(llvm::APInt::getSignedMinValue(I->Width));
      auto smax = klee::ConstantExpr::alloc(llvm::APInt::getSignedMaxValue(I->Width));
      auto sminExt = SExtExpr::create(smin, I->Width + 1);
      auto smaxExt = SExtExpr::create(smax, I->Width + 1);
      auto pred = SleExpr::create(addExt, sminExt);

      auto pred2 = SgeExpr::create(addExt, smaxExt);
      auto select2 = SelectExpr::create(pred2, smax, add);

      return SelectExpr::create(pred, smin, select2);
    }
    case Inst::UAddSat: {
      ref<Expr> add = AddExpr::create(get(Ops[0]), get(Ops[1]));
      return SelectExpr::create(get(addnuwUB(I)), add, klee::ConstantExpr::alloc(llvm::APInt::getMaxValue(I->Width)));
    }
    case Inst::SSubSat: {
      ref<Expr> sub = SubExpr::create(get(Ops[0]), get(Ops[1]));
      auto sextL = SExtExpr::create(get(Ops[0]), I->Width + 1);
      auto sextR = SExtExpr::create(get(Ops[1]), I->Width + 1);
      auto subExt = SubExpr::create(sextL, sextR);
      auto smin = klee::ConstantExpr::alloc(llvm::APInt::getSignedMinValue(I->Width));
      auto smax = klee::ConstantExpr::alloc(llvm::APInt::getSignedMaxValue(I->Width));
      auto sminExt = SExtExpr::create(smin, I->Width + 1);
      auto smaxExt = SExtExpr::create(smax, I->Width + 1);
      auto pred = SleExpr::create(subExt, sminExt);

      auto pred2 = SgeExpr::create(subExt, smaxExt);
      auto select2 = SelectExpr::create(pred2, smax, sub);

      return SelectExpr::create(pred, smin, select2);
    }
    case Inst::USubSat: {
      ref<Expr> sub = SubExpr::create(get(Ops[0]), get(Ops[1]));
      return SelectExpr::create(get(subnuwUB(I)), sub, klee::ConstantExpr::alloc(llvm::APInt::getMinValue(I->Width)));
    }
    case Inst::SAddWithOverflow:
    case Inst::UAddWithOverflow:
    case Inst::SSubWithOverflow:
    case Inst::USubWithOverflow:
    case Inst::SMulWithOverflow:
    case Inst::UMulWithOverflow:

    case Inst::Custom: {
      return get(CustomInstructionMap[I->Name](LIC, I->Ops));
    }

    default:
      break;
    }
    llvm_unreachable("unknown kind");
  }

  ref<Expr> get(Inst *I) {
    ref<Expr> &E = ExprMap[I];
    if (E.isNull()) {
      E = build(I);
      assert(E->getWidth() == I->Width);
    }
    return E;
  }

  // get() is recursive. It already has problems with running out of stack
  // space with very trivial inputs, since there are a lot of IR instructions
  // it knows how to produce, and thus a lot of possible replacements.
  // But it has built-in caching. And recursion only kicks in if the Inst is not
  // found in cache. Thus we simply need to *try* to prepopulate the cache.
  // Note that we can't really split `get()` into `getSimple()` and
  // `getOrBuildRecursive()` because we won't reach every single of these Inst
  // because we only look at Ops...
  void prepopulateExprMap(Inst *Root) {
    // Collect all Inst that are reachable from this root. Go Use->Def.
    // An assumption is being made that there are no circular references.
    // Note that we really do want a simple vector, and do want duplicate
    // elements. In other words, if we have already added that Inst into vector,
    // we "move" it to the back of the vector. But without actually moving.
    llvm::SmallVector<Inst *, 32> AllInst;
    AllInst.emplace_back(Root);
    // Visit every Inst in the vector, but address them by index,
    // since we will be appending new entries at the end.
    for (size_t InstNum = 0; InstNum < AllInst.size(); InstNum++) {
      Inst *CurrInst = AllInst[InstNum];
      const std::vector<Inst *> &Ops = CurrInst->orderedOps();
      AllInst.insert(AllInst.end(), Ops.rbegin(), Ops.rend());
    }

    // And now, 'get()' every Inst, going in Def->Use direction.
    // That is, when we visit Inst N2, that has Ops N0 and N1,
    // the Inst's for N0 and N1 were already generated.
    llvm::for_each(llvm::reverse(AllInst), [this](Inst *CurrInst) {
      switch (CurrInst->K) {
      case Inst::UntypedConst:
      case Inst::SAddWithOverflow:
      case Inst::UAddWithOverflow:
      case Inst::SSubWithOverflow:
      case Inst::USubWithOverflow:
      case Inst::SMulWithOverflow:
      case Inst::UMulWithOverflow:
        return; // Avoid pre-generation for some Inst'ructions.
      default:
        break;
      }
      (void)get(CurrInst);
    });
  }

  ref<Expr> makeSizedArrayRead(unsigned Width, llvm::StringRef Name, Inst *Origin) {
    std::string NameStr;
    if (Name.empty())
      NameStr = "arr";
    else if (Name[0] >= '0' && Name[0] <= '9')
      NameStr = ("a" + Name).str();
    else
      NameStr = Name;
    const Array *array = Cache.CreateArray(ArrayNames.makeName(NameStr), 1, 0, 0, Expr::Int32, Width);
    Arrays.push_back(array);
    Vars.push_back(Origin);

    UpdateList UL(Arrays.back(), 0);
    return ReadExpr::create(UL, klee::ConstantExpr::alloc(0, Expr::Int32));
  }

};

}

std::unique_ptr<ExprBuilder> souper::createKLEEBuilder(InstContext &IC) {
  return std::unique_ptr<ExprBuilder>(new KLEEBuilder(IC));
}
