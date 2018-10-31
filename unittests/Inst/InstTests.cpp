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

#include "llvm/Support/raw_ostream.h"
#include "souper/Inst/Inst.h"
#include "gtest/gtest.h"

using namespace souper;

TEST(InstTest, Fold) {
  InstContext IC;

  Inst *I1 = IC.getConst(llvm::APInt(64, 0));
  Inst *I2 = IC.getConst(llvm::APInt(64, 0));

  ASSERT_EQ(I2, I1);

  Inst *I3 = IC.getConst(llvm::APInt(64, 1));
  Inst *I4 = IC.getConst(llvm::APInt(32, 0));

  ASSERT_NE(I3, I1);
  ASSERT_NE(I4, I1);
  ASSERT_NE(I4, I3);

  Inst *I1AI3 = IC.getInst(Inst::Add, 64, {I1, I3});
  Inst *I3AI1 = IC.getInst(Inst::Add, 64, {I3, I1});

  ASSERT_EQ(I1AI3, I3AI1);

  Inst *I1SI3 = IC.getInst(Inst::Sub, 64, {I1, I3});
  Inst *I3SI1 = IC.getInst(Inst::Sub, 64, {I3, I1});

  ASSERT_NE(I1SI3, I3SI1);
}

TEST(InstTest, Print) {
  InstContext IC;

  std::string Str;
  llvm::raw_string_ostream SS(Str);

  Inst *I1 = IC.getConst(llvm::APInt(64, 1));
  Inst *I2 = IC.getConst(llvm::APInt(64, 2));
  Inst *I3 = IC.getConst(llvm::APInt(64, 3));

  Inst *I1AI2 = IC.getInst(Inst::Add, 64, {I1, I2});
  Inst *I1AI2MI3 = IC.getInst(Inst::Mul, 64, {I1AI2, I3});
  ReplacementContext Context;

  EXPECT_EQ("%1", Context.printInst(I1AI2MI3, SS, /*printNames=*/false));
  EXPECT_EQ("%0:i64 = add 1:i64, 2:i64\n"
            "%1:i64 = mul 3:i64, %0\n", SS.str());
}

TEST(InstTest, Evaluate) {
  InstContext IC;

  Inst *I1 = IC.getConst(llvm::APInt(64, 2));
  Inst *I2 = IC.getConst(llvm::APInt(64, 3));

  std::unordered_map<std::string, EvalValue> cache;

  EXPECT_EQ(Evaluate(IC.getInst(Inst::Add, 64, {I1, I2}), cache).Val, 5);
  EXPECT_EQ(Evaluate(IC.getInst(Inst::Sub, 64, {I1, I2}), cache).Val, -1);
  EXPECT_EQ(Evaluate(IC.getInst(Inst::Mul, 64, {I1, I2}), cache).Val, 6);
  EXPECT_EQ(Evaluate(IC.getInst(Inst::And, 64, {I1, I2}), cache).Val, 2);
  EXPECT_EQ(Evaluate(IC.getInst(Inst::Or, 64, {I1, I2}), cache).Val, 3);
  EXPECT_EQ(Evaluate(IC.getInst(Inst::Xor, 64, {I1, I2}), cache).Val, 1);
}

TEST(InstTest, Evaluate2) {
  InstContext IC;

  Inst *I0 = IC.getConst(llvm::APInt(64, 2));
  Inst *I1 = IC.getConst(llvm::APInt(64, 3));

  auto I2 = IC.getInst(Inst::Xor, 32 , {I0, I1});
  auto I3 = IC.getInst(Inst::Xor, 32 , {I1, I2});
  auto I4 = IC.getInst(Inst::Xor, 32 , {I2, I3});

  std::unordered_map<std::string, EvalValue> cache;
  EXPECT_EQ(Evaluate(I4, cache).Val, 3);
}

TEST(InstTest, Evaluate3) {
  InstContext IC;

  Inst *I0 = IC.createVar(32, "0");
  Inst *I1 = IC.createVar(32, "1");


  auto I2 = IC.getInst(Inst::Xor, 32 , {I0, I1});
  auto I3 = IC.getInst(Inst::Xor, 32 , {I1, I2});
  auto I4 = IC.getInst(Inst::Xor, 32 , {I2, I3});

  std::unordered_map<std::string, EvalValue> cache;
  cache["0"] = {llvm::APInt(32, 2), false, false};
  cache["1"] = {llvm::APInt(32, 3), false, false};

  EXPECT_EQ(Evaluate(I4, cache).Val, 3);
}



TEST(InstTest, KnownBits) {
  InstContext IC;
  Inst *I1 = IC.getConst(llvm::APInt(64, 2));
  Inst *I2 = IC.getConst(llvm::APInt(64, 3));

  Inst *IShift = IC.getInst(Inst::Shl, 64, {I2, I1});

  Inst *IVar = IC.createVar(8, "x");

  std::unordered_map<std::string, EvalValue> cache;
  cache["x"] = {llvm::APInt(8, 5), false, false};

  auto result1 = FindKnownBits(IShift, cache);

  EXPECT_EQ(
    std::string("0000000000000000000000000000000000000000000000000000000000001100"),
    IShift->getKnownBitsString(result1.Zero, result1.One));

  auto result2 = FindKnownBits(IVar, cache);
  EXPECT_EQ(std::string("00000101"), IVar->getKnownBitsString(result2.Zero, result2.One));

}
