/*
 * Copyright 2016 laf-intel
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/ValueTracking.h"

#include <set>

using namespace llvm;

namespace {

  class SplitSwitchesTransform : public ModulePass {

    public:
      static char ID;
      SplitSwitchesTransform() : ModulePass(ID) {
      } 

      bool runOnModule(Module &M) override;

      const char *getPassName() const override {
        return "splits switch constructs";
      }

      struct CaseExpr {
        ConstantInt* Val;
        BasicBlock* BB;

        CaseExpr(ConstantInt *val = nullptr, BasicBlock *bb = nullptr) :
          Val(val), BB(bb) { }
      };

    typedef std::vector<CaseExpr> CaseVector;

    private:
      bool splitSwitches(Module &M);
      bool transformCmps(Module &M, const bool processStrcmp, const bool processMemcmp);
      BasicBlock* switchConvert(CaseVector Cases, std::vector<bool> bytesChecked,
                                BasicBlock* OrigBlock, BasicBlock* NewDefault,
                                Value* Val, unsigned level);
  };

}

char SplitSwitchesTransform::ID = 0;


/* switchConvert - Transform simple list of Cases into list of CaseRange's */
BasicBlock* SplitSwitchesTransform::switchConvert(CaseVector Cases, std::vector<bool> bytesChecked, 
                                            BasicBlock* OrigBlock, BasicBlock* NewDefault,
                                            Value* Val, unsigned level) {

  unsigned ValTypeBitWidth = Cases[0].Val->getBitWidth();
  IntegerType *ValType  = IntegerType::get(OrigBlock->getContext(), ValTypeBitWidth);
  IntegerType *ByteType = IntegerType::get(OrigBlock->getContext(), 8);
  unsigned BytesInValue = bytesChecked.size();
  std::vector<uint8_t> setSizes;
  std::vector<std::set<uint8_t>> byteSets(BytesInValue, std::set<uint8_t>());


  /* for each of the possible cases we iterate over all bytes of the values
   * build a set of possible values at each byte position in byteSets */
  for (CaseExpr& Case: Cases) {
    for (unsigned i = 0; i < BytesInValue; i++) {

      uint8_t byte = (Case.Val->getZExtValue() >> (i*8)) & 0xFF;
      byteSets[i].insert(byte);
    }
  }

  unsigned smallestIndex = 0;
  unsigned smallestSize = 257;
  for(unsigned i = 0; i < byteSets.size(); i++) {
    if (bytesChecked[i])
      continue;
    if (byteSets[i].size() < smallestSize) {
      smallestIndex = i;
      smallestSize = byteSets[i].size();
    }
  }
  assert(bytesChecked[smallestIndex] == false);

  /* there are only smallestSize different bytes at index smallestIndex */
 
  Instruction *Shift, *Trunc;
  Function* F = OrigBlock->getParent();
  BasicBlock* NewNode = BasicBlock::Create(Val->getContext(), "NodeBlock", F);
  Shift = BinaryOperator::Create(Instruction::LShr, Val, ConstantInt::get(ValType, smallestIndex * 8));
  NewNode->getInstList().push_back(Shift);

  if (ValTypeBitWidth > 8) {
    Trunc = new TruncInst(Shift, ByteType);
    NewNode->getInstList().push_back(Trunc);
  }
  else {
    /* not necessary to trunc */
    Trunc = Shift;
  }

  /* this is a trivial case, we can directly check for the byte,
   * if the byte is not found go to default. if the byte was found
   * mark the byte as checked. if this was the last byte to check
   * we can finally execute the block belonging to this case */


  if (smallestSize == 1) {
    uint8_t byte = *(byteSets[smallestIndex].begin());

    /* insert instructions to check whether the value we are switching on is equal to byte */
    ICmpInst* Comp = new ICmpInst(ICmpInst::ICMP_EQ, Trunc, ConstantInt::get(ByteType, byte), "byteMatch");
    NewNode->getInstList().push_back(Comp);

    bytesChecked[smallestIndex] = true;
    if (std::all_of(bytesChecked.begin(), bytesChecked.end(), [](bool b){return b;} )) {
      assert(Cases.size() == 1);
      BranchInst::Create(Cases[0].BB, NewDefault, Comp, NewNode);

      /* we have to update the phi nodes! */
      for (BasicBlock::iterator I = Cases[0].BB->begin(); I != Cases[0].BB->end(); ++I) {
        if (!isa<PHINode>(&*I)) {
          continue;
        }
        PHINode *PN = cast<PHINode>(I);

        /* Only update the first occurence. */
        unsigned Idx = 0, E = PN->getNumIncomingValues();
        for (; Idx != E; ++Idx) {
          if (PN->getIncomingBlock(Idx) == OrigBlock) {
            PN->setIncomingBlock(Idx, NewNode);
            break;
          }
        }
      }
    }
    else {
      BasicBlock* BB = switchConvert(Cases, bytesChecked, OrigBlock, NewDefault, Val, level + 1);
      BranchInst::Create(BB, NewDefault, Comp, NewNode);
    }
  }
  /* there is no byte which we can directly check on, split the tree */
  else {

    std::vector<uint8_t> byteVector;
    std::copy(byteSets[smallestIndex].begin(), byteSets[smallestIndex].end(), std::back_inserter(byteVector));
    std::sort(byteVector.begin(), byteVector.end());
    uint8_t pivot = byteVector[byteVector.size() / 2];

    /* we already chose to divide the cases based on the value of byte at index smallestIndex
     * the pivot value determines the threshold for the decicion; if a case value
     * is smaller at this byte index move it to the LHS vector, otherwise to the RHS vector */

    CaseVector LHSCases, RHSCases;

    for (CaseExpr& Case: Cases) {
      uint8_t byte = (Case.Val->getZExtValue() >> (smallestIndex*8)) & 0xFF;

      if (byte < pivot) {
        LHSCases.push_back(Case);
      }
      else {
        RHSCases.push_back(Case);
      }
    }
    BasicBlock *LBB, *RBB;
    LBB = switchConvert(LHSCases, bytesChecked, OrigBlock, NewDefault, Val, level + 1);
    RBB = switchConvert(RHSCases, bytesChecked, OrigBlock, NewDefault, Val, level + 1);

    /* insert instructions to check whether the value we are switching on is equal to byte */
    ICmpInst* Comp = new ICmpInst(ICmpInst::ICMP_ULT, Trunc, ConstantInt::get(ByteType, pivot), "byteMatch");
    NewNode->getInstList().push_back(Comp);
    BranchInst::Create(LBB, RBB, Comp, NewNode);

  }

  return NewNode;
}

bool SplitSwitchesTransform::splitSwitches(Module &M) {

  std::vector<SwitchInst*> switches; 

  /* iterate over all functions, bbs and instruction and add
   * all switches to switches vector for later processing */
  for (auto &F : M) {
    bool is_add=false; 
    for (auto &BB : F) { 
      if((BB.getName().str().find("normal_basicblock")!=std::string::npos)){  
        is_add=true;
        break;
      }
    } 
    for (auto &BB : F) {
      if(!is_add)
        BB.setName("normal_basicblock");
      SwitchInst* switchInst = nullptr;

      if ((switchInst = dyn_cast<SwitchInst>(BB.getTerminator()))) {
        if (switchInst->getNumCases() < 1)
            continue;
          switches.push_back(switchInst);
      }
    }
  }

  if (!switches.size())
    return false;
  errs() << "Rewriting " << switches.size() << " switch statements " << "\n";

  for (auto &SI: switches) {

    BasicBlock *CurBlock = SI->getParent();
    BasicBlock *OrigBlock = CurBlock;
    Function *F = CurBlock->getParent();
    /* this is the value we are switching on */
    Value *Val = SI->getCondition();
    BasicBlock* Default = SI->getDefaultDest();

    /* If there is only the default destination, don't bother with the code below. */
    if (!SI->getNumCases()) {
      continue;
    }

    /* Create a new, empty default block so that the new hierarchy of
     * if-then statements go to this and the PHI nodes are happy.
     * if the default block is set as an unreachable we avoid creating one
     * because will never be a valid target.*/
    BasicBlock *NewDefault = nullptr;
    NewDefault = BasicBlock::Create(SI->getContext(), "NewDefault");
    NewDefault->insertInto(F, Default);
    BranchInst::Create(Default, NewDefault);


    /* Prepare cases vector. */
    CaseVector Cases;
    for (SwitchInst::CaseIt i = SI->case_begin(), e = SI->case_end(); i != e; ++i)
      Cases.push_back(CaseExpr(i.getCaseValue(), i.getCaseSuccessor()));
    
    std::vector<bool> bytesChecked(Cases[0].Val->getBitWidth() / 8, false);
    BasicBlock* SwitchBlock = switchConvert(Cases, bytesChecked, OrigBlock, NewDefault, Val, 0);

    /* Branch to our shiny new if-then stuff... */
    BranchInst::Create(SwitchBlock, OrigBlock);

    /* We are now done with the switch instruction, delete it. */
    CurBlock->getInstList().erase(SI);


   /* we have to update the phi nodes! */
   for (BasicBlock::iterator I = Default->begin(); I != Default->end(); ++I) {
     if (!isa<PHINode>(&*I)) {
      continue;
     }
     PHINode *PN = cast<PHINode>(I);

     /* Only update the first occurence. */
     unsigned Idx = 0, E = PN->getNumIncomingValues();
     for (; Idx != E; ++Idx) {
       if (PN->getIncomingBlock(Idx) == OrigBlock) {
         PN->setIncomingBlock(Idx, NewDefault);
         break;
       }
     }
   }
 }

 verifyModule(M);
 return true;
}

bool SplitSwitchesTransform::runOnModule(Module &M) {

  llvm::errs() << "Running split-switches-pass by whl\n"; 
  splitSwitches(M);
  verifyModule(M);

  return true;
}

static void registerSplitSwitchesTransPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  auto p = new SplitSwitchesTransform();
  PM.add(p);

}

static RegisterStandardPasses RegisterSplitSwitchesTransPass(
    PassManagerBuilder::EP_OptimizerLast, registerSplitSwitchesTransPass);

static RegisterStandardPasses RegisterSplitSwitchesTransPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerSplitSwitchesTransPass);
