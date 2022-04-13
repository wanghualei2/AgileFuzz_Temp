/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/ADT/DAGDeltaAlgorithm.h"
#include "llvm/ADT/DeltaAlgorithm.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"

#include <string.h> 
#include <cstring> 

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override; 

  };

}


char AFLCoverage::ID = 0;
 

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C); 
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C); 
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C); 

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLMapPtrLaf =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_laf_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  GlobalVariable *AFLPrevLafLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__laf_afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;
  int extra_blocks = 0;
  int strcmp_blocks=0;
  int switch_blocks=0;
  int compare_blocks=0;

  for (auto &F : M)
    for (auto &BB : F) {  
      
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP)); 

      if (AFL_R(100) >= inst_ratio) continue;

      if((BB.getName().str().find("normal_basicblock")!=std::string::npos)){   

        unsigned int cur_loc = AFL_R(MAP_SIZE);

        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

        /* Load prev_loc */

        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

        /* Load SHM pointer */

        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MapPtrIdx =
            IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* Set prev_loc to cur_loc >> 1 */

        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        inst_blocks++; 
        
      } else{    
        
        int split_type=0;

        if((BB.getName().str().find("cmp_added")!=std::string::npos)){  
          split_type=1;
          strcmp_blocks++;
        }else if((BB.getName().str().find("inv_cmp")!=std::string::npos)||(BB.getName().str().find("injected")!=std::string::npos)
               ||(BB.getName().str().find("sign")!=std::string::npos)){
          split_type=2;
          compare_blocks+=1;
        }else if((BB.getName().str().find("NewDefault")!=std::string::npos)||(BB.getName().str().find("NodeBlock")!=std::string::npos)){
          split_type=3;
          switch_blocks+=1;
        }

        if(split_type==0){
          continue;
        }

        // errs()<<"block name: "<<BB.getName()<<"\n";

        // 1. 生成当前随机数
        unsigned int block_id = AFL_R(MAP_SIZE*8); 
        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, block_id);

        // 2. 加载前一个基本块随机数 
        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLafLoc); 
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());  

        // 3. 加载共享内存
        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtrLaf);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        
        // 4. 计算前边和后边异或的结果-->边ID 
        Value *branch_id=IRB.CreateZExt(IRB.CreateXor(PrevLocCasted, CurLoc),IRB.getInt32Ty()); 

        Value *branch_id_type; 

        if(split_type==1){ 
          
          branch_id_type=IRB.CreateZExt(IRB.CreateOr(branch_id, ConstantInt::get(Int32Ty, 0x40000)), IRB.getInt32Ty());  

        }else if(split_type==2){
 
          unsigned int temp = 0x3FFFF;
          Value * branch_id_type2=IRB.CreateZExt(IRB.CreateAnd(branch_id, ConstantInt::get(Int32Ty, temp)), IRB.getInt32Ty());
          ConstantInt *type2 = ConstantInt::get(Int32Ty, 0x20000);
          branch_id_type=IRB.CreateZExt(IRB.CreateOr(branch_id_type2, type2), IRB.getInt32Ty());

        }else{

          ConstantInt * type = ConstantInt::get(Int32Ty, 0x1FFFF);
          branch_id_type=IRB.CreateZExt(IRB.CreateAnd(branch_id, type), IRB.getInt32Ty()); 

        } 

        /** mov rax,rcx
         * shr rax,8
         */   
        Value *branch_id_high16 = IRB.CreateZExt(IRB.CreateLShr(branch_id_type, ConstantInt::get(Int8Ty, 3)), IRB.getInt32Ty());
        Value *MapPtrIndex =
            IRB.CreateGEP(MapPtr, branch_id_high16);
        /** mov dx,1
         *  shl dx,cx
         */   
        Value *branch_id_low3=IRB.CreateAnd(branch_id, ConstantInt::get(Int8Ty, 7));
        Value *MapPtrOffset = IRB.CreateShl(ConstantInt::get(Int8Ty, 1),branch_id_low3); 
 
        LoadInst *Counter = IRB.CreateLoad(MapPtrIndex);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateOr(Counter, MapPtrOffset);

        IRB.CreateStore(Incr, MapPtrIndex)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* 将当前基本块右移一位，然后保存 */ 
        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, block_id >> 1), AFLPrevLafLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        extra_blocks++; 
      }  

    }

  /* Say something nice. */

  if (!be_quiet) {

    OKF("total %d split_blocks !",extra_blocks);
    OKF("total %d strcmp_blocks !",strcmp_blocks);
    OKF("total %d compare_blocks !",compare_blocks);
    OKF("total %d switch_blocks !",switch_blocks);
    if (!inst_blocks){
      WARNF("No instrumentation targets found.");
    } 
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

} 


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
