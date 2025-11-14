#include "llvm/Transforms/Obfuscation/BogusControlFlow2.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <vector>

using namespace llvm;

namespace polaris {

BasicBlock *cloneBasicBlock(BasicBlock *BB) {
  ValueToValueMapTy VMap;
  BasicBlock *cloneBB = CloneBasicBlock(BB, VMap, "cloneBB", BB->getParent());
  BasicBlock::iterator origI = BB->begin();
  for (Instruction &I : *cloneBB) {
    for (int i = 0; i < I.getNumOperands(); i++) {
      Value *V = MapValue(I.getOperand(i), VMap);
      if (V) {
        I.setOperand(i, V);
      }
    }
    SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
    I.getAllMetadata(MDs);
    for (std::pair<unsigned, MDNode *> pair : MDs) {
      MDNode *MD = MapMetadata(pair.second, VMap);
      if (MD) {
        I.setMetadata(pair.first, MD);
      }
    }
    I.setDebugLoc(origI->getDebugLoc());
    origI++;
  }
  return cloneBB;
}

Value *createVarFromFuncOrGlobal(Function &F, IRBuilder<> &B) {
  Module *M = F.getParent();
  LLVMContext &Ctx = M->getContext();
  Type *I32 = Type::getInt32Ty(Ctx);
  Type *IntPtrTy = B.getIntPtrTy(M->getDataLayout());

  SmallVector<Argument *, 4> Candidates;
  for (Argument &A : F.args()) {
    if (A.getType()->isIntegerTy() || A.getType()->isPointerTy()) {
      Candidates.push_back(&A);
    }
  }

  Value *X = nullptr;

  if (!Candidates.empty()) {
    llvm::errs() << "Find argument\n";
    unsigned idx = getRandomNumber() % Candidates.size();
    Argument *Chosen = Candidates[idx];

    if (Chosen->getType()->isIntegerTy()) {
      unsigned bw = cast<IntegerType>(Chosen->getType())->getBitWidth();
      if (bw < 32)
        X = B.CreateZExt(Chosen, I32, "x.zext");
      else if (bw > 32)
        X = B.CreateTrunc(Chosen, I32, "x.trunc");
      else
        X = Chosen; // i32
    } else {
      // ptr -> intptr -> i32
      Value *P2I = B.CreatePtrToInt(Chosen, IntPtrTy, "x.ptrtoint");
      unsigned pw = cast<IntegerType>(IntPtrTy)->getBitWidth();
      if (pw < 32)
        X = B.CreateZExt(P2I, I32, "x.zext");
      else if (pw > 32)
        X = B.CreateTrunc(P2I, I32, "x.trunc");
      else
        X = P2I;
    }
  } else {
    GlobalVariable *XGV = M->getGlobalVariable("x", /*AllowInternal=*/true);
    if (!XGV) {
      XGV = new GlobalVariable(
          *M, I32, /*isConstant=*/false, GlobalValue::CommonLinkage,
          ConstantInt::get(I32, 0), "x");
    }
    X = B.CreateLoad(I32, XGV, "x.load");
  }

  return X; // i32
}
Value *createBogusCmp(BasicBlock *insertAfter) {
  // if((y < 10 || x * (x + 1) % 2 == 0))
  Module *M = insertAfter->getModule();
  LLVMContext &context = M->getContext();
  Function *F = insertAfter->getParent();

  IRBuilder<> builder(context);
  builder.SetInsertPoint(insertAfter);
  Value *x = createVarFromFuncOrGlobal(*F, builder);
  Value *y = createVarFromFuncOrGlobal(*F, builder);
  Value *cond1 =
      builder.CreateICmpSLT(y, ConstantInt::get(Type::getInt32Ty(context), rand()));
  Value *op1 =
      builder.CreateAdd(x, ConstantInt::get(Type::getInt32Ty(context), 1));
  Value *op2 = builder.CreateMul(op1, x);
  Value *op3 =
      builder.CreateURem(op2, ConstantInt::get(Type::getInt32Ty(context), 2));
  Value *cond2 =
      builder.CreateICmpEQ(op3, ConstantInt::get(Type::getInt32Ty(context), 0));
  return BinaryOperator::CreateOr(cond1, cond2, "", insertAfter);
}

PreservedAnalyses BogusControlFlow2::run(Function &F,
                                         FunctionAnalysisManager &AM) {

  if (readAnnotate(F).find("boguscfg") != std::string::npos) {
    std::vector<BasicBlock *> origBB;
    for (BasicBlock &BB : F) {
      origBB.push_back(&BB);
    }
    for (BasicBlock *BB : origBB) {
      if (isa<InvokeInst>(BB->getTerminator()) || BB->isEHPad() ||
          (getRandomNumber() % 100) <= 20) {
        continue;
      }
      BasicBlock *headBB = BB;
      BasicBlock *bodyBB =
          BB->splitBasicBlock(BB->getFirstNonPHIOrDbgOrLifetime(), "bodyBB");
      BasicBlock *tailBB =
          bodyBB->splitBasicBlock(bodyBB->getTerminator(), "endBB");
      BasicBlock *cloneBB = cloneBasicBlock(bodyBB);

      BB->getTerminator()->eraseFromParent();
      bodyBB->getTerminator()->eraseFromParent();
      cloneBB->getTerminator()->eraseFromParent();

      Value *cond1 = createBogusCmp(BB);
      Value *cond2 = createBogusCmp(bodyBB);

      BranchInst::Create(bodyBB, cloneBB, cond1, BB);
      BranchInst::Create(tailBB, cloneBB, cond2, bodyBB);
      BranchInst::Create(bodyBB, cloneBB);
    }
    return PreservedAnalyses::none();
  }
  return PreservedAnalyses::all();
}

}; // namespace polaris
