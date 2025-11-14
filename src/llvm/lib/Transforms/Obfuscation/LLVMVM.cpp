#include "llvm/Transforms/Obfuscation/LLVMVM.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LowerSwitch.h"
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <utility>
#include <vector>

using namespace llvm;
namespace polaris {

Type *getAllocateType(Value *v) {
  if (isa<AllocaInst>(*v)) {
    return ((AllocaInst *)v)->getAllocatedType();
  }
  assert(false);
  return nullptr;
}
Type *getGlobalVariableType(GlobalVariable *gv) {
  return gv->getInitializer()->getType();
}

void LLVMVM::demoteRegisters(Function *f) {
  std::vector<PHINode *> tmpPhi;
  std::vector<Instruction *> tmpReg;
  BasicBlock *bbEntry = &*f->begin();
  do {
    tmpPhi.clear();
    tmpReg.clear();
    for (Function::iterator i = f->begin(); i != f->end(); i++) {
      for (BasicBlock::iterator j = i->begin(); j != i->end(); j++) {
        if (isa<PHINode>(j)) {
          PHINode *phi = cast<PHINode>(j);
          tmpPhi.push_back(phi);
          continue;
        }
        if (!(isa<AllocaInst>(j) && j->getParent() == bbEntry) &&
            j->isUsedOutsideOfBlock(&*i)) {
          tmpReg.push_back(&*j);
          continue;
        }
      }
    }
    for (unsigned int i = 0; i < tmpReg.size(); i++)
      DemoteRegToStack(*tmpReg.at(i), f->begin()->getTerminator());
    for (unsigned int i = 0; i < tmpPhi.size(); i++)
      DemotePHIToStack(tmpPhi.at(i), f->begin()->getTerminator());
  } while (tmpReg.size() != 0 || tmpPhi.size() != 0);
}
BasicBlock *LLVMVM::handleAlloca(Function &f, std::map<Value *, int> &value_map,
                                 std::vector<std::pair<int, int>> &remap,
                                 int &space) {
  std::vector<AllocaInst *> allocas;
  printf("    -collect allocainst\n");
  for (BasicBlock &bb : f)
    for (Instruction &i : bb) {
      if (isa<AllocaInst>(i))
        allocas.push_back((AllocaInst *)&i);
    }
  BasicBlock *alloca_block = &f.getEntryBlock();
  printf("    -move allocainst before\n");
  for (AllocaInst *a : allocas)
    a->moveBefore(&*alloca_block->getFirstInsertionPt());
  printf("    -split allocainst block\n");
  for (Instruction &i : *alloca_block) {
    if (!isa<AllocaInst>(i)) {
      alloca_block->splitBasicBlock(&i);
      break;
    }
  }
  printf("    -calculate locals address\n");
  DataLayout data = f.getParent()->getDataLayout();
  for (AllocaInst *a : allocas) {
    int real_addr = space;
    a->print(llvm::errs());

    std::optional<TypeSize> alloca_size = a->getAllocationSize(data);
    if (!alloca_size) {
      assert(false && "[!] fail to get type size");
    }
    int size_int = static_cast<int>(alloca_size->getFixedSize());
    printf("   [%4d] alloc size %d\n", real_addr, size_int);

    space += size_int; // data.getTypeAllocSize(a->getAllocatedType());
    int ptr_addr = space;
    value_map[a] = space;
    printf("   [%4d] store ptr size %d\n", ptr_addr,
           data.getTypeAllocSize(a->getType()));
    space += data.getTypeAllocSize(a->getType());
    remap.push_back(std::make_pair(ptr_addr, real_addr));
  }

  return alloca_block;
}
Type *getTypeAfterIndex(GetElementPtrInst *gep, int index) {
  Type *type = gep->getSourceElementType();
  std::vector<Value *> list;
  int s = 0;
  for (auto iter = gep->idx_begin(); iter != gep->idx_end(); iter++) {
    Value *v = *iter;
    list.push_back(v);
    if (++s > index) {
      break;
    }
  }
  return GetElementPtrInst::getIndexedType(type, list);
}
void findOperand(Instruction &instr,
                 std::vector<std::pair<int, Value *>> &operand,
                 std::vector<std::pair<int, Value *>> &unsupported) {

  int i = 0;
  for (Value *opnd : instr.operands()) {
    if (isa<ConstantInt>(*opnd) /* || isa<ConstantFP>(*opnd)*/ ||
        isa<Instruction>(*opnd) || isa<Argument>(*opnd)) {
      operand.push_back(std::make_pair(i, opnd));
    } else
      unsupported.push_back(std::make_pair(i, opnd));
    i++;
  }
  if (isa<GetElementPtrInst>(instr)) {
    instr.print(llvm::errs());
    GetElementPtrInst *gep = (GetElementPtrInst *)&instr;
    std::vector<std::pair<int, Value *>> new_op;
    for (auto iter = operand.begin(); iter != operand.end(); iter++) {
      int index = iter->first;
      if (index <= 1) {
        new_op.push_back(*iter);
        continue;
      }
      Type *pa = getTypeAfterIndex(gep, index - 2);
      if (pa->isStructTy()) {
        unsupported.push_back(*iter);
      } else {
        new_op.push_back(*iter);
      }
    }
    operand.clear();
    for (auto iter = new_op.begin(); iter != new_op.end(); iter++) {
      operand.push_back(*iter);
    }
    // printf("------------------------------\n");
  }
  /*if (isa<GetElementPtrInst>(instr)) {
  GetElementPtrInst *gep = (GetElementPtrInst *)&instr;
  Type *type = gep->getSourceElementType();
  if (type->isStructTy()) {
    std::pair<int, Value *> p = std::make_pair(gep->getPointerOperandIndex(),
                                               gep->getPointerOperand());
    for (auto iter = operand.begin(); iter != operand.end(); iter++) {
      if (*iter != p) {
        unsupported.push_back(*iter);
        printf("%d", iter->first);
        iter->second->dump();
      }
    }
    operand.clear();
    operand.push_back(p);
  }

} else */
  if (isa<CallInst>(instr)) {

    CallInst *call = (CallInst *)&instr;
    Function *function = call->getCalledFunction();
    if (function != nullptr) {
      std::vector<Value *> immargs;
      AttributeList attrs = function->getAttributes();
      for (size_t i = 0; i < function->arg_size(); i++) {
        Value *arg = call->getArgOperand(i);
        if (attrs.hasParamAttr(i, Attribute::ImmArg))
          immargs.push_back(arg);
      }
      std::vector<std::pair<int, Value *>> to_move;
      for (auto iter = operand.begin(); iter != operand.end(); iter++) {
        if (std::find(immargs.begin(), immargs.end(), iter->second) !=
            immargs.end()) {
          to_move.push_back(*iter);
        }
      }
      for (auto iter = to_move.begin(); iter != to_move.end(); iter++) {
        operand.erase(std::find(operand.begin(), operand.end(), *iter));
        unsupported.push_back(*iter);
      }
    }
  }
}
VMOpInfo *LLVMVM::getOrCreateRawOp(Instruction &instr,
                                   std::vector<VMOpInfo *> &ops) {
  std::vector<std::pair<int, Value *>> operand1, un1;

  findOperand(instr, operand1, un1);
  for (VMOpInfo *info : ops) {
    if (info->builtin_type != RAW_INST)
      continue;
    if (info->instr->isSameOperationAs(&instr)) {

      std::vector<std::pair<int, Value *>> operand2, un2;
      findOperand(*info->instr, operand2, un2);
      if (un1.size() != un2.size())
        continue;
      bool ok = true;
      for (int i = 0; i < un1.size(); i++) {
        if (un1[i] != un2[i]) {
          ok = false;
          break;
        }
      }
      if (ok)
        return info;
    }
  }
  VMOpInfo *news = new VMOpInfo();

  news->instr = &instr;
  for (int i = 0; i < operand1.size(); i++)
    news->opnds.push_back(operand1.at(i));

  ops.push_back(news);
  return news;
}
bool LLVMVM::check(Function &f) {
  for (BasicBlock &bb : f)
    for (Instruction &i : bb) {
      if ((i.isTerminator() && !isa<BranchInst>(i) && !isa<ReturnInst>(i)) ||
          i.isFuncletPad()) {
        printf("[!] Unsupported Instruction Type: %s\n", i.getOpcodeName());
        return false;
      }
    }
  return true;
}
void LLVMVM::createBuiltinOps(std::vector<VMOpInfo *> &ops) {

  VMOpInfo *jump_to = new VMOpInfo();
  jump_to->builtin_type = JUMP_TO;
  ops.push_back(jump_to);

  VMOpInfo *branch = new VMOpInfo();
  branch->builtin_type = BRANCH;
  ops.push_back(branch);

  int size[4] = {1, 2, 4, 8};
  for (int i = 0; i < 4; i++) {
    VMOpInfo *store = new VMOpInfo();
    store->builtin_type = STORE_IMM;
    store->op_size = size[i];
    ops.push_back(store);
  }

  for (int i = 0; i < 3; i++) {
    VMOpInfo *push = new VMOpInfo();
    push->builtin_type = PUSH_ADDR;
    push->op_size = size[i];
    ops.push_back(push);
  }
}
int getRand(int range, std::set<int> &used) {
  assert(used.size() / 2 < range);
  int ptr = rand() % range;
  while (used.find(ptr) != used.end()) {
    ptr = rand() % range;
  }
  return ptr;
}
void LLVMVM::allocateOpcode(std::vector<VMOpInfo *> &ops) {
  int processed = 0;
  std::map<std::pair<int, int>, std::set<int>> prefixs;
  prefixs[std::make_pair(0, 0)] = std::set<int>();
  int prob_table[3] = {50, 30, 20};
  while (processed < ops.size() && prefixs.size() != 0) {
    int c = rand() % prefixs.size(), p = 0;
    std::pair<int, int> choose;
    std::map<std::pair<int, int>, std::set<int>>::iterator iter;
    for (iter = prefixs.begin(); iter != prefixs.end(); iter++, p++) {
      if (p == c) {
        choose = iter->first;
        break;
      }
    }
    std::set<int> *used = &prefixs[choose];
    int used_val = used->size();

    if (used_val >= 0xff) {
      prefixs.erase(iter);
      continue;
    }
    int prefix_val = choose.first, prefix_len = choose.second;
    ops[processed]->opcode.len = prefix_len + 1;
    for (int i = 0; i < prefix_len; i++) {
      ops[processed]->opcode.code[i] = prefix_val & 0xff;
      prefix_val >>= 8;
    }
    unsigned char rand_val = getRand(256, *used);
    ops[processed]->opcode.code[prefix_len] = rand_val;
    used->insert(rand_val);
    processed++;
    if (prefix_len < 3 && used_val < 0xff &&
        rand() % 100 > (100 - prob_table[prefix_len])) {
      rand_val = getRand(256, *used);
      prefixs[std::make_pair(choose.first | ((rand_val) << (8 * prefix_len)),
                             prefix_len + 1)] = std::set<int>();
      used->insert(rand_val);
    }
  }
  assert(processed == ops.size() && "fail to allocate opcode...");
}
void LLVMVM::destoryRandExpr(RandExpr *root) {
  if (root->op != CONST && root->op != VAR) {
    destoryRandExpr(root->l);
    destoryRandExpr(root->r);
  }
  delete root;
  return;
}
RandExpr *LLVMVM::generateRandExpr(int depth) {

  if (depth < 0) {
    RandExpr *var = new RandExpr();
    var->op = VAR;
    return var;
  }

  int op = rand() % 5 + 1;
  RandExpr *n = new RandExpr();
  n->op = op;
  RandExpr *son = generateRandExpr(depth - 1);
  if (son->op == VAR) {
    RandExpr *t = new RandExpr();
    t->op = CONST;
    t->data = (rand() << 16) | rand();
    if (rand() % 2) {
      n->l = son;
      n->r = t;
    } else {
      n->r = son;
      n->l = t;
    }

  } else {
    n->l = son;
    n->r = generateRandExpr(depth - 1);
  }

  return n;
}
void exprDump(RandExpr *tree) {
  if (tree->op == VAR) {
    printf("x");
    return;
  } else if (tree->op == CONST) {
    printf("0x%x", tree->data);
    return;
  } else if (tree->op == SHL) {
    printf("(");
    exprDump(tree->l);
    printf(")");
    printf(" << ");
    printf("(");
    exprDump(tree->r);
    printf(")");
    return;
  } else if (tree->op == SHR) {
    printf("(");
    exprDump(tree->l);
    printf(")");
    printf(" >> ");
    printf("(");
    exprDump(tree->r);
    printf(")");
    return;
  } else if (tree->op == XOR) {
    printf("(");
    exprDump(tree->l);
    printf(")");
    printf(" ^ ");
    printf("(");
    exprDump(tree->r);
    printf(")");
    return;
  }
}
Value *LLVMVM::randExpr2Ir(IRBuilder<> &irb, Value *val, RandExpr *tree) {
  // exprDump(tree);
  // printf("\n");
  if (tree->op == VAR) {
    return val;
  } else if (tree->op == CONST) {
    return irb.getInt32(tree->data);
  } else if (tree->op == SHL) {
    return irb.CreateShl(randExpr2Ir(irb, val, tree->l),
                         randExpr2Ir(irb, val, tree->r));
  } else if (tree->op == SHR) {
    return irb.CreateLShr(randExpr2Ir(irb, val, tree->l),
                          randExpr2Ir(irb, val, tree->r));
  } else if (tree->op == XOR) {
    return irb.CreateXor(randExpr2Ir(irb, val, tree->l),
                         randExpr2Ir(irb, val, tree->r));
  } else if (tree->op == OR) {
    return irb.CreateOr(randExpr2Ir(irb, val, tree->l),
                        randExpr2Ir(irb, val, tree->r));
  } else if (tree->op == ADD) {
    return irb.CreateAdd(randExpr2Ir(irb, val, tree->l),
                         randExpr2Ir(irb, val, tree->r));
  }
}
Function *LLVMVM::buildCipher(Module *mod) {
  FunctionType *type =
      FunctionType::get(Type::getInt8Ty(mod->getContext()),
                        {Type::getInt32PtrTy(mod->getContext())}, false);
  Function *cipher = Function::Create(type, GlobalValue::PrivateLinkage,
                                      Twine("xorshift32"), mod);
  BasicBlock *block = BasicBlock::Create(cipher->getContext(), "bb", cipher);
  IRBuilder<> irb(block);
  Argument *arg_val = cipher->getArg(0);
  Value *x = irb.CreateAlloca(irb.getInt32Ty());
  irb.CreateStore(irb.CreateLoad(irb.getInt32Ty(), arg_val), x);
  irb.CreateStore(
      irb.CreateXor(irb.CreateLoad(irb.getInt32Ty(), x),
                    irb.CreateShl(irb.CreateLoad(irb.getInt32Ty(), x), 13)),
      x);
  irb.CreateStore(
      irb.CreateXor(irb.CreateLoad(irb.getInt32Ty(), x),
                    irb.CreateLShr(irb.CreateLoad(irb.getInt32Ty(), x), 17)),
      x);
  irb.CreateStore(
      irb.CreateXor(irb.CreateLoad(irb.getInt32Ty(), x),
                    irb.CreateShl(irb.CreateLoad(irb.getInt32Ty(), x), 5)),
      x);
  Value *x_val = irb.CreateLoad(irb.getInt32Ty(), x);
  irb.CreateStore(x_val, arg_val);
  irb.CreateRet(irb.CreateTrunc(x_val, irb.getInt8Ty()));
  return cipher;
}
Value *LLVMVM::decodeBytecode(IRBuilder<> &irb, Value *buf, Value *op_arr,
                              Value *cipher_arg, bool shift, Type *val_type) {
  int bitsize = val_type->getIntegerBitWidth();
  assert(bitsize % 8 == 0);
  irb.CreateMemCpy(buf, (MaybeAlign)0, op_arr, (MaybeAlign)0, bitsize / 8);
  bool move_next = false;
  for (int i = 0; i < bitsize / 8; i++) {
    if (shift)
      irb.CreateCall(FunctionCallee(this->cipher), {cipher_arg});
    else {
      if (i >= 4 && !move_next) {
        irb.CreateCall(FunctionCallee(this->cipher), {cipher_arg});
        move_next = true;
      }
    }
    Value *key = irb.CreateLoad(irb.getInt32Ty(), cipher_arg);
    Value *ptr = irb.CreateGEP(getAllocateType(buf), buf,
                               {irb.getInt32(0), irb.getInt32(i)});
    irb.CreateStore(
        irb.CreateXor(
            irb.CreateTrunc(irb.CreateLShr(key, (i % 4) * 8), irb.getInt8Ty()),
            irb.CreateLoad(irb.getInt8Ty(), ptr)),
        ptr);
  }
  Value *decode_val = irb.CreateLoad(
      val_type, irb.CreateBitOrPointerCast(buf, op_arr->getType()));
  return decode_val;
}

void LLVMVM::buildVMFunction(Function &f, BasicBlock *op_entry, Function &vm,
                             std::vector<VMOpInfo *> &ops, int mem_size,
                             GlobalVariable *opcodes, int addr_stack_size,
                             std::vector<std::pair<int, int>> &remap,
                             std::map<Value *, int> &value_map,
                             std::map<BasicBlock *, int> &bb_key_map,
                             std::map<VMOpcodeInfo *, RandExpr *> &cipher_map) {

  BasicBlock *entry = BasicBlock::Create(vm.getContext(), "entry", &vm);
  // BasicBlock *loop_end = BasicBlock::Create(vm.getContext(), "loopend",
  // &vm);
  IRBuilder<> irb(entry);
  Value *pc = irb.CreateAlloca(irb.getInt32Ty());
  Value *memory = irb.CreateAlloca(ArrayType::get(irb.getInt8Ty(), mem_size));
  Value *addr_stack =
      irb.CreateAlloca(ArrayType::get(irb.getInt32Ty(), addr_stack_size));
  Value *ptr = irb.CreateAlloca(irb.getInt32Ty());
  Value *seed = irb.CreateAlloca(irb.getInt32Ty());
  Value *buf = irb.CreateAlloca(ArrayType::get(irb.getInt8Ty(), 8));
  // initial for locals
  printf("-  initial for keys %08X\n", bb_key_map[op_entry]);
  for (std::pair<int, int> p : remap) {
    int ptr_addr = p.first, real_addr = p.second;
    Value *pptr = irb.CreateGEP(getAllocateType(memory), memory,
                                {irb.getInt32(0), irb.getInt32(real_addr)});
    Value *to_store = irb.CreateGEP(getAllocateType(memory), memory,
                                    {irb.getInt32(0), irb.getInt32(ptr_addr)});
    irb.CreateStore(
        pptr, irb.CreateBitCast(
                  to_store, irb.getInt8Ty()->getPointerTo()->getPointerTo()));
  }
  irb.CreateStore(irb.getInt32(bb_key_map[op_entry]), seed);
  printf("-  initial for arguments\n");
  // initial for arguments
  Function::arg_iterator real_iter = vm.arg_begin();
  for (Function::arg_iterator iter = f.arg_begin(); iter != f.arg_end();
       iter++) {
    Value *arg = &*iter;
    Value *real_arg = &*real_iter;
    assert(value_map.count(arg) != 0);
    int addr = value_map[arg];
    Value *to_store = irb.CreateGEP(getAllocateType(memory), memory,
                                    {irb.getInt32(0), irb.getInt32(addr)});
    irb.CreateStore(
        real_arg,
        irb.CreateBitCast(to_store, real_arg->getType()->getPointerTo()));
    real_iter++;
  }
  printf("-  start building\n");
  irb.CreateStore(irb.getInt32(0), pc);
  irb.CreateStore(irb.getInt32(0), ptr);
  BasicBlock *dispatch_bb =
      BasicBlock::Create(vm.getContext(), "dispatch", &vm);
  irb.SetInsertPoint(dispatch_bb);
  Value *opvalue =
      irb.CreateGEP(getGlobalVariableType(opcodes), opcodes,
                    {irb.getInt32(0), irb.CreateLoad(irb.getInt32Ty(), pc)});
  printf("-  start decoding part\n");
  opvalue = decodeBytecode(irb, buf, opvalue, seed, true, irb.getInt8Ty());
  irb.CreateStore(
      irb.CreateAdd(irb.CreateLoad(irb.getInt32Ty(), pc), irb.getInt32(1)), pc);
  SwitchInst::Create(opvalue, dispatch_bb, 0, dispatch_bb);
  // dispatch_bb->moveBefore(loop_end);
  std::vector<PrefixTree *> allocated_node;
  std::map<PrefixTree *, BasicBlock *> node_to_block;
  PrefixTree *root = new PrefixTree();
  node_to_block[root] = dispatch_bb;
  allocated_node.push_back(root);
  for (VMOpInfo *op : ops) {
    PrefixTree *ptr = root;
    for (int i = 0; i < op->opcode.len - 1; i++) {
      unsigned char cur = op->opcode.code[i];
      if (ptr->sons.find(cur) == ptr->sons.end()) {

        BasicBlock *bb = BasicBlock::Create(vm.getContext(), "dispatch", &vm);
        irb.SetInsertPoint(bb);
        Value *opvalue = irb.CreateGEP(
            getGlobalVariableType(opcodes), opcodes,
            {irb.getInt32(0), irb.CreateLoad(irb.getInt32Ty(), pc)});
        opvalue =
            decodeBytecode(irb, buf, opvalue, seed, true, irb.getInt8Ty());
        irb.CreateStore(irb.CreateAdd(irb.CreateLoad(irb.getInt32Ty(), pc),
                                      irb.getInt32(1)),
                        pc);
        SwitchInst::Create(opvalue, dispatch_bb, 0, bb);
        // bb->moveBefore(loop_end);

        PrefixTree *node = new PrefixTree();
        allocated_node.push_back(node);
        node->val = cur;
        node_to_block[node] = bb;
        ptr->sons[cur] = node;
      }
      ptr = ptr->sons[cur];
    }
  }
  for (PrefixTree *node : allocated_node) {
    for (auto iter = node->sons.begin(); iter != node->sons.end(); iter++) {
      unsigned char cur = iter->first;
      PrefixTree *son = iter->second;
      SwitchInst *sw = (SwitchInst *)node_to_block[node]->getTerminator();
      sw->addCase(irb.getInt8(cur), node_to_block[son]);
    }
  }
  BranchInst::Create(dispatch_bb, entry);

  std::map<VMOpInfo *, BasicBlock *> handler_map;
  for (VMOpInfo *op : ops) {
    BasicBlock *handler;
    if (op->builtin_type) {
      if (op->builtin_type == PUSH_ADDR) {
        if (op->op_size == 1) {
          handler = BasicBlock::Create(vm.getContext(), "push_addr1", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *addr = irb.CreateGEP(getGlobalVariableType(opcodes), opcodes,
                                      {irb.getInt32(0), vpc});
          addr = decodeBytecode(irb, buf, addr, seed, false, irb.getInt8Ty());
          irb.CreateStore(irb.CreateZExt(addr, irb.getInt32Ty()),
                          irb.CreateGEP(getAllocateType(addr_stack), addr_stack,
                                        {irb.getInt32(0), vptr}));
          irb.CreateStore(irb.CreateAdd(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(1)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else if (op->op_size == 2) {
          handler = BasicBlock::Create(vm.getContext(), "push_addr2", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *addr =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt16Ty()->getPointerTo());
          addr = decodeBytecode(irb, buf, addr, seed, false, irb.getInt16Ty());

          irb.CreateStore(irb.CreateZExt(addr, irb.getInt32Ty()),
                          irb.CreateGEP(getAllocateType(addr_stack), addr_stack,
                                        {irb.getInt32(0), vptr}));
          irb.CreateStore(irb.CreateAdd(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(2)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else if (op->op_size == 4) {
          handler = BasicBlock::Create(vm.getContext(), "push_addr4", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *addr =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt32Ty()->getPointerTo());
          addr = decodeBytecode(irb, buf, addr, seed, false, irb.getInt32Ty());

          irb.CreateStore(addr,
                          irb.CreateGEP(getAllocateType(addr_stack), addr_stack,
                                        {irb.getInt32(0), vptr}));
          irb.CreateStore(irb.CreateAdd(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(4)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else
          assert(false && "Unknown builtin op type!");

      } else if (op->builtin_type == JUMP_TO) {
        handler = BasicBlock::Create(vm.getContext(), Twine("goto"), &vm);
        irb.SetInsertPoint(handler);
        Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
        Value *jmp_offset =
            irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                            opcodes, {irb.getInt32(0), vpc}),
                              irb.getInt32Ty()->getPointerTo());
        jmp_offset =
            decodeBytecode(irb, buf, jmp_offset, seed, false, irb.getInt32Ty());

        Value *next_key = irb.CreateBitCast(
            irb.CreateGEP(
                getGlobalVariableType(opcodes), opcodes,
                {irb.getInt32(0), irb.CreateAdd(vpc, irb.getInt32(4))}),
            irb.getInt32Ty()->getPointerTo());
        next_key =
            decodeBytecode(irb, buf, next_key, seed, false, irb.getInt32Ty());
        irb.CreateStore(next_key, seed);
        irb.CreateStore(irb.CreateAdd(vpc, jmp_offset), pc);
        BranchInst::Create(dispatch_bb, handler);
        // handler->moveBefore(loop_end);
        handler_map[op] = handler;

      } else if (op->builtin_type == STORE_IMM) {

        if (op->op_size == 1) {
          handler = BasicBlock::Create(vm.getContext(), "store_imm1", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *imm = irb.CreateGEP(getGlobalVariableType(opcodes), opcodes,
                                     {irb.getInt32(0), vpc});
          imm = decodeBytecode(irb, buf, imm, seed, false, irb.getInt8Ty());

          Value *addr = irb.CreateLoad(
              irb.getInt32Ty(),
              irb.CreateGEP(
                  getAllocateType(addr_stack), addr_stack,
                  {irb.getInt32(0), irb.CreateSub(vptr, irb.getInt32(1))}));

          irb.CreateStore(imm, irb.CreateGEP(getGlobalVariableType(opcodes),
                                             memory, {irb.getInt32(0), addr}));

          irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(1)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else if (op->op_size == 2) {
          handler = BasicBlock::Create(vm.getContext(), "store_imm2", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *imm =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt16Ty()->getPointerTo());
          imm = decodeBytecode(irb, buf, imm, seed, false, irb.getInt16Ty());

          Value *addr = irb.CreateLoad(
              irb.getInt32Ty(),
              irb.CreateGEP(
                  getAllocateType(addr_stack), addr_stack,
                  {irb.getInt32(0), irb.CreateSub(vptr, irb.getInt32(1))}));
          irb.CreateStore(
              imm,
              irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                              {irb.getInt32(0), addr}),
                                irb.getInt16Ty()->getPointerTo()));

          irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(2)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else if (op->op_size == 4) {
          handler = BasicBlock::Create(vm.getContext(), "store_imm4", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *imm =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt32Ty()->getPointerTo());
          imm = decodeBytecode(irb, buf, imm, seed, false, irb.getInt32Ty());

          Value *addr = irb.CreateLoad(
              irb.getInt32Ty(),
              irb.CreateGEP(
                  getAllocateType(addr_stack), addr_stack,
                  {irb.getInt32(0), irb.CreateSub(vptr, irb.getInt32(1))}));
          irb.CreateStore(
              imm,
              irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                              {irb.getInt32(0), addr}),
                                irb.getInt32Ty()->getPointerTo()));

          irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(4)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        } else {
          handler = BasicBlock::Create(vm.getContext(), "store_imm8", &vm);
          irb.SetInsertPoint(handler);
          Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
          Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
          Value *imm =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt64Ty()->getPointerTo());
          imm = decodeBytecode(irb, buf, imm, seed, false, irb.getInt64Ty());

          Value *addr = irb.CreateLoad(
              irb.getInt32Ty(),
              irb.CreateGEP(
                  getAllocateType(addr_stack), addr_stack,
                  {irb.getInt32(0), irb.CreateSub(vptr, irb.getInt32(1))}));
          irb.CreateStore(
              imm,
              irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                              {irb.getInt32(0), addr}),
                                irb.getInt64Ty()->getPointerTo()));
          irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(1)), ptr);
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(8)), pc);
          BranchInst::Create(dispatch_bb, handler);
          // handler->moveBefore(loop_end);
          handler_map[op] = handler;
        }
      } else if (op->builtin_type == BRANCH) {

        handler = BasicBlock::Create(vm.getContext(), Twine("branch"), &vm);
        irb.SetInsertPoint(handler);
        Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
        Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
        Value *cond_addr = irb.CreateLoad(
            irb.getInt32Ty(),
            irb.CreateGEP(
                getAllocateType(addr_stack), addr_stack,
                {irb.getInt32(0), irb.CreateSub(vptr, irb.getInt32(1))}));
        Value *cond = irb.CreateLoad(
            irb.getInt1Ty(),
            irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                            {irb.getInt32(0), cond_addr}),
                              irb.getInt1Ty()->getPointerTo()));
        Value *jmp_offset =
            irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                            opcodes, {irb.getInt32(0), vpc}),
                              irb.getInt32Ty()->getPointerTo());
        jmp_offset =
            decodeBytecode(irb, buf, jmp_offset, seed, false, irb.getInt32Ty());

        Value *next_key = irb.CreateBitCast(
            irb.CreateGEP(
                getGlobalVariableType(opcodes), opcodes,
                {irb.getInt32(0), irb.CreateAdd(vpc, irb.getInt32(4))}),
            irb.getInt32Ty()->getPointerTo());
        next_key =
            decodeBytecode(irb, buf, next_key, seed, false, irb.getInt32Ty());
        Value *key = irb.CreateSelect(cond, next_key,
                                      irb.CreateLoad(irb.getInt32Ty(), seed));
        irb.CreateStore(key, seed);
        Value *final_offset =
            irb.CreateSelect(cond, jmp_offset, irb.getInt32(8));
        irb.CreateStore(irb.CreateAdd(vpc, final_offset), pc);
        irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(1)), ptr);

        BranchInst::Create(dispatch_bb, handler);
        // handler->moveBefore(loop_end);
        handler_map[op] = handler;

      } else
        assert(false && "Unknown builtin op type!");
    } else {
      handler = BasicBlock::Create(
          vm.getContext(), Twine("handler_") + op->instr->getOpcodeName(), &vm);
      irb.SetInsertPoint(handler);
      Value *vpc = irb.CreateLoad(irb.getInt32Ty(), pc);
      Value *vptr = irb.CreateLoad(irb.getInt32Ty(), ptr);
      Instruction *target = op->instr->clone();
      Value *pos = vptr;
      int arg_num = op->opnds.size();
      for (int i = 0; i < arg_num; i++) {
        std::pair<int, Value *> p = op->opnds[i];
        Value *arg_addr = irb.CreateLoad(
            irb.getInt32Ty(),
            irb.CreateGEP(getAllocateType(addr_stack), addr_stack,
                          {irb.getInt32(0),
                           irb.CreateSub(vptr, irb.getInt32(arg_num - i))}));
        Value *arg = irb.CreateLoad(
            p.second->getType(),
            irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                            {irb.getInt32(0), arg_addr}),
                              p.second->getType()->getPointerTo()));
        target->setOperand(p.first, arg);
        pos = arg;
      }
      target->insertAfter((Instruction *)pos);
      if (isa<ReturnInst>(*target)) {
        // handler->moveBefore(loop_end);
        handler_map[op] = handler;
      } else {
        if (!target->getType()->isVoidTy()) {
          Value *to_store =
              irb.CreateBitCast(irb.CreateGEP(getGlobalVariableType(opcodes),
                                              opcodes, {irb.getInt32(0), vpc}),
                                irb.getInt32Ty()->getPointerTo());
          to_store =
              decodeBytecode(irb, buf, to_store, seed, false, irb.getInt32Ty());
          irb.CreateStore(
              target,
              irb.CreateBitCast(irb.CreateGEP(getAllocateType(memory), memory,
                                              {irb.getInt32(0), to_store}),
                                target->getType()->getPointerTo()));
          irb.CreateStore(irb.CreateAdd(vpc, irb.getInt32(4)), pc);
        }
        assert(handler != nullptr);
        irb.CreateStore(irb.CreateSub(vptr, irb.getInt32(arg_num)), ptr);
        BranchInst::Create(dispatch_bb, handler);
        // handler->moveBefore(loop_end);
        handler_map[op] = handler;
      }
    }
    RandExpr *expr = cipher_map[&op->opcode];
    irb.SetInsertPoint(&*handler->getFirstInsertionPt());
    Value *old_seed = irb.CreateLoad(irb.getInt32Ty(), seed);
    Value *new_seed = randExpr2Ir(irb, old_seed, expr);
    irb.CreateStore(irb.CreateXor(old_seed, new_seed), seed);
  }
  for (VMOpInfo *op : ops) {
    PrefixTree *ptr = root;
    for (int i = 0; i < op->opcode.len - 1; i++) {
      unsigned char cur = op->opcode.code[i];
      assert(ptr->sons.find(cur) != ptr->sons.end());
      ptr = ptr->sons[cur];
    }
    SwitchInst *sw = (SwitchInst *)node_to_block[ptr]->getTerminator();
    sw->addCase(irb.getInt8(op->opcode.code[op->opcode.len - 1]),
                handler_map[op]);
  }
  std::vector<BasicBlock *> bbs;
  for (auto iter = node_to_block.begin(); iter != node_to_block.end(); iter++) {
    bbs.push_back(iter->second);
  }
  for (auto iter = handler_map.begin(); iter != handler_map.end(); iter++) {
    bbs.push_back(iter->second);
  }
  for (auto iter = node_to_block.begin(); iter != node_to_block.end(); iter++) {
    BasicBlock *bb = iter->second;
    SwitchInst *sw = (SwitchInst *)bb->getTerminator();
    std::set<int> used_val;
    for (auto iter0 = sw->case_begin(); iter0 != sw->case_end(); iter0++) {
      used_val.insert(iter0->getCaseValue()->getZExtValue());
    }
    if (sw->getNumCases() < 100) {
      int turn = rand() % 20, ptr = 0;
      while (ptr < turn) {
        int n = getRand(256, used_val);
        used_val.insert(n);
        sw->addCase(irb.getInt8(n), bbs.at(rand() % bbs.size()));
        ptr++;
      }
    }
  }
  // BranchInst::Create(dispatch_bb, loop_end);
  for (PrefixTree *node : allocated_node)
    delete node;
}
bool cmp(std::pair<Instruction *, int> &a, std::pair<Instruction *, int> &b) {
  return a.second < b.second;
}
int LLVMVM::allocaMemory(BasicBlock &bb,
                         std::map<Instruction *, int> &alloca_map,
                         int mem_base) {
  int max_space = 0;
  DataLayout data = bb.getParent()->getParent()->getDataLayout();
  std::map<Instruction *, std::set<Instruction *> *> alive;
  for (Instruction &i : bb) {
    if (alive.count(&i) == 0) {
      std::set<Instruction *> *instr_set = new std::set<Instruction *>;
      alive[&i] = instr_set;
    }
  }
  for (Instruction &i : bb) {
    if (i.isUsedOutsideOfBlock(&bb))
      assert(false && "Impossible: value escaped");
    for (Value *opnd : i.operands()) {
      if (isa<Instruction>(*opnd) && !isa<AllocaInst>(*opnd)) {
        Instruction *instr = (Instruction *)opnd;
        if (instr->getParent() != &bb)
          assert(false && "Impossible: value escaped");
        BasicBlock::iterator start = instr->getIterator(),
                             end = i.getIterator();
        ++end;
        for (BasicBlock::iterator iter = ++start; iter != end; iter++) {
          Instruction *ii = &*iter;
          alive[ii]->insert(instr);
        }
      }
    }
  }
  /*for(Instruction &i:bb)
  {
      printf("current opname: %s\n\t",i.getOpcodeName());
      if(alive[&i]->size()==0)
          printf("null");
      for(std::set<Instruction*>::iterator
  iter=alive[&i]->begin();iter!=alive[&i]->end();iter++) printf("%s
  ",(*iter)->getOpcodeName()); printf("\n");
  }*/
  // printf("value remain!\n");
  std::vector<std::pair<Instruction *, int>> current_alloc;
  for (Instruction &i : bb) {
    std::vector<std::pair<Instruction *, int>> freed;
    for (std::vector<std::pair<Instruction *, int>>::iterator iter =
             current_alloc.begin();
         iter != current_alloc.end(); iter++) {
      std::pair<Instruction *, int> p = *iter;
      bool find = false;
      for (std::set<Instruction *>::iterator iter = alive[&i]->begin();
           iter != alive[&i]->end(); iter++) {
        if (p.first == *iter) {
          find = true;
          break;
        }
      }
      if (!find) {
        // printf("    free value opcode:
        // %s\n",p.first->getOpcodeName());
        freed.push_back(p);
      }
    }
    for (std::pair<Instruction *, int> pp : freed) {
      for (std::vector<std::pair<Instruction *, int>>::iterator iter =
               current_alloc.begin();
           iter != current_alloc.end(); iter++) {
        std::pair<Instruction *, int> p = *iter;
        if (p == pp) {
          current_alloc.erase(iter);
          break;
        }
      }
    }

    // printf("2 --------- %s\n",i.getOpcodeName());
    // printf("    allocated value num: %d\n",current_alloc.size());
    sort(current_alloc, cmp);
    for (std::vector<std::pair<Instruction *, int>>::iterator iter =
             current_alloc.begin();
         iter != current_alloc.end(); iter++) {
      std::pair<Instruction *, int> p = *iter;
      // printf("    > value %s at addr
      // %d\n",p.first->getOpcodeName(),p.second+mem_base);
    }
    // printf("free ok %d!\n",freed.size());
    if (!i.getType()->isVoidTy()) {
      // printf("    this instruction need space
      // %d\n",data.getTypeAllocSize(i.getType()));
      std::vector<std::pair<Instruction *, int>>::iterator ptr = current_alloc
                                                                     .begin(),
                                                           prev;
      while (ptr != current_alloc.end()) {
        int space, addr;
        std::pair<Instruction *, int> cur = *ptr;
        if (ptr != current_alloc.begin()) {
          addr = prev->second + data.getTypeAllocSize(prev->first->getType());
          space = cur.second - addr;
        } else {
          addr = 0;
          space = cur.second;
        }
        if (space >= data.getTypeAllocSize(i.getType())) {
          // printf("    find free space\n");
          current_alloc.insert(ptr, std::make_pair(&i, addr));
          alloca_map[&i] = addr + mem_base;
          break;
        }
        prev = ptr;
        ptr++;
      }
      if (ptr == current_alloc.end()) {
        // printf("    no free space,alloca new space\n");
        int addr;
        if (current_alloc.size() != 0)
          addr = prev->second + data.getTypeAllocSize(prev->first->getType());
        else
          addr = 0;
        int bound = addr + data.getTypeAllocSize(i.getType());
        max_space = max_space > bound ? max_space : bound;
        current_alloc.push_back(std::make_pair(&i, addr));
        alloca_map[&i] = addr + mem_base;
      }
    }
    // if(alloca_map.count(&i)>0)
    // printf("    [~] value addr: %d\n",alloca_map[&i]);
  }
  // printf("-----after alloca max_space %d\n",max_space+mem_base);
  for (Instruction &i : bb)
    delete alive[&i];
  return max_space + mem_base;
}
unsigned int xorshift(unsigned int *state) {
  unsigned int x = *state;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  return *state = x;
}
void pushBytes(unsigned int *state, unsigned char *ptr, int size,
               std::vector<unsigned char> &buffer) {
  bool move_next = false;
  for (int i = 0; i < size; i++) {
    if (i >= 4 && !move_next) {
      xorshift(state);
      move_next = true;
    }
    unsigned int k = *state;
    unsigned char v = ptr[i] ^ (k >> ((i % 4) * 8));
    buffer.push_back(v);
  }
}

void pushOpcode(unsigned int *state, VMOpcodeInfo *op,
                std::vector<unsigned char> &buffer) {
  assert(op->len <= 4);
  for (int i = 0; i < op->len; i++) {
    xorshift(state);
    unsigned char v = op->code[i] ^ (*state);
    buffer.push_back(v);
  }
}
int queryAddr(Value *v, std::map<Value *, int> &locals_addr_map,
              std::map<Instruction *, int> &reg_addr_map) {
  int addr;
  if (locals_addr_map.count(v) != 0)
    return locals_addr_map[v];
  else if (reg_addr_map.count((Instruction *)v) != 0)
    return reg_addr_map[(Instruction *)v];
  else
    assert(false && "Unknown value!");
}
VMOpcodeInfo *findStoreImmOp(std::vector<VMOpInfo *> &ops, int store_size) {
  for (VMOpInfo *op : ops) {
    if (op->builtin_type == STORE_IMM && op->op_size == store_size)
      return &op->opcode;
  }
  assert(false);
}
VMOpcodeInfo *findPushAddrOp(std::vector<VMOpInfo *> &ops, int push_size) {
  for (VMOpInfo *op : ops) {
    if (op->builtin_type == PUSH_ADDR && op->op_size == push_size)
      return &op->opcode;
  }
  assert(false);
}
VMOpcodeInfo *findBranchOp(std::vector<VMOpInfo *> &ops) {
  for (VMOpInfo *op : ops) {
    if (op->builtin_type == BRANCH)
      return &op->opcode;
  }
  assert(false);
}
VMOpcodeInfo *findJumpOp(std::vector<VMOpInfo *> &ops) {
  for (VMOpInfo *op : ops) {
    if (op->builtin_type == JUMP_TO)
      return &op->opcode;
  }
  assert(false);
}
int getAddressOpSize(int addr) {
  assert(addr >= 0);
  unsigned int v = addr;
  if (v & 0xffff0000)
    return 4;
  else if (v & 0xff00)
    return 2;
  else
    return 1;
}
unsigned int LLVMVM::evalRandExpr(RandExpr *tree, unsigned int v) {
  assert(tree != nullptr);
  if (tree->op == VAR) {
    return v;
  } else if (tree->op == CONST) {
    return tree->data;
  } else if (tree->op == SHL) {
    return evalRandExpr(tree->l, v) << evalRandExpr(tree->r, v);
  } else if (tree->op == SHR) {
    return evalRandExpr(tree->l, v) >> evalRandExpr(tree->r, v);
  } else if (tree->op == XOR) {
    return evalRandExpr(tree->l, v) ^ evalRandExpr(tree->r, v);
  } else if (tree->op == OR) {
    return evalRandExpr(tree->l, v) | evalRandExpr(tree->r, v);
  } else if (tree->op == ADD) {
    return evalRandExpr(tree->l, v) + evalRandExpr(tree->r, v);
  }
}
int LLVMVM::generateBytecodes(
    BasicBlock *entry_block, std::vector<BasicBlock *> &code,
    std::map<Value *, int> &locals_addr_map,
    std::map<Instruction *, VMOpInfo *> &instr_map,
    std::vector<VMOpInfo *> &ops, int mem_size,
    std::vector<Constant *> &opcodes, std::map<BasicBlock *, int> &bb_key_map,
    std::map<VMOpcodeInfo *, RandExpr *> &cipher_map) {
  if (code.size() == 0)
    return mem_size;
  std::vector<unsigned char> opcodes_raw;
  int new_mem_size = mem_size;
  unsigned int state = 0;
  LLVMContext *context = &code[0]->getContext();
  std::vector<std::pair<int, BasicBlock *>> br_to_fix;
  std::map<BasicBlock *, int> block_addr;
  std::map<int, VMOpcodeInfo *> store_ops;
  int size[] = {1, 2, 4, 8};
  for (int i = 0; i < 4; i++)
    store_ops[size[i]] = findStoreImmOp(ops, size[i]);

  std::map<int, VMOpcodeInfo *> push_addr_ops;
  for (int i = 0; i < 3; i++)
    push_addr_ops[size[i]] = findPushAddrOp(ops, size[i]);

  VMOpcodeInfo *br_op = findBranchOp(ops);
  VMOpcodeInfo *jump_op = findJumpOp(ops);
  printf("all VMOpcodeInfo ready, start generating....\n");
  std::map<BasicBlock *, int> key_map;
  // for (auto iter = instr_map.begin(); iter != instr_map.end(); iter++)
  //   iter->first->dump();

  for (int i = 0; i < code.size(); i++) {

    BasicBlock *bb = code[i];
    state = bb_key_map[bb];
    DataLayout data = bb->getParent()->getParent()->getDataLayout();
    int cur_addr = opcodes_raw.size();
    block_addr[bb] = cur_addr;
    std::map<Instruction *, int> reg_addr_map;
    int allocated_space = allocaMemory(*bb, reg_addr_map, mem_size);
    int max_used_space = allocated_space;
    printf("block key: %08X\n", state);
    for (Instruction &instr : *bb) {
      instr.print(llvm::errs());
      assert(instr_map.find(&instr) != instr_map.end());
      VMOpInfo *op = instr_map[&instr];
      int used_space = allocated_space;
      int empty = 0;
      if (isa<BranchInst>(instr)) {
        BranchInst *br = (BranchInst *)&instr;
        if (br->isConditional()) {
          Value *cond = br->getCondition();
          assert(cond->getType() == Type::getInt1Ty(*context));
          int addr = queryAddr(cond, locals_addr_map, reg_addr_map);
          int addr_len = 0;
          // push addr
          printf("%-6d", opcodes_raw.size());
          addr_len = getAddressOpSize(addr);
          pushOpcode(&state, push_addr_ops[addr_len], opcodes_raw);
          state ^= evalRandExpr(cipher_map[push_addr_ops[addr_len]], state);
          pushBytes(&state, (unsigned char *)&addr, addr_len, opcodes_raw);
          printf("push addr%d=[%d]\n", addr_len, addr);

          // br offset
          printf("%-6d", opcodes_raw.size());
          br_to_fix.push_back(std::make_pair(opcodes_raw.size() + br_op->len,
                                             br->getSuccessor(0)));
          pushOpcode(&state, br_op, opcodes_raw);
          state ^= evalRandExpr(cipher_map[br_op], state);
          pushBytes(&state, (unsigned char *)&empty, 4, opcodes_raw);
          int key = bb_key_map[br->getSuccessor(0)];
          pushBytes(&state, (unsigned char *)&key, 4, opcodes_raw);
          printf("branch offset=%d key=%08X\n", empty, key);

          /*if (i == code.size() - 1 ||
              code[i + 1] != br->getSuccessor(1)) {*/

          // goto offset
          printf("%-6d", opcodes_raw.size());
          br_to_fix.push_back(std::make_pair(opcodes_raw.size() + jump_op->len,
                                             br->getSuccessor(1)));
          pushOpcode(&state, jump_op, opcodes_raw);
          state ^= evalRandExpr(cipher_map[jump_op], state);
          pushBytes(&state, (unsigned char *)&empty, 4, opcodes_raw);
          key = bb_key_map[br->getSuccessor(1)];
          pushBytes(&state, (unsigned char *)&key, 4, opcodes_raw);
          printf("goto offset=%d key=%08X\n", empty, key);
          //}
        } else {
          /*if (i == code.size() - 1||
              code[i + 1] != br->getSuccessor(0)) {*/
          // goto offset
          printf("%-6d", opcodes_raw.size());
          br_to_fix.push_back(std::make_pair(opcodes_raw.size() + jump_op->len,
                                             br->getSuccessor(0)));
          pushOpcode(&state, jump_op, opcodes_raw);
          state ^= evalRandExpr(cipher_map[jump_op], state);
          pushBytes(&state, (unsigned char *)&empty, 4, opcodes_raw);
          int key = bb_key_map[br->getSuccessor(0)];
          pushBytes(&state, (unsigned char *)&key, 4, opcodes_raw);
          printf("goto offset=%d key=%08X\n", empty, key);
          //}
        }
      } else {
        VMOpInfo *vmop = instr_map[&instr];
        for (std::pair<int, Value *> p : vmop->opnds) {
          Value *op = instr.getOperand(p.first);
          if (isa<ConstantInt>(*op) /* || isa<ConstantFP>(op)*/) {
            ConstantInt *val = (ConstantInt *)op;
            int store_size = data.getTypeAllocSize(val->getType());
            int addr_len = 0;
            addr_len = getAddressOpSize(used_space);
            printf("%-6d", opcodes_raw.size());
            pushOpcode(&state, push_addr_ops[addr_len], opcodes_raw);
            state ^= evalRandExpr(cipher_map[push_addr_ops[addr_len]], state);
            pushBytes(&state, (unsigned char *)&used_space, addr_len,
                      opcodes_raw);
            printf("push addr%d=[%d]\n", addr_len, used_space);

            // store value
            printf("%-6d", opcodes_raw.size());
            pushOpcode(&state, store_ops[store_size], opcodes_raw);
            state ^= evalRandExpr(cipher_map[store_ops[store_size]], state);

            unsigned long long r = val->getZExtValue();
            pushBytes(&state, (unsigned char *)&r, store_size, opcodes_raw);
            printf("store imm%d=%d\n", store_size, r);

            // push addr
            addr_len = getAddressOpSize(used_space);
            printf("%-6d", opcodes_raw.size());
            pushOpcode(&state, push_addr_ops[addr_len], opcodes_raw);
            state ^= evalRandExpr(cipher_map[push_addr_ops[addr_len]], state);

            pushBytes(&state, (unsigned char *)&used_space, addr_len,
                      opcodes_raw);
            printf("push addr%d=[%d]\n", addr_len, used_space);
            used_space += store_size;
          } else {
            int addr = queryAddr(op, locals_addr_map, reg_addr_map);
            int addr_len = 0;
            // push addr
            addr_len = getAddressOpSize(addr);
            printf("%-6d", opcodes_raw.size());
            pushOpcode(&state, push_addr_ops[addr_len], opcodes_raw);
            state ^= evalRandExpr(cipher_map[push_addr_ops[addr_len]], state);
            pushBytes(&state, (unsigned char *)&addr, addr_len, opcodes_raw);
            printf("push addr%d=[%d]\n", addr_len, addr);
          }
        }

        if (!instr.getType()->isVoidTy()) {
          // handler addr

          int addr = queryAddr(&instr, locals_addr_map, reg_addr_map);
          printf("%-6d", opcodes_raw.size());
          pushOpcode(&state, &vmop->opcode, opcodes_raw);
          state ^= evalRandExpr(cipher_map[&vmop->opcode], state);
          pushBytes(&state, (unsigned char *)&addr, 4, opcodes_raw);
          printf("handler_%d st=[%d] name=%s\n", vmop->opcode, addr,
                 vmop->instr->getOpcodeName());
        } else {
          // handler
          printf("%-6d", opcodes_raw.size());
          pushOpcode(&state, &vmop->opcode, opcodes_raw);
          state ^= evalRandExpr(cipher_map[&vmop->opcode], state);
          printf("handler_%d name=%s\n", vmop->opcode,
                 vmop->instr->getOpcodeName());
        }
      }
      max_used_space =
          max_used_space > used_space ? max_used_space : used_space;
      printf("\n");
    }
    printf("   block max used space: %d\n\n", max_used_space);
    new_mem_size =
        new_mem_size > max_used_space ? new_mem_size : max_used_space;
  }
  for (std::pair<int, BasicBlock *> p : br_to_fix) {

    int pos = p.first;
    BasicBlock *target = p.second;
    assert(block_addr.count(target) != 0);
    int delta = block_addr[target] - pos;
    unsigned char *ptr = (unsigned char *)&delta;
    for (int i = 0; i < 4; i++)
      opcodes_raw[pos + i] ^= ptr[i];
  }
  for (unsigned char op : opcodes_raw)
    opcodes.push_back(ConstantInt::get(Type::getInt8Ty(*context), op));
  return new_mem_size;
}
void LLVMVM::fixCallInst(Function *target, Function *orig) {
  orig->replaceAllUsesWith(target);
  orig->dropAllReferences();
  BasicBlock *dummy = BasicBlock::Create(orig->getContext(), "dummy", orig);
  IRBuilder<> irb(dummy);
  std::vector<Value *> args;
  for (Function::arg_iterator iter = orig->arg_begin(); iter != orig->arg_end();
       iter++)
    args.push_back(&*iter);
  Value *call = irb.CreateCall(FunctionCallee(target), args);
  if (target->getReturnType()->isVoidTy())
    irb.CreateRetVoid();
  else
    irb.CreateRet(call);

  /*for(Function &func:*target->getParent())
      for(BasicBlock &bb:func)
          for(Instruction &ii:bb)
          {
              if(isa<CallInst>(ii))
              {
                  CallInst* callInst=&cast<CallInst>(ii);
                  if(callInst->getCalledFunction()==orig)
                      callInst->setCalledFunction(FunctionCallee(target));
              }
          }
  */
}
void LLVMVM::allocateOpcodeKey(Function &f,
                               std::map<BasicBlock *, int> &bb_map) {
  for (BasicBlock &bb : f)
    bb_map[&bb] = (rand() << 16) | (rand() & 0xffff);
}
Function *LLVMVM::virtualization(Function &f) {
  printf("\nFunction Name: %s\n", f.getName());
  if (!check(f))
    return NULL;
  printf("[1] start demote registers!\n");
  demoteRegisters(&f);
  std::map<Value *, int> alloca_map;
  std::vector<std::pair<int, int>> remap;
  int mem_size = 0, cur_op = 1;
  printf("[2] start alloca vm memory for arguments!\n");
  DataLayout data = f.getParent()->getDataLayout();
  for (Function::arg_iterator iter = f.arg_begin(); iter != f.arg_end();
       iter++) {
    Value *arg = &*iter;
    alloca_map[arg] = mem_size;
    mem_size += data.getTypeAllocSize(arg->getType());
  }
  printf("    ----arguments space %d\n", mem_size);
  printf("[3] start alloca vm memory for locals!\n");
  BasicBlock *locals_block = handleAlloca(f, alloca_map, remap, mem_size);
  printf("    ----current allocated space %d\n", mem_size);
  std::vector<BasicBlock *> code_blocks;
  printf("[4] create mapping from instruction to opcode\n");
  std::map<Instruction *, VMOpInfo *> instr_map;
  std::vector<VMOpInfo *> ops;
  BasicBlock *op_entry = &f.getEntryBlock();
  createBuiltinOps(ops);
  printf("called [createBuiltinOps]\n");
  for (BasicBlock &bb : f) {
    if (&bb == &*locals_block) {
      assert(bb.getTerminator()->getNumSuccessors() == 1);
      op_entry = bb.getTerminator()->getSuccessor(0);
      continue;
    }
    code_blocks.push_back(&bb);
    for (Instruction &i : bb) {
      if (isa<BranchInst>(i)) {
        for (VMOpInfo *o : ops) {
          if (o->builtin_type == BRANCH) {
            instr_map[&i] = o;
            break;
          }
        }
      } else {
        VMOpInfo *op = getOrCreateRawOp(i, ops);
        instr_map[&i] = op;
      }
    }
  }

  printf("   -current number of raw op handlers: %d\n", ops.size());
  for (VMOpInfo *o : ops) {
    if (!o->builtin_type) {
      printf("    -- %s\n", o->instr->getOpcodeName());
      o->instr->print(llvm::errs());
    }
  }
  allocateOpcode(ops);
  std::map<VMOpcodeInfo *, RandExpr *> cipher_map;
  for (VMOpInfo *o : ops) {
    cipher_map[&o->opcode] = generateRandExpr(2);
  }

  printf("[5] building vistualization function\n");
  std::map<BasicBlock *, int> bb_key_map;

  allocateOpcodeKey(f, bb_key_map);
  printf("   -called [allocateOpcodeKey]\n");
  std::vector<Constant *> opcodes;

  int new_mem_size =
      generateBytecodes(op_entry, code_blocks, alloca_map, instr_map, ops,
                        mem_size, opcodes, bb_key_map, cipher_map);
  printf("   -called [generateOpcodes]\n");
  ArrayType *AT =
      ArrayType::get(Type::getInt8Ty(f.getContext()), opcodes.size());
  Constant *opcode_array =
      ConstantArray::get(AT, ArrayRef<Constant *>(opcodes));
  GlobalVariable *oparr_var = new GlobalVariable(
      *(f.getParent()), AT, false, GlobalValue::LinkageTypes::PrivateLinkage,
      opcode_array, "opcodes");
  Function *vm_func =
      Function::Create(f.getFunctionType(), f.getLinkage(),
                       f.getName() + Twine("_VM"), f.getParent());
  buildVMFunction(f, op_entry, *vm_func, ops, new_mem_size, oparr_var, 256,
                  remap, alloca_map, bb_key_map, cipher_map);
  printf("   -called [buildVMFunction]\n");
  for (VMOpInfo *o : ops) {
    destoryRandExpr(cipher_map[&o->opcode]);
  }
  return vm_func;
}

PreservedAnalyses LLVMVM::run(Module &M, ModuleAnalysisManager &AM) {
  srand(time(0));
  printf("start vmp pass!\n");
  this->cipher = buildCipher(&M);
  std::vector<Function *> removed;
  for (Function &f : M) {
    llvm::errs() << f.getName();
    if (&f == this->cipher) {
      continue;
    }
    bool is_vm = false;
    for (Function *ff : vm_funcs) {
      if (&f == ff) {
        is_vm = true;
        break;
      }
    }
    if (!is_vm && f.hasExactDefinition() &&
        readAnnotate(f).find("virtualization") != std::string::npos) {
      FunctionAnalysisManager &FAM =
          AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
      LowerSwitchPass lower;
      lower.run(f, FAM);
      Function *vmfunc = virtualization(f);
      if (vmfunc != NULL) {
        vm_funcs.push_back(vmfunc);
        fixCallInst(vmfunc, &f);
      }
    }
  }
  return PreservedAnalyses::none();
}
} // namespace polaris