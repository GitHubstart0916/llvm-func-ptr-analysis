//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>


#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include "Liveness.h"
#include <string.h>
using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}

//    std::set<std::string> values;
    bool to_log = false;
    std::set<Function*> *funcs = new std::set<Function*>;

    std::map<int, std::set<Function*>*> *func_maps = new std::map<int, std::set<Function*>*>;
    std::set<Value*> *c_know = new std::set<Value*>;
    std::set<Instruction*> *alias_inst = new std::set<Instruction*>;

    //CFG
    std::map<Function*, std::set<BasicBlock*>*> *bbs_map = new std::map<Function*, std::set<BasicBlock*>*>;
    std::map<BasicBlock*, std::set<BasicBlock*>*> *dm_map = new std::map<BasicBlock*, std::set<BasicBlock*>*>;
    std::map<BasicBlock*, std::set<BasicBlock*>*> *idm_map = new std::map<BasicBlock*, std::set<BasicBlock*>*>;
    std::map<BasicBlock*, std::set<BasicBlock*>*> *df_map = new std::map<BasicBlock*, std::set<BasicBlock*>*>;
    std::map<Value*, std::set<BasicBlock*>*> *f_map = new std::map<Value*, std::set<BasicBlock*>*>;
    std::map<Value*, std::set<BasicBlock*>*> *w_map = new std::map<Value*, std::set<BasicBlock*>*>;
    std::map<Value*, std::set<Instruction*>*> *def_insts_map = new std::map<Value*, std::set<Instruction*>*>;
    std::map<Value*, std::set<Instruction*>*> *use_insts_map = new std::map<Value*, std::set<Instruction*>*>;
//    std::map<Instruction*, std::set<BasicBlock*>*> *w_map = new std::map<Instruction*, std::set<BasicBlock*>*>;
    std::map<Value*, std::map<Value*, int>*> *def_pos_map = new std::map<Value*, std::map<Value*, int>*>; // only for func
    std::map<Value*, int>* def_pos;

//

    std::set<std::set<Value*>*> alias_ptr;
    //mem_analysis
    std::map<Instruction*, Value*> ld2alloc;
    std::set<BasicBlock*> def_bbs, use_bbs, *F, *W;
    std::set<Instruction*> *def_insts, *use_insts;
    //for bb in F,i.e. those basic block need to insert phi, bb_phis[bb] is the value set of mem_phi, like array ssa
    std::map<Value*, std::map<BasicBlock*, std::set<Value*>*>*> bb_mem_phi_value;
    std::map<Value*, std::map<Instruction*, Value*>*> reach_def; // maybe: function phi(bb) calledValue
    std::stack<Value*> S;
//    std::map<Instruction*, std::set<BasicBlock*>*> use_bbs;
    //todo: maybe has bug -- need test
    Value* n_alloc = nullptr;
    Instruction* n_pos = nullptr;
    Value* reach_v = nullptr;

    void add_to_alias(Value *A, Value *B) {
        for (auto *alias_set: alias_ptr) {
            if (alias_set->find(A) != alias_set->end()) {
                alias_set->insert(B);
                return;
            }
            if (alias_set->find(B) != alias_set->end()) {
                alias_set->insert(A);
                return;
            }
        }
        auto *ins = new std::set<Value*>;
        ins->insert(A), ins->insert(B);
        alias_ptr.insert(ins);
    }

    void add_to_bb_mem_phi_value(Value* instr, BasicBlock* k, Value* v) {
        if (bb_mem_phi_value.find(instr) == bb_mem_phi_value.end()) {
            bb_mem_phi_value[instr] = new std::map<BasicBlock*, std::set<Value*>*>;
        }
        if (bb_mem_phi_value[instr]->find(k) == bb_mem_phi_value[instr]->end()) {
            (*bb_mem_phi_value[instr])[k] = (new std::set<Value*>);
        }
        (*bb_mem_phi_value[instr])[k]->insert(v);
    }

    void add_func(int index, std::map<int, std::set<Function*>*> *p_map, Function* func) {
        if ((*p_map)[index] == nullptr) {
            (*p_map)[index] = new std::set<Function*>;
        }
        (*p_map)[index]->insert(func);
    }

    bool is_alloc_or_malloc(Value* v) {
        if (auto *t = dyn_cast<AllocaInst>(v)) {
            return true;
        } else if (auto *t = dyn_cast<CallBase>(v)) {
            return t->getCalledValue()->getName() == "malloc";
        }
        return false;
    }

    void get_values(Value* v, std::set<Function*>* p_set, BasicBlock *bb, int index, std::map<int, std::set<Function*>*> *p_map, std::set<Value*>* know) {
        if (know->find(v) != know->end()) return;
        know->insert(v);
        if (v == nullptr) return;
        if (auto *cast = dyn_cast<BitCastInst>(v)) {
            n_alloc = cast->getOperand(0);
            outs() << *n_alloc << " " << *n_pos << "\n";
            Value* v = nullptr;
            if (n_pos->getParent()->getParent() != cast->getParent()->getParent()) {
                if (auto *arg = dyn_cast<Argument>(n_alloc)) {
                    get_values(arg, p_set, bb, index, p_map, know);
                }
                 else v = get_reach_def(n_alloc, cast->getParent()->getParent()->getEntryBlock().getTerminator());
            } else {
                v = get_reach_def(n_alloc, n_pos);
            }

            get_values(v, p_set, bb, index, p_map, know);
        } else if (auto *gep = dyn_cast<GetElementPtrInst>(v)) {
            Value* p_base = gep->getPointerOperand();
            get_values(p_base, p_set, bb, index, p_map, know);
        } else if (auto *alloc = dyn_cast<AllocaInst>(v)) {
            n_alloc = alloc;
            Value* v = get_reach_def(n_alloc, n_pos);
            outs() << *n_alloc << " reach pos: " << *n_pos << " value is: " << *v << "\n";
            get_values(v, p_set, bb, index, p_map, know);
        } else if (auto *b_v = dyn_cast<BasicBlock>(v)) {
            for (Value* nxt: *(*bb_mem_phi_value[n_alloc])[b_v]) {
                get_values(nxt, p_set, bb, index, p_map, know);
            }
        } else if (auto *ld = dyn_cast<LoadInst>(v)) {
            n_alloc = ld2alloc[ld];
            if (n_alloc == nullptr) {
                Value* p = ld->getPointerOperand();
                if (auto *gep = dyn_cast<GetElementPtrInst>(p)) {
                    Value* p_base = gep->getPointerOperand();
//                    outs() << *p_base << "\n";
                    get_values(p_base, p_set, bb, index, p_map, know);
                }
            } else if (auto *para = dyn_cast<Argument>(n_alloc)) {

                Value* v = get_param_reach_def(n_alloc, ld);
                outs() << "n alloc is param, and reach v is ";
                if (v == nullptr) outs() << "null\n";
                else outs() << *v << "\n";

                if (v == nullptr)   get_values(n_alloc, p_set, bb, index, p_map, know);
                else {
                    while (is_alloc_or_malloc(v)) {
                        v = (Instruction*) get_reach_def((Instruction*) v, ld);
//                outs() << *v << "\n";
                    }
                    get_values(v, p_set, bb, index, p_map, know);
                }
            } else {
                Value* v = get_reach_def(n_alloc, ld);
                while (is_alloc_or_malloc(v)) {
                    v = (Instruction*) get_reach_def((Instruction*) v, ld);
//                outs() << *v << "\n";
                }
                get_values(v, p_set, bb, index, p_map, know);
            }
        } else if (auto *phi = dyn_cast<PHINode>(v)) {
//            for (Use &use: phi->operands()) {
//                errs() << use->getNumUses() << " ";
//            }
            if (phi->getParent() == bb) {
                get_values(phi->getOperand(index), p_set, phi->getParent(), index, p_map, know);
            } else {
                int num = phi->getNumOperands();
                for (int i = 0; i < num; i ++) {
                    get_values(phi->getOperand(i), p_set, phi->getParent(), i, p_map, know);
                }
            }
        } else if (auto *func = dyn_cast<Function>(v)) {
            p_set->insert(func);
            if (bb == nullptr) {
                add_func(-1, p_map, func);
            } else {
                add_func(index, p_map, func);
            }
        } else if (auto *param = dyn_cast<Argument>(v)) {
//            errs() << "func arg: " << param->getParent()->getName() << "  " << param->getArgNo() << "\n";
            Function* F = param->getParent();
//            errs() << F->getName() << "\n";
            int pos = param->getArgNo();
            std::set<CallBase*> *F_calls = new std::set<CallBase*>;
            for (User *user: F->users()) {
                get_func_caller(F, user, F_calls);
            }
//            for (auto  *call: *F_calls) {
//                call->print(errs(), false); errs() << "\n";
//                errs() << *call->getOperandUse(pos).get() << "\n";
//            }
            for (auto *call: *F_calls) {
//                call->print(errs(), false); errs() << "\n";
//                errs() << *call->getOperandUse(pos).get() << "\n";
                n_pos = call;
                if (auto *para = dyn_cast<Argument>(call->getOperandUse(pos).get())) {
                    Value *v = get_reach_def(call->getOperandUse(pos).get(), n_pos);
                    if (v == nullptr) {
                        get_values(call->getOperandUse(pos).get(), p_set, bb, 0, p_map, know);
                    } else {
                        get_values(v, p_set, bb, 0, p_map, know);
                    }
                } else {
                    get_values(call->getOperandUse(pos).get(), p_set, bb, 0, p_map, know);
                }


            }
        } else if (auto *call = dyn_cast<CallBase>(v)) {
            auto* t = new std::set<Function*>;
            auto* t_map = new std::map<int, std::set<Function*>*>;
            auto* t_know = new std::set<Value*>;
            get_values(call->getCalledValue(), t, nullptr, 0, t_map, t_know);

            BasicBlock *t_bb = nullptr;
            if (auto *in = dyn_cast<Instruction>(call->getCalledValue())) {
                t_bb = in->getParent();
            }

            for (auto it = t_map->begin(); it != t_map->end(); it++) {
                for (Function* F: *(it->second)) {
                    for (BasicBlock &B: *F) {
                        for (Instruction &I: B) {
                            if (auto *ret = dyn_cast<ReturnInst>(&I)) {
                                get_values(ret->getReturnValue(), p_set, t_bb, it->first, p_map, know);
                            }
                        }
                    }
                }
            }
//            for (Function* F: *t) {
//                for (BasicBlock &B: *F) {
//                    for (Instruction &I: B) {
//                        if (auto *ret = dyn_cast<ReturnInst>(&I)) {
//                            get_values(ret->getReturnValue(), p_set, nullptr, 0, p_map);
//                        }
//                    }
//                }
//            }
        }
    }

    void get_func_caller(Value* F, User* user, std::set<CallBase*>* callers) {
        if (auto *Inst = dyn_cast<Instruction>(user)) {
            if (auto *call = dyn_cast<CallBase>(Inst)) {
//                if (F->getType()->isPointerTy() && ((PointerType*) F->getType())->getPointerElementType()->isFunctionTy()) {
//                    errs() << "need dfs " << F->getName()  << "\n";
//                }
                if (call->getCalledValue() == F) {
//                    errs() << "call this" << F->getName()  << "\n";
                    callers->insert(call);
                } else {
                    // call a func
//                    errs() << "use in param: " << F->getName()  << "\n";
                    auto* t = new std::set<Function*>;
                    auto* t_map = new std::map<int, std::set<Function*>*>;
                    auto* t_know = new std::set<Value*>;
                    get_values(call->getCalledValue(), t, nullptr, 0, t_map, t_know);
                    unsigned int len = call->getNumOperands(), pos = -1;
                    for (int i = 0; i < len; i++) {
                        if (call->getOperand(i) == F) pos = i;
                    }
//                    errs() << "use in param: " << F->getName() << " at pos: " << pos << "\n";
                    for (Function *f: *t) {
                        for (User *param_user: f->getArg(pos)->users()) {
//                            errs() << *param_user << "\n";
//                            errs() << "now arg is: " << *f->getArg(pos) << "\n";
                            get_func_caller(f->getArg(pos), param_user, callers);
                        }
                    }

                }
            } else if (auto *phi = dyn_cast<PHINode>(Inst)) {
                for (User *user1: (phi->users())) {
                    get_func_caller(phi, user1, callers);
                }
            } else {
                //arg and etc
                for (User *user1: (Inst->users())) {
                    get_func_caller(Inst, user1, callers);
                }
            }
        }
    }

    void init(Module &M) {
        for (Function &F: M) {
            (*bbs_map)[&F] = new std::set<BasicBlock*>;
            for (BasicBlock &bb: F) {
                (*bbs_map)[&F]->insert(&bb);
                (*dm_map)[&bb] = new std::set<BasicBlock*>;
                (*df_map)[&bb] = new std::set<BasicBlock*>;
                (*idm_map)[&bb] = new std::set<BasicBlock*>;
            }
        }
    }

    void make_dom(Module &M) {
        for (Function &F: M) {
            BasicBlock* enter = &(*F.getBasicBlockList().begin());
            std::set<BasicBlock*>* BBs = (*bbs_map)[&F];
            outs() << F.getName() << ": " << BBs->size() << "\n";
            for (BasicBlock* bb: *BBs) {
                bb->printAsOperand(outs(), false); outs() << " ";
                std::set<BasicBlock*>* doms = new std::set<BasicBlock*>();
                std::set<BasicBlock*>* know = new std::set<BasicBlock*>();
                dfs(enter, bb, know);
                for (BasicBlock* temp: *BBs) {
                    if (!(know->find(temp) != know->end())) {
                        doms->insert(temp);
                    }
                }
                (*dm_map)[bb] = doms;
            }
            outs() << "\n";
        }
    }

    void dfs(BasicBlock *bb, BasicBlock *no, std::set<BasicBlock *>* know) {
        if ((bb == no)) {
            return;
        }
        if ((know->find(bb) != know->end())) {
            return;
        }
        know->insert(bb);
        for (BasicBlock* next: successors(bb)) {
            if (know->find(next) == know->end() && (next != no)) {
                dfs(next, no, know);
            }
        }
    }

    void make_idm(Module &M) {
        for (Function &F: M) {
            std::set<BasicBlock*>* BBs = (*bbs_map)[&F];
            for (BasicBlock* A: *BBs) {
                std::set<BasicBlock*>* idoms = new std::set<BasicBlock*>();
                for (BasicBlock* B: *((*dm_map)[A])) {
                    if (AIDomB(A, B)) {
                        idoms->insert(B);
                    }
                }
                (*idm_map)[A] = (idoms);
            }
        }
    }

    bool AIDomB(BasicBlock *A, BasicBlock *B) {
        std::set<BasicBlock*>* ADoms = (*dm_map)[A];
        if (!(ADoms->find(B) != ADoms->end())) {
            return false;
        }
        if ((A == B)) {
            return false;
        }
        for (BasicBlock* temp: *ADoms) {
            if (!(temp == A) && !(temp == B)) {
                if ((*dm_map)[temp]->find(B) != (*dm_map)[temp]->end()) {
                    return false;
                }
            }
        }
        return true;
    }

    void make_df(Module &M) {
        for (Function &F: M) {
            for (BasicBlock* X: *(*bbs_map)[&F]) {
                std::set<BasicBlock*>* DF = new std::set<BasicBlock*>();
                for (BasicBlock* Y: *(*bbs_map)[&F]) {
                    if (DFXHasY(X, Y)) {
                        DF->insert(Y);
                    }
                }
                (*df_map)[X] = (DF);
            }
        }

    }

    bool DFXHasY(BasicBlock *X, BasicBlock *Y) {
        for (BasicBlock* P: predecessors(Y)) {
            if (((*dm_map)[X]->find(P) != (*dm_map)[X]->end()) &&
                ((X == Y) || !((*dm_map)[X]->find(Y) != (*dm_map)[X]->end()))) {
                return true;
            }
        }
        return false;
    }

    void print_map(std::map<BasicBlock*, std::set<BasicBlock*>*> *prt) {
        if (prt == dm_map) outs() << "print bb doms:\n";
        if (prt == idm_map) outs() << "print bb idoms:\n";
        if (prt == df_map) outs() << "print bb DF:\n";

        for (auto it = prt->begin(); it != prt->end(); it++) {
            BasicBlock* bb = it->first;
            bb->printAsOperand(outs(), false); outs() << ":(" << bb->getParent()->getName() << "):";
            for (BasicBlock *d_bb: *(it->second)) {
                d_bb->printAsOperand(outs(), false); outs() << " ";
            }
            outs() << "\n";
        }
    }

    void print_reach_def() {
//        outs() << "reach def:\n";
//        for (auto it = reach_def.begin(); it != reach_def.end(); it++) {
//            outs() << *it->first << "in basic block ";
//            BasicBlock* bb = it->first->getParent();
//            bb->printAsOperand(outs(), false);
//            outs() << ":(" << bb->getParent()->getName() << "):";
////            outs() << *it->second << "\n";
//            Value* v = it->second;
//            if (BasicBlock* b_v = dyn_cast<BasicBlock>(v)) {
//                v->printAsOperand(outs(), false);
//            } else {
//                outs() << *v;
//            }
//            outs() << "\n";
//        }
//        outs() << "=====================\n";
    }

    void print_bb_mem_phi_value() {
        for (auto ie = bb_mem_phi_value.begin(); ie != bb_mem_phi_value.end(); ie++) {
            outs() << "for instr: " <<  *ie->first << ":\n";
            for (auto it = ie->second->begin(); it != ie->second->end(); it++) {
                it->first->printAsOperand(outs(), false); outs() << " : ";
                for (Value* v: *it->second) {
                    if (v == nullptr) outs() << "null";
                    else {
                        if (BasicBlock* b_v = dyn_cast<BasicBlock>(v)) {
                            v->printAsOperand(outs(), false);
                        } else if (Function* f_v = dyn_cast<Function>(v)) {
                            outs() << f_v->getName();
                        } else {
                            outs() << *v;
                        }
                    }
                    outs() << " ";
                }
                outs() << "\n";
            }
        }

    }

    bool is_gep_cast_malloc_alloc(Value *v) {
        if (auto *gep = dyn_cast<GetElementPtrInst>(v)) {
            return true;
        }
        if (auto *cast = dyn_cast<BitCastInst>(v)) {
            return true;
        }
        return is_alloc_or_malloc(v);
    }

    Value *get_mem_pos(Value *v) {
        while (!is_alloc_or_malloc(v)) {
            if (auto *gep = dyn_cast<GetElementPtrInst>(v)) {
                v = gep->getPointerOperand();
            } else if (auto *cast = dyn_cast<BitCastInst>(v)) {
                v = cast->getOperand(0);
            } else {
                if (auto* param = dyn_cast<Argument>(v)) {
                    break;
                }
                outs()  << "error: " << *v << "\n";
                exit(-1);
//                return nullptr;
            }
        }
        return v;
    }

    void mem_phi(Module &M) {
        // todo: calc func params:
        for (Function &function: M) {
            for (Value &vv: function.args()) {
                Value *alloc = &vv;
                bb_mem_phi_value[alloc] = new std::map<BasicBlock*, std::set<Value*>*>;
                reach_def[alloc] = new std::map<Instruction*, Value*>;
                use_bbs.clear(), def_bbs.clear();
                use_insts = new std::set<Instruction*>;
                def_insts = new std::set<Instruction*>;
                def_pos = new std::map<Value*, int>;
                W = new std::set<BasicBlock*>, F = new std::set<BasicBlock*>;
                mem_use_def_dfs(alloc);
                W = new std::set<BasicBlock*>, F = new std::set<BasicBlock*>;
//                        mem_use_def_dfs(alloc);
                for (auto *v: *use_insts) {
                    ld2alloc[v] = alloc;
                }
                for (auto t: def_bbs) {
                    W->insert(t);
                }
                if (def_insts->size() == 0) continue;
                while (!W->empty()) {
                    BasicBlock* X = getRandFromHashSet(W);
                    W->erase(X);
                    for (BasicBlock* Y: *(*df_map)[X]) {
                        if (!(F->find(Y) != F->end())) {
                            F->insert(Y);
                            if (!(def_bbs.find(Y) != def_bbs.end())) {
                                W->insert(Y);
                            }
                        }
                    }
                }
                // F need insert phi
                (*f_map)[alloc] = F;
                (*w_map)[alloc] = W;
                (*def_insts_map)[alloc] = def_insts;
                (*use_insts_map)[alloc] = use_insts;
                (*def_pos_map)[alloc] = def_pos;
                outs() << "F has bb: ";
                for (BasicBlock* f_bb: *F) {
                    f_bb->printAsOperand(outs(), false); outs() << " ";
                }
                outs() << "\n";
                while (!S.empty()) S.pop();
                rename_dfs(alloc, &function.getEntryBlock());
                // todo: extend basic block value to common value
                for (auto* v_set: ValueSet(bb_mem_phi_value)) {
                    v_set->erase(nullptr);
                }
                print_bb_mem_phi_value();
                // tag
                bool tag = true;
                while (tag) {
                    tag = false;
                    for (auto* v_set: ValueSet(*bb_mem_phi_value[alloc])) {
                        std::vector<BasicBlock*> bbs_to_ext;
                        for (auto* v: *v_set) {
                            if (!v) continue;
                            if (auto* b_v = dyn_cast<BasicBlock>(v)) {
                                tag = true; bbs_to_ext.push_back(b_v);
                            }
                        }
                        for (BasicBlock* bb_to_ext: bbs_to_ext) {
                            for (Value* v_to_add: *(*bb_mem_phi_value[alloc])[bb_to_ext]) {
                                v_set->insert(v_to_add);
                            }
                            v_set->erase(bb_to_ext);
                        }
                    }
                }
            }
        }

        //calc alias
        for (Function &function: M) {
            for (BasicBlock &bb: function) {
                for (Instruction &inst: bb) {
                    //todo: to calc alias ptrs
                    if (auto *st = dyn_cast<StoreInst>(&inst)) {
                        Value *A = st->getValueOperand(), *B = st->getPointerOperand();
                        if (is_gep_cast_malloc_alloc(A) && is_gep_cast_malloc_alloc(B)) {
                            A = get_mem_pos(A);
                            B = get_mem_pos(B);
                            add_to_alias(A, B);
                            alias_inst->insert(st); // todo: check
                        }
                    }
                }
            }
        }
        outs() << "alias ptr:\n";
        for (auto *k: alias_ptr) {
            for (auto *kk: *k) {
                outs() << *kk << ",\t";
            }
            outs() << "\n";
        }

        //pre calc def-use
        for (Function &function: M) {
            for (BasicBlock &B: function) {
                for (Instruction &inst: B) {
                    bool run_tag = false;
                    Instruction *alloc = nullptr;
                    if (auto *call = dyn_cast<CallBase>(&inst)) {
                        if (call->getCalledValue()->getName().size() == 6 &&
                            call->getCalledValue()->getName() == "malloc") {
//                            errs() << call->getCalledValue()->getName() << "\n";
                            run_tag = true;
                            alloc = call;
                        }
                    } else if (auto *loc = dyn_cast<AllocaInst>(&inst)) {
                        run_tag = true;
                        alloc = loc;
                    }
                    if (run_tag) {
                        bb_mem_phi_value[alloc] = new std::map<BasicBlock*, std::set<Value*>*>;
                        reach_def[alloc] = new std::map<Instruction*, Value*>;
                        use_bbs.clear(), def_bbs.clear();
                        use_insts = new std::set<Instruction*>;
                        def_insts = new std::set<Instruction*>;
                        def_pos = new std::map<Value*, int>;
                        W = new std::set<BasicBlock*>, F = new std::set<BasicBlock*>;
                        mem_use_def_dfs(alloc);
                        (*def_insts_map)[alloc] = def_insts;
                        (*use_insts_map)[alloc] = use_insts;
                        (*def_pos_map)[alloc] = def_pos;
                    }
                }
            }
        }

        //merge alias
        for (auto *k_set: alias_ptr) {
            for (auto *k: *k_set) {
//                outs() << *kk << ",\t";
                auto *todo_def = (*def_insts_map)[k];
                auto *todo_use = (*use_insts_map)[k];
                for (auto *k1: *k_set) {
                    if (k1 != k) {
                        for (auto *v: *(*def_insts_map)[k1]) {
                            todo_def->insert(v);
                        }
                        for (auto *v: *(*use_insts_map)[k1]) {
                            todo_use->insert(v);
                        }
                    }
                }
            }
            outs() << "\n";
        }


        for (Function &function: M) {
            for (BasicBlock &B: function) {
                for (Instruction &inst: B) {
                    bool run_tag = false;
                    Instruction* alloc = nullptr;
                    if (auto *call = dyn_cast<CallBase>(&inst)) {
                        if (call->getCalledValue()->getName().size() == 6 &&
                                call->getCalledValue()->getName() == "malloc") {
//                            errs() << call->getCalledValue()->getName() << "\n";
                            run_tag = true;
                            alloc = call;
                        }
                    } else if (auto *loc = dyn_cast<AllocaInst>(&inst)) {
                        run_tag = true;
                        alloc = loc;
                    }
                    if (run_tag) {
                        bb_mem_phi_value[alloc] = new std::map<BasicBlock*, std::set<Value*>*>;
                        reach_def[alloc] = new std::map<Instruction*, Value*>;
                        use_bbs.clear(), def_bbs.clear();
                        use_insts = (*use_insts_map)[alloc];
                        def_insts = (*def_insts_map)[alloc];
                        def_pos = (*def_pos_map)[alloc];
                        W = new std::set<BasicBlock*>, F = new std::set<BasicBlock*>;
//                        mem_use_def_dfs(alloc);
                        for (auto *v: *use_insts) {
                            ld2alloc[v] = alloc;
                            use_bbs.insert(v->getParent());
                        }
                        for (auto *v: *def_insts) {
                            def_bbs.insert(v->getParent());
                        }
                        for (auto t: def_bbs) {
                            W->insert(t);
                        }
                        while (!W->empty()) {
                            BasicBlock* X = getRandFromHashSet(W);
                            W->erase(X);
                            for (BasicBlock* Y: *(*df_map)[X]) {
                                if (!(F->find(Y) != F->end())) {
                                    F->insert(Y);
                                    if (!(def_bbs.find(Y) != def_bbs.end())) {
                                        W->insert(Y);
                                    }
                                }
                            }
                        }
                        // F need insert phi
                        (*f_map)[alloc] = F;
                        (*w_map)[alloc] = W;
//                        (*def_insts_map)[alloc] = def_insts;
//                        (*use_insts_map)[alloc] = use_insts;
                        outs() << "F has bb: ";
                        for (BasicBlock* f_bb: *F) {
                            f_bb->printAsOperand(outs(), false); outs() << " ";
                        }
                        outs() <<  S.size() << "\n";
                        while (!S.empty()) S.pop();
                        rename_dfs(alloc, &function.getEntryBlock());
                        // todo: extend basic block value to common value
                        for (auto* v_set: ValueSet(bb_mem_phi_value)) {
                            v_set->erase(nullptr);
                        }
                        print_bb_mem_phi_value();
                        // tag
                        bool tag = true;
                        while (tag) {
                            tag = false;
                            for (auto* v_set: ValueSet(*bb_mem_phi_value[alloc])) {
                                std::vector<BasicBlock*> bbs_to_ext;
                                for (auto* v: *v_set) {
                                    if (!v) continue;
                                    if (auto* b_v = dyn_cast<BasicBlock>(v)) {
                                        tag = true; bbs_to_ext.push_back(b_v);
                                    }
                                }
                                for (BasicBlock* bb_to_ext: bbs_to_ext) {
                                    for (Value* v_to_add: *(*bb_mem_phi_value[alloc])[bb_to_ext]) {
                                        v_set->insert(v_to_add);
                                    }
                                    v_set->erase(bb_to_ext);
                                }
                            }
                        }
                        print_bb_mem_phi_value();
                    }
                }
            }
        }
    }

    template<typename T, typename _T>
    std::vector<T> KeySet(std::map<T, _T> test)
    {
        std::vector<T> keys;
        for(auto it = test.begin(); it != test.end(); ++it){
            keys.push_back(it->first);
        }
        return keys;
    }

    template<typename T, typename _T>
    std::vector<_T> ValueSet(std::map<T, _T> test)
    {
        std::vector<_T> keys;
        for(auto it = test.begin(); it != test.end(); ++it){
            keys.push_back(it->second);
        }
        return keys;
    }

    BasicBlock* getRandFromHashSet(std::set<BasicBlock*>* hashSet) {
        for (BasicBlock* bb: (*hashSet)) {
            return bb;
        }
        return nullptr;
    }

    Value* get_reach_def(Value* alloc, Instruction* pos) {
        reach_v = nullptr;
        F = (*f_map)[alloc], W = (*w_map)[alloc];
        def_insts = (*def_insts_map)[alloc];
        def_pos = (*def_pos_map)[alloc];
        if (def_insts == nullptr || def_insts->empty()) return nullptr;
        for (auto *v: *alias_inst) {
            if (def_insts->find(v) != def_insts->end()) def_insts->erase(v);
        }
        outs() << *alloc << " defs: \n";
        for (Instruction* def_inst: *def_insts) {
            outs() << *def_inst << "\n";
        }
        outs() << "==========================\n";
        outs() << "F has bb: \n";
        for (BasicBlock* bb: *F) {
            bb->printAsOperand(outs(), false), outs() << " ";
        }
        outs() << "==========================\n";
        while (!S.empty()) S.pop();
        get_reach_v_dfs(alloc, pos, &pos->getParent()->getParent()->getEntryBlock());
//        if (auto *bb = dyn_cast<BasicBlock>(reach_v)) {
//            outs() << *alloc << " at " << *pos << " is "; bb->printAsOperand(outs(), false); outs() << "\n";
//            for (Value *def: *(*bb_mem_phi_value[alloc])[bb]) {
//                outs() << *def << "\n";
//            }
//        }
        if (reach_v) {
            outs() << "reach v is \n";
            outs() << *reach_v;
        }
        return reach_v;
    }


    void get_reach_v_dfs(Value* alloc, Instruction *pos, BasicBlock *X) {
        int cnt = 0;
        if (F->find(X) != F->end()) { // X has mem phi
            X->printAsOperand(outs(), false);
            outs() << "\n";
            S.push(X); cnt++;
        }
        for (Instruction* A = X->getFirstNonPHIOrDbg(); A; A = A->getNextNonDebugInstruction()) {
//            (*reach_def[alloc])[A] = get_stack_top_v();
            if (A == pos) {
                reach_v = get_stack_top_v();
            }
            if (def_insts->find(A) != def_insts->end()) {
                if (auto* st = dyn_cast<StoreInst>(A)) {
//                    outs() << *st->getValueOperand() << "\n";
//                    outs() << *st->getOperandUse(0).get() << "\n";
                    S.push(st->getValueOperand());
                    cnt++;
//                    outs() << "S size is " << S.size() << "\n";
                } else if (auto* func_call = dyn_cast<CallBase>(A)) {
                    if (func_call->getCalledValue()->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
                        S.push(func_call->getOperand(1));
                        cnt++;
                    } else {
                        int idx = -1;
                        for (int i = 0; i < func_call->getNumArgOperands(); i++) {
//                    log(func_call->getOperand(i));
                            if (func_call->getOperand(i) == alloc) {
                                idx = i;
                            }
                        }
//                log(idx);
//                to_log = false;
                        if (idx == -1) idx = (*p_def_pos)[func_call];
                        if (idx != -1) {
                            outs() << *func_call << " use ptr " << *alloc << " at index of " << idx << "\n";
                            Value *param_reach_def = get_param_reach_def(func_call->getCalledFunction()->getArg(idx),
                                                                         func_call->getCalledFunction()->getEntryBlock().getTerminator());
                            if (param_reach_def != nullptr) {
                                outs() << *param_reach_def << "\n";
                                S.push(param_reach_def);
                                cnt++;
                            }
                        }
                    }

                }
            } else if (auto* func_call = dyn_cast<CallBase>(A)) {

            }
        }

//        for (BasicBlock* bb: successors(X)) {
//            if (F->find(bb) != F->end()) {
//                add_to_bb_mem_phi_value(alloc, bb, get_stack_top_v());
//            }
//        }
        for (BasicBlock* next: *(*idm_map)[X]) {
            get_reach_v_dfs(alloc, pos, next);
        }
        for (int i = 0; i < cnt; i++) {
            S.pop();
//            outs() << "S pop\n";
        }
    }

    std::stack<Value*> param_S;
    Value* reach_p;
    std::set<BasicBlock*> *p_f, *p_w;
    std::set<Instruction*> *p_def_insts;
    std::map<Value*, int> *p_def_pos;

    Value* get_param_reach_def(Value* alloc, Instruction* pos) {
        reach_p = nullptr;
        p_f = (*f_map)[alloc], p_w = (*w_map)[alloc];
        p_def_pos = (*def_pos_map)[alloc];
        p_def_insts = (*def_insts_map)[alloc];
        if (p_def_insts == nullptr || p_def_insts->empty()) return nullptr;
        while (!param_S.empty()) param_S.pop();
        get_reach_p_dfs(alloc, pos, &pos->getParent()->getParent()->getEntryBlock());
        return reach_p;
    }


    void get_reach_p_dfs(Value* alloc, Instruction *pos, BasicBlock *X) {
        int cnt = 0;
        if (p_f->find(X) != p_f->end()) { // X has mem phi
            X->printAsOperand(outs(), false);
            outs() << "\n";
            param_S.push(X); cnt++;
        }
        for (Instruction* A = X->getFirstNonPHIOrDbg(); A; A = A->getNextNonDebugInstruction()) {
            if (A == pos) {
                reach_p = get_stack_top_p();
            }
            if (p_def_insts->find(A) != p_def_insts->end()) {
                if (auto* st = dyn_cast<StoreInst>(A)) {
                    param_S.push(st->getValueOperand());
                    cnt++;
                } else if (auto* func_call = dyn_cast<CallBase>(A)) {
                    if (func_call->getCalledValue()->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
                        param_S.push(func_call->getOperand(1));
                        cnt++;
                    } else {
                        int idx = -1;
                        for (int i = 0; i < func_call->getNumArgOperands(); i++) {
//                    log(func_call->getOperand(i));
                            if (func_call->getOperand(i) == alloc) {
                                idx = i;
                            }
                        }
//                log(idx);
//                to_log = false;
                        if (idx == -1) idx = (*p_def_pos)[func_call];
                        if (idx != -1) {
                            outs() << *func_call << " use ptr " << *alloc << " at index of " << idx << "\n";
                            std::stack<Value*> tmp, tmp2;
                            Value* t_reach_p;
                            t_reach_p = reach_p;
                            while (!param_S.empty()) {
                                tmp.push(param_S.top());
                                param_S.pop();
                            }
                            while (!tmp.empty()) {
                                tmp2.push(tmp.top());
                                tmp.pop();
                            }
                            Value *param_reach_def = get_param_reach_def(func_call->getCalledFunction()->getArg(idx),
                                                                         func_call->getCalledFunction()->getEntryBlock().getTerminator());
                            while (!tmp2.empty()) {
                                tmp.push(tmp2.top());
                                tmp2.pop();
                            }

                            while (!tmp.empty()) {
                                param_S.push(tmp.top());
                                tmp.pop();
                            }
                            reach_p = t_reach_p;

                            if (param_reach_def != nullptr) {
                                outs() << *param_reach_def << "\n";
                                param_S.push(param_reach_def);
                                cnt++;
                            }
                        }
                    }

                }
            }
        }

        for (BasicBlock* next: *(*idm_map)[X]) {
            get_reach_p_dfs(alloc, pos, next);
        }
        for (int i = 0; i < cnt; i++) {
            param_S.pop();
        }
    }

    template<typename T>
    void log(T t) {
        if (to_log) outs() << t << "\n";
    }

    template<typename T>
    void log(T* t) {
        if (to_log) outs() << *t << "\n";
    }

    void rename_dfs(Value* alloc, BasicBlock* X) {
        int cnt = 0;
        if (F->find(X) != F->end()) { // X has mem phi
            S.push(X);
        }
        for (Instruction* A = X->getFirstNonPHIOrDbg(); A; A = A->getNextNonDebugInstruction()) {
//            if (use_insts.find(A) != use_insts.end()) {
//                (*reach_def[alloc])[A] = get_stack_top_v();
//            }
            (*reach_def[alloc])[A] = get_stack_top_v();
            if (def_insts->find(A) != def_insts->end()) {
                if (auto* st = dyn_cast<StoreInst>(A)) {
                    S.push(st->getValueOperand());
                    cnt++;
                } else if (auto *func_call = dyn_cast<CallBase>(A)) {
//                    S.push(call);
                    if (func_call->getCalledValue()->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
                        S.push(func_call->getOperand(1));
                        cnt++;
                    } else {
                        int idx = -1;
                        for (int i = 0; i < func_call->getNumArgOperands(); i++) {
//                    log(func_call->getOperand(i));
                            if (func_call->getOperand(i) == alloc) {
                                idx = i;
                            }
                        }
//                log(idx);
//                to_log = false;
                        if (idx == -1) idx = 0;
                        if (idx != -1) {
                            outs() << *func_call << " use ptr " << *alloc << " at index of " << idx << "\n";
                            Value *param_reach_def = get_param_reach_def(func_call->getCalledFunction()->getArg(idx),
                                                                         func_call->getCalledFunction()->getEntryBlock().getTerminator());
                            if (param_reach_def != nullptr) {
                                outs() << *param_reach_def << "\n";
                                S.push(param_reach_def);
                                cnt++;
                            }
                        }
                    }
                } else {
                    //todo: this branch maybe unreachable
                    assert("error");
                }
            }
        }
        for (BasicBlock* bb: successors(X)) {
            if (F->find(bb) != F->end()) {
                add_to_bb_mem_phi_value(alloc, bb, get_stack_top_v());
            }
        }
        for (BasicBlock* next: *(*idm_map)[X]) {
            rename_dfs(alloc, next);
        }
        for (int i = 0; i < cnt; i++) S.pop();
    }

    Value* get_stack_top_v() {
        if (S.empty()) {
            return nullptr;
        }
        return S.top();
    }

    Value* get_stack_top_p() {
        if (param_S.empty()) {
            return nullptr;
        }
        return param_S.top();
    }

    // no-element-analysis
    void mem_use_def_dfs(Value *inst) {
        for (User *user: inst->users()) {
//            outs() << *user << "\n";
            if (auto *phi = dyn_cast<PHINode>(user)) {
                mem_use_def_dfs(phi);
            } else if (auto* gep = dyn_cast<GetElementPtrInst>(user)) {
                mem_use_def_dfs(gep);
            } else if (auto* ld = dyn_cast<LoadInst>(user)) {
                use_bbs.insert(ld->getParent());
                use_insts->insert(ld);
                //todo:: dangerous method
                mem_use_def_dfs(ld);
            } else if (auto* st = dyn_cast<StoreInst>(user)) {
                if (st->getValueOperand() == inst) {
                    use_bbs.insert(st->getParent());
                    use_insts->insert(st);
                } else {
                    def_bbs.insert(st->getParent());
                    def_insts->insert(st);
                }

            } else if (auto* cast = dyn_cast<BitCastInst>(user)) {
                mem_use_def_dfs(cast);
            } else if (auto *call = dyn_cast<CallBase>(user)) {
                if (call->getCalledValue()->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
//                    outs() << "memcpy st" << *get_mem_pos(call->getOperand(0)) << "\n";
//                    outs() << "memcpy from" << *get_mem_pos(call->getOperand(1)) << "\n";
//                    call->getOperand(1);
                    if (call->getOperand(0) == inst) {
                        def_insts->insert(call);
                        def_bbs.insert(call->getParent());
                    } else {
//                        def_insts->insert(call);
//                        def_bbs.insert(call->getParent());
                    }

                } else {
                    int idx = -1;
                    for (int i = 0; i < call->getNumArgOperands(); i++) {
//                    log(func_call->getOperand(i));
                        if (call->getOperand(i) == inst) {
                            idx = i;
                        }
                    }
                    if (auto *func = dyn_cast<Function>(call->getCalledValue())) {
                        Value *v = get_param_reach_def(call->getCalledFunction()->getArg(idx),
                                                       call->getCalledFunction()->getEntryBlock().getTerminator());
                        if (v != nullptr) {
                            outs() << *call << " def " << *inst << "\n";
                            def_bbs.insert(call->getParent());
                            def_insts->insert(call);
                            (*def_pos)[call] = idx;
                        }
                    }
                }


            }

        }
    }

//    //alloca-instr's reach def at pos
//    std::set<Value*>* get_reach_defs(Instruction* alloc, Instruction* pos) {
//
//    }

    bool runOnModule(Module &M) override {
//        errs() << "Hello: ";
//        errs().write_escaped(M.getName()) << '\n';
        for (Function &F: M) {
            outs() << F << "\n";
        }
        init(M);
        make_dom(M);
        print_map(dm_map);
        make_idm(M);
        print_map(idm_map);
        make_df(M);
        print_map(df_map);
        mem_phi(M);
        print_reach_def();
        for (Function &F: M) {
//            errs() << F.getName();
//            errs() << " use empty: " << F.users().empty() << "\n";
            for (BasicBlock &B: F) {
//                F.getArg();
//                auto I = B.getInstList().begin();
                for (Instruction* I = B.getFirstNonPHIOrDbg(); I; I = I->getNextNonDebugInstruction()) {
//                for (Instruction &I: B) {
//                    if (I.getDebugLoc().getLine() == 0)  {
//                        if (auto *p = dyn_cast<PHINode>(&I)); else continue;
//                    }
//                    I->print(errs(), false); errs() << '\n';
                    if (auto *call = dyn_cast<CallBase>(I)) {
                        Value* v = call->getCalledValue();
                        if (v->getName().size() >= 4 && v->getName()[0] == 'l' && v->getName()[1] == 'l'
                            && v->getName()[2] == 'v' && v->getName()[3] == 'm') {
                            continue;
                        }
//                        values.clear();
                        funcs->clear();
                        func_maps->clear();
                        c_know->clear();
//                        if (call->getDebugLoc().getLine() == 88) {
//                            errs() << "line 88\n";
//                        }
                        //todo: check this position is correct or not
                        n_pos = call;
                        get_values(call->getCalledValue(), funcs, nullptr, 0, func_maps, c_know);
                        std::vector<std::string> ret;
                        for (auto func: *funcs) {
                            ret.push_back(func->getName());
                        }
                        outs() << call->getDebugLoc().getLine() << " : ";
                        for (int i = 0; i < ret.size(); i++) {
                            outs() << ret[i];
                            if (i < ret.size() - 1) outs() << ", ";
                        }
                        outs() << "\n";
//                        errs() << call->getDebugLoc().getLine() << ": ";
//                        for (auto it = func_maps->begin(); it != func_maps->end(); it++) {
//                            for (auto *func: *(it->second)) {
//                                errs() << "index: " << it->first << func->getName() << "\t";
////                                errs() << func->getName() << " ";
//                            }
//                        }
//                        errs() << "\n";
                    }
                }
            }
        }
//        errs() << "------------------------------\n";
        return false;
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
//#if LLVM_VERSION_MAJOR == 5
//   Passes.add(new EnableFunctionOptPass());
//#endif
    Passes.add(new EnableFunctionOptPass());
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
//   Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
//#ifndef NDEBUG
//   system("pause");
//#endif
}

