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
    std::set<Function*> *funcs = new std::set<Function*>;

    std::map<int, std::set<Function*>*> *func_maps = new std::map<int, std::set<Function*>*>;
    std::set<Value*> *c_know = new std::set<Value*>;

    void add_func(int index, std::map<int, std::set<Function*>*> *p_map, Function* func) {
        if ((*p_map)[index] == nullptr) {
            (*p_map)[index] = new std::set<Function*>;
        }
        (*p_map)[index]->insert(func);
    }

    void get_values(Value* v, std::set<Function*>* p_set, BasicBlock *bb, int index, std::map<int, std::set<Function*>*> *p_map, std::set<Value*>* know) {
        if (know->find(v) != know->end()) return;
        know->insert(v);
        if (auto *phi = dyn_cast<PHINode>(v)) {
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
                get_values(call->getOperandUse(pos).get(), p_set, bb, 0, p_map, know);
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


    bool runOnModule(Module &M) override {
//        errs() << "Hello: ";
//        errs().write_escaped(M.getName()) << '\n';
        for (Function &F: M) {
            errs() << F << "\n";
//            for (BasicBlock &B: F) {
//                for (Instruction &I: B) {
//                    errs() << I << "\n";
//                }
//            }
        }
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
//                        values.clear();
                        funcs->clear();
                        func_maps->clear();
                        c_know->clear();
//                        if (call->getDebugLoc().getLine() == 25) {
//                            errs() << "line 25\n";
//                        }
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

