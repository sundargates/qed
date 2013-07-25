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

#define DEBUG_TYPE "hello"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/DIBuilder.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Analysis/Dominators.h"


#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Support/CommandLine.h"

#include <sstream>
#include <cstdlib>

using namespace llvm;

#define FOR(i,x,y) for(int i=x; i<=y; i++)
#define FORN(i,n) FOR(i,0,(n-1))
#define FORE(it,v) for(__typeof(v.begin()) it = v.begin(); it != v.end(); it++)
#define db(x) errs() << (#x) << " = " << x << "\n";
#define CLR(x) memset(x,0,sizeof(x));
#define sz(x) ((int)x.size())
#define mp std::make_pair
#define pb push_back
#define re return
typedef unsigned long long ull;
typedef long long ll;
typedef std::vector<int> vi;
typedef std::pair<int,int> ii;
typedef ValueToValueMapTy ValueDuplicateMap;
#define each_custom(item, set, begin, end) (__typeof((set).begin()) item = (set).begin(), __end = (set).end(); item != __end; ++item)
#define each(item, set) each_custom(item, set, begin, end)

enum QEDLevel
{
    EDDI,
    CFTSS,
    EDDIANDCFTSS,
    CFCSS,
    ALL
};

// Some Command Line Arguments will be parsed here
static cl::opt<QEDLevel> QEDMode 
(
    "QED-Mode", 
    cl::init(ALL), 
    cl::desc("Choose QED Mode:"),
    cl::value_desc("QED Mode"),
    cl::values
    (
        clEnumVal(EDDI , "Enable EDDI Transformations"),
        clEnumVal(CFTSS, "Enable CFTSS Transformations"),
        clEnumVal(EDDIANDCFTSS, "Enable both EDDI and CFTSS Transformations"),
        clEnumVal(CFCSS, "Enable CFCSS Transformations"),
        clEnumVal(ALL,   "Enable All Transformations"),
        clEnumValEnd
    )
);

static cl::opt<int> NUM_ELEMENTS_IN_CFTSS_ARRAY
(
    "NUM-CFTSS-BB",
    cl::init(10),
    cl::desc("Choose the number of basic blocks that you want to track")
);

namespace
{
    struct QED : public ModulePass
    {
        public:
        static char ID;
        Value *one;
        LLVMContext & context;
        IntegerType * i1;
        IntegerType * i8;
        IntegerType * i32;
        IntegerType * i64;
        ConstantInt * i1_true;
        ConstantInt * i1_false;
        ConstantInt * i32_zero;
        int currentBasicBlock;
        // int NUM_ELEMENTS_IN_CFTSS_ARRAY;


        // GlobalVariable *last_cftss_id;
        GlobalVariable *cftss_array;
        GlobalVariable *cftss_array_pos;
        GlobalVariable *cftss_array_n;
        GlobalVariable *global_cfcss_id;


        Function *EDDICheckFunction;
        std::string EDDI_CHECK_FUNCTION_NAME;

        Function *CFCSSCheckFunction;
        std::string CFCSS_CHECK_FUNCTION_NAME;

        QED() : ModulePass(ID), context(getGlobalContext())
        {
            i1                        = Type::getInt1Ty(context);
            i8                        = Type::getInt8Ty(context);
            i32                       = Type::getInt32Ty(context);
            i64                       = Type::getInt64Ty(context);
            
            one                       = ConstantInt::get(Type::getInt32Ty(context),1);
            i1_true                   = ConstantInt::get(i1, true);
            i1_false                  = ConstantInt::get(i1, false);
            i32_zero                  = ConstantInt::get(i32, 0);
            EDDI_CHECK_FUNCTION_NAME  = "eddi_check_function";
            CFCSS_CHECK_FUNCTION_NAME = "cfcss_check_function";
            
            // db(QEDMode);
            // db(NUM_CFTSS_BB);
            // NUM_ELEMENTS_IN_CFTSS_ARRAY = NUM_CFTSS_BB;
            // db(NUM_ELEMENTS_IN_CFTSS_ARRAY);
        }
        bool supportsEDDI(QEDLevel QEDMode)
        {
            if(QEDMode==EDDI)
                return true;
            if(QEDMode==EDDIANDCFTSS)
                return true;
            if(QEDMode==ALL)
                return true;
            return false;
        }
        bool supportsCFTSS(QEDLevel QEDMode)
        {
            if(QEDMode==CFTSS)
                return true;
            if(QEDMode==EDDIANDCFTSS)
                return true;
            if(QEDMode==CFCSS)
                return true;
            if(QEDMode==ALL)
                return true;
            return false;
        }
        bool supportsCFCSS(QEDLevel QEDMode)
        {
            if(QEDMode==CFCSS)
                return true;
            if(QEDMode==ALL)
                return true;
            return false;
        }
        bool prototypeNeedsToBeModified(Function *F)
        {
            // db(F->getName());
            return  F!=NULL
                    && (!F->getBasicBlockList().empty() && F->size())
                    && F->getName().compare("main") 
                    && (F->getName().find("entry_point")==StringRef::npos)
                    && F->getName().compare(EDDI_CHECK_FUNCTION_NAME)
                    && F->getName().compare(CFCSS_CHECK_FUNCTION_NAME);
        }
        unsigned bitWidth(Type * type)
        {
            return type->isPointerTy() ? 32 : type->getPrimitiveSizeInBits();
        }

        void cloneGlobal(GlobalVariable * global, Module &M, ValueDuplicateMap & map)
        {
            // db(global->getName());
            std::string name = makeName(global, "_dup");
            PointerType * type = global->getType();
            GlobalVariable *global_dup = new GlobalVariable
            (
                M,
                type->getElementType(),
                global->isConstant(),
                global->getLinkage(),
                global->getInitializer(),
                name,
                global,
                global->getThreadLocalMode(),
                type->getAddressSpace()
            );
            
            global_dup->copyAttributesFrom(global);
            map[global] = global_dup;
        }
        void cloneGlobalVariables(Module &M, ValueDuplicateMap & map)
        {
            for (Module::global_iterator I = M.global_begin(), E = M.global_end(); I != E; ++I)
            {
                // Ignore all 'special' globals.
                // db(I->getName());
                if (
                        I->getName().startswith("llvm.") 
                        || I->getName().startswith(".llvm.") 
                        || I->getName().startswith("__")
                        || I->getName().startswith("__")
                        || !I->hasInitializer()
                    )
                    continue;
                cloneGlobal(I, M, map);
            }
        }
        void modifyPrototype(Function * func, ValueDuplicateMap & map)
        {
            // Modify function type to reflect duplicated arguments, muxed return type
            FunctionType * type = func->getFunctionType();
            Type * return_type = type->getReturnType();
            // const AttributeSet &PAL = func->getAttributes();

            std::vector<Type *> arg_types;
            for each_custom(arg_type, *type, param_begin, param_end)
            {
                arg_types.push_back(*arg_type);
                arg_types.push_back(*arg_type);
            }

            Type * new_return_type = return_type;
            if (return_type->isVoidTy())
                new_return_type = Type::getVoidTy(context);
            else
            {
                std::vector<Type*> RetTypes;
                Type *dup_return_type = return_type;
                RetTypes.pb(return_type);
                RetTypes.pb(dup_return_type);
                new_return_type = StructType::get(context, RetTypes, true);
            }

            FunctionType * new_type = FunctionType::get(new_return_type, arg_types, type->isVarArg());
            unsigned address_space  = func->getType()->getAddressSpace();
            func->mutateType(PointerType::get(new_type, address_space));

            /* Duplicate arguments */
            std::vector<Argument *> arg_list;
            for each_custom(arg, *func, arg_begin, arg_end)
                arg_list.push_back(arg);
                
            for each(arg, arg_list)
            {
                Argument * arg_dup = new Argument((*arg)->getType(), makeName(*arg, "_dup"));
                func->getArgumentList().insertAfter(*arg, arg_dup);
                map[*arg] = arg_dup;
            }
            
            // The existing function return attributes.
            // SmallVector<AttributeSet, 8> AttributesVec;

            // //Push empty attribute set for Return Index because the older attributes may not be valid anymore
            // AttributesVec.pb(AttributeSet());
                
                
            // // Construct the new parameter list from non-dead arguments. Also construct
            // // a new set of parameter attributes to correspond. Skip the first parameter
            // // attribute, since that belongs to the return value.
            // unsigned i = 0;
            // // unsigned size = 0;
            // for (Function::arg_iterator I = func->arg_begin(), E = func->arg_end();
            // I != E; ++I, ++i)
            // {
            //     // Get the original parameter attributes (skipping the first one, that is
            //     // for the return value.
            //     // Push the attributes twice to reflect the fact that the
            //     // arguments have been duplicated.
            //     AttributeSet temp = PAL.getParamAttributes(i+1);
            //     AttributesVec.push_back(temp);
            //     AttributesVec.push_back(temp);
            // }

            // // Push the Function attributes
            // if (PAL.hasAttributes(AttributeSet::FunctionIndex))
            //     AttributesVec.push_back(AttributeSet::get(func->getContext(),
            //                               PAL.getFnAttributes()));

            // // Reconstruct the AttributesList based on the vector we constructed.
            // // AttributeSet NewPAL = AttributeSet::get(func->getContext(), AttributesVec);
            // // func->setAttributes(NewPAL);
            func->setAttributes(AttributeSet());

        }
        std::pair<Value *, bool>  mapValue(Value * value, ValueDuplicateMap & map)
        {
            Value * direct_match = map.lookup(value);
            if (direct_match)
                return mp(direct_match, true);

            Constant * constant = dyn_cast<Constant>(value);
            if (constant)
            {
                Type * type = constant->getType();
                std::vector<Constant *> operands;
                for each_custom(operand, *constant, op_begin, op_end)
                {
                    operands.push_back(cast<Constant>(mapValue(*operand, map).first));
                }
                ConstantExpr * constant_expr = dyn_cast<ConstantExpr>(constant);
                if (constant_expr)
                {
                    return mp(constant_expr->getWithOperands(operands, type), true);
                }
                else if (isa<ConstantArray>(constant))
                {
                    return mp(ConstantArray::get(cast<ArrayType>(type), operands), true);
                }
                else if (isa<ConstantStruct>(constant))
                {
                    return mp(ConstantStruct::get(cast<StructType>(type), operands), true);
                }
                else if (isa<ConstantVector>(constant))
                {
                    return mp(ConstantVector::get(operands), true);
                }
                else
                {
                    return mp(constant, true);
                }
            }
            // Instruction * instruction = dyn_cast<Instruction>(value);
            // if(instruction)
            // {
            //     instruction->dump();
            //     Instruction *NI = instruction->clone();
            //     map[instruction] = NI;
            //     mapOperands(NI, map);
            //     return NI;
            // }
            // value->dump();
            // errs()<<"The above operand does not have a replacement?\n";
            return mp(value, false);
        }
        bool isCloneable(Instruction *inst)
        {
            bool success = true;
            success &= !isa<TerminatorInst>(inst);

            CallInst *call = dyn_cast<CallInst>(inst);
            Function *F = call?call->getCalledFunction():NULL;
            success &= !call 
                    || (call && (call->isInlineAsm()))
                    || (call && F && (F->isIntrinsic()))
                    ;
            return success;
        }
        bool isPhi(Instruction *inst)
        {
            bool success = true;
            success &= isa<PHINode>(inst);
            return success;
        }
        bool isGetElementPtrInst(Instruction *inst)
        {
            bool success = true;
            success &= isa<GetElementPtrInst>(inst);
            return success;
        }
        bool isCastInst(Instruction *inst)
        {
            bool success = true;
            success &= isa<CastInst>(inst);
            return success;
        }
        bool isCallable(Value *inst)
        {
            CallInst *call = dyn_cast<CallInst>(inst);
            if(call)
                return true;
            return false;
        }
        bool isAllocable(Instruction *inst)
        {
            return isa<AllocaInst>(inst);
        }
        void mapOperands(Instruction *instr, ValueDuplicateMap & map, std::vector<std::pair<Instruction *, Value *> > &toBeReplaced)
        {
            for each_custom(operand, *instr, op_begin, op_end)
            {
                std::pair<Value *, bool> t = mapValue(*operand, map);
                *operand = t.first;
                if(!t.second && !isCallable(*operand))
                {
                    Value *temp  = *operand;
                    std::pair<Instruction *, Value *> V = mp(instr, temp);
                    toBeReplaced.pb(V);
                    // db("PUSHED");
                }
            }
        }
        void printInstruction(Instruction *I)
        {
            errs()<<I->getName()<<"\t"<<I->getNumOperands()<<"\t";
            for(unsigned i = 0;i < I->getNumOperands(); i++)
            {
                errs()<<I->getOperand(i)->getValueID()<<"\t";
                I->getOperand(i)->dump();
            }
        }
        CmpInst * createCheckInst(Value * a, Value * b, const Twine & name, Instruction * insertBefore)
        {
            bool float_type = a->getType()->isFPOrFPVectorTy();
            CmpInst::OtherOps op = float_type ? Instruction::FCmp : Instruction::ICmp;
            CmpInst::Predicate predicate = float_type ? CmpInst::FCMP_ONE : CmpInst::ICMP_NE;
            CmpInst * cmp = CmpInst::Create(op, predicate, a, b, name, insertBefore);
            return cmp;
        }
        bool hasOutput(Instruction *I)
        {
            if(isa<CallInst>(I) || isa<TerminatorInst>(I) || 
                isa<AllocaInst>(I) || isa<LoadInst>(I) || isa<StoreInst>(I))
                return false;
            return true;
        }
        std::string makeName(Value * value, const char * suffix)
        {
            return value->hasName() ? value->getName().str() + suffix : std::string();
        }
        Function * getExternalFunction(StringRef name, FunctionType * type, Module * module)
        {
                module->getOrInsertFunction(name, type);
                Function * function = module->getFunction(name);
                assert(function);
                return function;
        }
        CallInst * createExitCall(Value * status, BasicBlock * block, Module * module)
        {
                FunctionType * exit_type = FunctionType::get(Type::getVoidTy(context), Type::getInt32Ty(context), false);
                Function * exit_func = getExternalFunction("exit", exit_type, module);
                CallInst * call = CallInst::Create(exit_func, status, "", block);
                call->setDoesNotThrow();
                return call;
        }
//         Duplicate all call instruction parameters, demux the return value
//         Depends on muxFunction being called on all functions to produce the function type map
        void modifyCallInstruction(CallInst *call, ValueDuplicateMap & map, std::vector<CallInst *> & toBeRemoved)
        {
            std::vector<Value *> args;
            for (unsigned index = 0; index < call->getNumArgOperands(); index++)
            {
                Value * arg = call->getArgOperand(index);
                args.push_back(arg);
                args.push_back(mapValue(arg, map).first);
            }
            Function * function = call->getCalledFunction();
            CallInst * new_call = CallInst::Create(function, args, "", call);
            // new_call->setAttributes(call->getAttributes());

            Type * result_type = call->getType();
            if (!result_type->isVoidTy())
            {
                Value *result =  ExtractValueInst::Create (new_call, 0, "", call);
                Value *result_dup =  ExtractValueInst::Create (new_call, 1, "", call);
                call->replaceAllUsesWith(result);
                map[result] = result_dup;
            }
            toBeRemoved.pb(call);
        }
        void muxReturnInst(ReturnInst * ret, ValueDuplicateMap & map)
        {
            Value *value = ret->getReturnValue();
            Value *value_dup = mapValue(value, map).first;
            std::vector< Value * > V;
            std::vector< Type * > Elements;
            V.push_back(value);
            V.push_back(value_dup);
            
            Elements.push_back(value->getType());
            Elements.push_back(value_dup->getType());
            Type *type = StructType::get(context, Elements, true);
            AllocaInst *ptr = new AllocaInst (type, 0, "", ret);
            Instruction *str = new LoadInst(ptr, "", ret);
            str = InsertValueInst::Create(str, value, 0, "", ret);
            str = InsertValueInst::Create(str, value_dup, 1, "", ret);
            
            ret->setOperand(0, str);
        }
        bool remapOperand(Instruction *instr, Value *old_value, Value *new_value)
        {
            for each_custom(operand, *instr, op_begin, op_end)
                if(*operand == old_value)
                {
                    *operand = new_value;
                    return true;
                }
            return false;
        }
        Instruction *getNextInstruction(Instruction *inst)
        {
            if (inst == NULL) return NULL;
            BasicBlock::iterator iter = inst;
            Instruction *nextInstruction = ++iter;
            if(nextInstruction==inst->getParent()->end())
                return NULL;
            return nextInstruction;
        }
        Value * createReduction(Instruction::BinaryOps op, ArrayRef<Value *> inputs, Instruction * insertBefore, const Twine & name = "")
        {
            size_t size = inputs.size();
            switch (size)
            {
                case 0:
                    return NULL;
                case 1:
                    return inputs[0];
                default:
                    size_t middle = size / 2;
                    Value * input1 = createReduction(op, inputs.slice(0, middle), insertBefore);
                    Value * input2 = createReduction(op, inputs.slice(middle), insertBefore);
                    assert(!input1->getType()->isVectorTy() && "Vectors cannot be reduced");
                    assert(!input2->getType()->isVectorTy() && "Vectors cannot be reduced");

                    assert(!input1->getType()->isPointerTy() && "Pointers shouldn't be compared");
                    assert(!input2->getType()->isPointerTy() && "Pointers shouldn't be compared");
                    // errs() <<"\n\n";
                    // input1->getType()->dump();errs()<<"\t";
                    // input2->getType()->dump();
                    // if(input1->getType()->isVectorTy())
                    // {
                    //     assert(input1->getType()->getVectorElementType()==i1);
                    //     // Value *temp = createReduction()
                    // }
                    // if(input2->getType()->isVectorTy())
                    // {
                    //     assert(input1->getType()->getVectorElementType()==i1);
                    //     assert(false);
                    // }
                    return BinaryOperator::Create(op, input1, input2, name, insertBefore);
            }
        }
        Value * createCFCSSChecks(
                                    std::vector<int> possible_values,
                                    Instruction * insertBefore, 
                                    Value *last_cftss_id,
                                    const Twine & name = ""
                                )
        {
            std::vector<Value *> res;
            Value *loaded_cftss_id = new LoadInst(last_cftss_id, "", insertBefore);
            FORN(i, sz(possible_values))
            {
                Value *temp = ConstantInt::get(Type::getInt32Ty(context), possible_values[i], false);
                res.pb(CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ, loaded_cftss_id, temp, "", insertBefore));
            }

            Value *reduced_res = createReduction(Instruction::Or, res, insertBefore, name);
            std::vector<Value *> args;
            args.pb(reduced_res);
            // args.pb(ConstantInt::get(Type::getInt32Ty(context), current_basicblock_id, false));
            return CallInst::Create(CFCSSCheckFunction, args, "", insertBefore);
        }
        int get_value_from_map(BasicBlock *bb, std::map<BasicBlock *, int> &bb_id_map)
        {
            if(!bb_id_map[bb])
            {
                db("The basic block does not exist in the map.");
                exit(-1);
            }
            return bb_id_map[bb];
        }
        bool needsToBeChecked (Instruction *I)
        {
            // I->mayReturn() 
            //             && hasOutput(I) 
            //             && !isPhi(I) 
            //             && !isGetElementPtrInst(I) 
            //             && !isCastInst(I)
            //             %% !

            if(!I->mayReturn())
                return false;
            if(!hasOutput(I))
                return false;
            if(isGetElementPtrInst(I))
                return false;
            if(isPhi(I))
                return false;
            if(I->getType()->isPointerTy())
                return false;
            if(isCastInst(I))
                return false;
            if(I->getType()->isVectorTy())
                return false;

            return true;

        }
        void cloneBasicBlock(BasicBlock *bb, Function *F, Module *M, ValueDuplicateMap & map, std::map<BasicBlock *, int> bb_id_map, 
            std::vector< std::pair<Instruction *, Value *> > &toBeReplaced)
        {
            // db(bb->getName());
            std::string bbname = bb->getName();
            Instruction *I; Instruction *NI;
            std::vector<CallInst *> toBeRemoved;
            std::vector<Value *> createdCheckInsts;
            bool previous = false;
            int skip = 0;
            FORE(iter, (*bb))
            {
                // iter->dump();
                if(skip)
                {
                    skip --;
                    continue;
                }
                if(previous)
                {
                    CmpInst *cmp = createCheckInst(I, NI, makeName(I, "_check"), (Instruction *)iter);
                    createdCheckInsts.pb(cmp);
                    previous = false;
                }
                CallInst *call = dyn_cast<CallInst>(iter);
                if (call && !call->isInlineAsm() && prototypeNeedsToBeModified(call->getCalledFunction()))
                {
                    // errs()<<"Replaced call for "<<call->getCalledFunction()<<"\n";
                    modifyCallInstruction(call, map, toBeRemoved);
                }
                else
                if(isCloneable(iter))
                {
                    // iter->dump();
                    I = iter;
                    NI = I->clone();
                    mapOperands(NI, map, toBeReplaced);
                    map[I] = NI;
                    if(I->hasName())
                        NI->setName(makeName(I, "_dup"));
                    NI->insertAfter(I);
                    skip++;

                    if(needsToBeChecked(I))
                            previous = true;
                }
            }
            FORN(i, sz(toBeRemoved))
            {
                CallInst *temp = toBeRemoved[i];
                temp->eraseFromParent();
            }

            if(sz(createdCheckInsts))
            {
                Value * error = createReduction(Instruction::Or, createdCheckInsts, bb->getTerminator(), makeName(bb, "_error"));
                CallInst::Create(EDDICheckFunction, error, "", bb->getTerminator());
            }

        }
        void cloneBlockTree(DomTreeNodeBase<BasicBlock> * root, Function * function, Module *M, 
            ValueDuplicateMap & map, std::map<BasicBlock *, int> bb_id_map, 
            std::vector< std::pair<Instruction *, Value *> > &toBeReplaced)
        {
            cloneBasicBlock(root->getBlock(), function, M, map, bb_id_map, toBeReplaced);
            for each(child, *root)
                cloneBlockTree(*child, function, M, map, bb_id_map, toBeReplaced);
        }

        void mapBasicBlock(BasicBlock *bb, std::map<BasicBlock *, int> &bb_id_map)
        {
            if(bb_id_map[bb])
            {
                db("The basic block has been mapped before.");
                exit(-1);
            }
            bb_id_map[bb] = currentBasicBlock;
            currentBasicBlock++;
        }
        void mapBlockTree(DomTreeNodeBase<BasicBlock> * root, std::map<BasicBlock *, int> &bb_id_map)
        {
            mapBasicBlock(root->getBlock(), bb_id_map);

            for each(child, *root)
                mapBlockTree(*child, bb_id_map);
        }
        std::string int_to_string(int a)
        {
            std::stringstream s;
            s<<a;
            std::string res;
            s>>res;
            return res;
        }
        void trackBasicBlock(BasicBlock *bb, std::map<BasicBlock *, int> &bb_id_map)
        {
            std::vector<Instruction *> cftss_block;
            
            Value *tobestoredval                = ConstantInt::get(Type::getInt32Ty(context), get_value_from_map(bb, bb_id_map), false);

            //Increment N indicating that the number of reached basic blocks is one more.
            Instruction *loaded_cftss_array_n   = new LoadInst(cftss_array_n, "");
            cftss_block.pb(loaded_cftss_array_n);
            Instruction *increment_n            = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_n, one);
            cftss_block.pb(increment_n);
            cftss_block.pb(new StoreInst(increment_n, cftss_array_n));
            
            // Push the new basic block ID into the vector and pop one if necessary.
            Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "");
            cftss_block.pb(loaded_cftss_array_pos);
            Instruction *sext_cftss_array_pos   = new SExtInst(loaded_cftss_array_pos, i64, "");
            cftss_block.pb(sext_cftss_array_pos);
            

            std::vector<Value *> temp;
            temp.pb(i32_zero);
            temp.pb(sext_cftss_array_pos);



            Instruction *get_element_ptr_inst = GetElementPtrInst::CreateInBounds(cftss_array, temp, "");
            cftss_block.pb(get_element_ptr_inst);
            
            Instruction *store_inst           = new StoreInst (tobestoredval, get_element_ptr_inst);
            {
                LLVMContext& C = store_inst->getContext();
                std::string bbid = int_to_string(get_value_from_map(bb, bb_id_map));
                std::string temp = "BasicBlockID-" + bbid;
                MDNode* N = MDNode::get(C, tobestoredval);
                store_inst->setMetadata(temp, N);
            }
            cftss_block.pb(store_inst);
            
            Instruction *increment            = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_pos, one);
            cftss_block.pb(increment);
            
            Instruction *mod_instruction      = BinaryOperator::Create(Instruction::URem, increment, ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY));
            cftss_block.pb(mod_instruction);
            
            Instruction *final_store          = new StoreInst (mod_instruction, cftss_array_pos);
            cftss_block.pb(final_store);



            //TODO: clean up this code.
            Instruction *insertionPoint = bb->getFirstInsertionPt();
            FORN(i, sz(cftss_block))
                cftss_block[i]->insertBefore(insertionPoint);

        }
        void trackBlockTree(DomTreeNodeBase<BasicBlock> * root, std::map<BasicBlock *, int> bb_id_map)
        {

            trackBasicBlock(root->getBlock(), bb_id_map);

            for each(child, *root)
                trackBlockTree(*child, bb_id_map);
        }
        void controlFlowCheckBasicBlock(BasicBlock *bb, Value *last_cftss_id, std::map<BasicBlock *, int> &bb_id_map)
        {
            Value *tobestoredval   = ConstantInt::get(Type::getInt32Ty(context), get_value_from_map(bb, bb_id_map), false);
            BasicBlock::iterator I = bb->begin();
            while (isPhi(I) || I==last_cftss_id) ++I;

            new StoreInst (tobestoredval, last_cftss_id, I);

            std::vector<int> possible_values;
            for (pred_iterator PI = pred_begin(bb), E = pred_end(bb); PI != E; ++PI) 
            {
                BasicBlock *Pred = *PI;
                possible_values.pb(get_value_from_map(Pred, bb_id_map));
            }
            if (sz(possible_values))
            {
                createCFCSSChecks
                    (
                        possible_values, 
                        bb->getFirstInsertionPt(), 
                        last_cftss_id,
                        makeName(bb, "_cfcss_checks")
                    );
            }
        }
        void controlFlowCheckBlockTree(DomTreeNodeBase<BasicBlock> * root, Value *last_cftss_id, std::map<BasicBlock *, int> bb_id_map)
        {
            assert(supportsCFCSS(QEDMode) && "This mode shouldn't use CFCSS");
            controlFlowCheckBasicBlock(root->getBlock(), last_cftss_id, bb_id_map);

            for each(child, *root)
                controlFlowCheckBlockTree(*child, last_cftss_id, bb_id_map);
        }
        void printName(Value *v)
        {
            errs()<<v->getName()<<"\n";
        }


        void mapFunctionBasicBlocks(Function *F, std::map<BasicBlock *, int> &bb_id_map, Module &M)
        {
            DominatorTree & dominator_tree = getAnalysis<DominatorTree>(*F);
            mapBlockTree(dominator_tree.getBase().getRootNode(), bb_id_map);
        }
        void cloneFunction(Function *F, ValueDuplicateMap & global_map, std::map<BasicBlock *, int> &bb_id_map, Module &M)
        {
            //TODO: Can do better than this.
            if(F->getName() == EDDI_CHECK_FUNCTION_NAME || F->getName() == CFCSS_CHECK_FUNCTION_NAME)
                return;

            // db(F->getName());;

            std::vector< std::pair<Instruction *, Value *> > toBeReplaced;
            toBeReplaced.clear();

            DominatorTree & dominator_tree = getAnalysis<DominatorTree>(*F);
            ValueDuplicateMap map;
            map.insert(global_map.begin(), global_map.end());

            // mapBlockTree(dominator_tree.getBase().getRootNode(), bb_id_map);




            //This is EDDI-V essentially.
            if(supportsEDDI(QEDMode))
            {

                // EDDI_V!
                cloneBlockTree(dominator_tree.getBase().getRootNode(), F, &M, map, bb_id_map, toBeReplaced);

                // Phi-Node handler
                FORN(i,sz(toBeReplaced))
                {
                    std::pair<Value *, bool> t = mapValue(toBeReplaced[i].second, map);
                    if(t.second)
                        if(!remapOperand(toBeReplaced[i].first, toBeReplaced[i].second, t.first))
                        {
                            db("Error on Replacing");
                            exit(-1);
                        }
                }

                // Replace the return instructions
                // This has to be done last because you may not have replicated everything if you just replace 
                // the return instruction in cloneBasicBlock
                if (prototypeNeedsToBeModified(F))
                {
                    FORE(iter, (*F))
                    {
                        ReturnInst * ret = dyn_cast<ReturnInst>(iter->getTerminator());
                        if (ret && ret->getReturnValue())
                            muxReturnInst(ret, map);
                    }
                }
            }




            // Start allocating IDs to basic blocks if the user expects CFTSS
            if (supportsCFTSS(QEDMode))
                trackBlockTree(dominator_tree.getBase().getRootNode(), bb_id_map);

            if (supportsCFCSS(QEDMode))
            {
                BasicBlock &entry = F->getEntryBlock();
                Instruction *last_cftss_id = new AllocaInst (Type::getInt32Ty(context), 0, "LAST_CFTSS_ID", entry.getFirstInsertionPt());
                controlFlowCheckBlockTree(dominator_tree.getBase().getRootNode(), last_cftss_id, bb_id_map);
            }

        }
        Constant * createStringConstant(const std::string & string)
        {
            std::vector<Constant *> necklace;
            for each(character, string)
            {
                necklace.push_back(ConstantInt::get(i8, *character));
            }
            necklace.push_back(ConstantInt::get(i8, 0));
            return ConstantArray::get(ArrayType::get(i8, string.size()), necklace);
        }

        // Function * getExternalFunction(StringRef name, FunctionType * type, Module * module)
        // {
        //     module->getOrInsertFunction(name, type);
        //     Function * function = module->getFunction(name);
        //     assert(function);
        //     return function;
        // }

        CallInst * createPrintfCall(Twine format_name, const std::string & format_val,
                                    ArrayRef<Value *> args, BasicBlock * block, Module * module)
        {
            /* Get printf function, adding declaration if needed */
            FunctionType * printf_type = FunctionType::get(i32, PointerType::get(i8, 0), true);
            Function * printf_func = getExternalFunction("printf", printf_type, module);

            /* Add global string constant for format */
            Constant * format_data = createStringConstant(format_val);
            GlobalVariable * format = new GlobalVariable(format_data->getType(), true, GlobalValue::PrivateLinkage,
                                                         format_data, format_name);
            format->setUnnamedAddr(true);
            format->setAlignment(1);
            module->getGlobalList().push_back(format);

            /* Build argument list */
            std::vector<Value *> arg_list;
            Value * zero_zero[] = { i32_zero, i32_zero };
            arg_list.push_back(ConstantExpr::getInBoundsGetElementPtr(format, zero_zero));
            arg_list.insert(arg_list.end(), args.begin(), args.end());

            CallInst * call = CallInst::Create(printf_func, arg_list, "", block);
            call->setDoesNotThrow();
            return call;
        }
        //Unifying code between EDDI_check_function and CFCSS_check_function
        void printLastBasicBlocks(Module& module, Function* checkFunction, LLVMContext& context, BasicBlock* exit_bb,
            std::map<BasicBlock*, int>& bb_id_map)
        {
            Instruction *i_iter = new AllocaInst (Type::getInt32Ty(context), 0, "i", exit_bb);
            new StoreInst(i32_zero, i_iter, exit_bb);

            BasicBlock* cond_bb = llvm::BasicBlock::Create(context, "for.cond", checkFunction);
            BasicBlock* body_bb = llvm::BasicBlock::Create(context, "for.body", checkFunction);
            BasicBlock* inc_bb = llvm::BasicBlock::Create(context, "for.inc", checkFunction);
            BasicBlock* end_bb = llvm::BasicBlock::Create(context, "for.end", checkFunction);

            // Basic Block 3 LLVM IR code:
            // This is where the control gets into if a check fails.
            // We basically want to print all the basic blocks list in this place.

            // exit_block: 
            //     %i = alloca i32, align 4
            //     store i32 0, i32* %i, align 4
            //     br label %for.cond

            // for.cond:                                         ; preds = %for.inc, %entry
            //     %0 = load i32* %i, align 4
            //     %cmp = icmp slt i32 %0, 10
            //     br i1 %cmp, label %for.body, label %for.end

            // for.body:                                         ; preds = %for.cond
            //     %1 = load i32* @temp, align 4
            //     %idxprom = sext i32 %1 to i64
            //     %arrayidx = getelementptr inbounds [100 x i32]* @array, i32 0, i64 %idxprom
            //     %2 = load i32* %arrayidx, align 4
            //     %call = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %2)
//                 %test = icmp i32 %2 0
//                 br exit_bb inc_bb
            //     br label %for.inc

            // for.inc:                                          ; preds = %for.body
            //     %3 = load i32* %i, align 4
            //     %inc = add nsw i32 %3, 1
            //     store i32 %inc, i32* %i, align 4
            //     %4 = load i32* @temp, align 4
            //     %inc1 = add nsw i32 %4, 1
            //     store i32 %inc1, i32* @temp, align 4
            //     %5 = load i32* @temp, align 4
            //     %rem = srem i32 %5, 10
            //     store i32 %rem, i32* @temp, align 4
            //     br label %for.cond

            // for.end:                                          ; preds = %for.cond
            //     call void @exit(i32 1) #2
            //     br label %return_block

            // exit_block:
            {               
                BranchInst::Create(cond_bb, exit_bb);
            }

            // for.cond:
            {
                Instruction *load_i = new LoadInst(i_iter, "", cond_bb);
                Instruction *cmp    = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SLT, load_i, 
                                        ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), "cmp", cond_bb); 
                BranchInst::Create(body_bb, end_bb, cmp, cond_bb);// cond_bb -> body_bb or end_bb
            }

            //for.body:
            {
                Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "", body_bb);
                Instruction *sext_cftss_array_pos   = new SExtInst(loaded_cftss_array_pos, i64, "idxprom", body_bb);

                std::vector<Value*> temp;
                temp.pb(i32_zero);
                temp.pb(sext_cftss_array_pos);

                Instruction *get_element_ptr_inst   = GetElementPtrInst::CreateInBounds(cftss_array, temp, "arrayidx", body_bb);
                Instruction *loaded_array_val       = new LoadInst(get_element_ptr_inst, "", body_bb);

                Instruction *load_i = new LoadInst(i_iter, "", body_bb);
                temp.clear();
                temp.pb(loaded_array_val);
                temp.pb(load_i);
                createPrintfCall("cfcssmessage1", "Basic Block ID = %d\tI = %d\n", temp, body_bb, &module);
                //int main_entry_bb_val = get_value_from_map(&(module.getFunction(StringRef("main"))->getEntryBlock()), bb_id_map);
                //Instruction* cmp_i = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_NE, temp[0],
                //                                ConstantInt::get(i32, 0), "cmp", body_bb);
                //                                  ConstantInt::get(i32, main_entry_bb_val), "cmp", body_bb);
                //How about I just compare i and CFCSS_ARRAY_N?
                //Instruction* load_n = new LoadInst(cftss_array_n, "", body_bb);
                //Instruction* cmp_i = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_SLT, loaded_array_val,
                //                                load_n, "cmp", body_bb);
                //BranchInst::Create(inc_bb, end_bb, cmp_i, body_bb);
                BranchInst::Create(inc_bb, body_bb);
            }

            //for.inc:
            {
                Instruction *load_i                 = new LoadInst(i_iter, "", inc_bb);
                Instruction *increment              = BinaryOperator::Create(Instruction::Add, load_i, one, "inc", inc_bb);
                new StoreInst(increment, i_iter, inc_bb);
                Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "", inc_bb);
                Value* toAdd                        = ConstantInt::get(Type::getInt32Ty(context), NUM_ELEMENTS_IN_CFTSS_ARRAY - 1);
                //Instead of decrementing 1 and adding 10, it's easier to just add 9.
                //Added 10 because urem computes remainder by converting to an unsigned int, which causes undesirable
                // behavior, so it's easier to just deal with a positive number.
                Instruction *decrement              = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_pos, toAdd, "dec1", inc_bb);
                Instruction *mod_instruction        = BinaryOperator::Create(Instruction::URem, decrement, 
                                                    ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), "rem", inc_bb);
                new StoreInst(mod_instruction, cftss_array_pos, inc_bb);
                BranchInst::Create(cond_bb, inc_bb);
            }
            //for.end:
            {
                createExitCall(one, end_bb, &module);
                BranchInst::Create(exit_bb, end_bb); //Should this be the return block instead?
            }
        }

        void createEDDICheckFunction(Module &module, std::map<BasicBlock*, int>& bb_id_map)
        {
            assert(supportsEDDI(QEDMode));

            std::vector<Type*> Params;
            std::vector<Value *> temp;


            Params.pb(Type::getInt1Ty(context));

            llvm::FunctionType* ftype = llvm::FunctionType::get(Type::getVoidTy(context), Params, false);
            module.getOrInsertFunction(EDDI_CHECK_FUNCTION_NAME, ftype);

            EDDICheckFunction = module.getFunction(EDDI_CHECK_FUNCTION_NAME);
            Argument *check_value = &EDDICheckFunction->getArgumentList().front();
            
            BasicBlock *entry = llvm::BasicBlock::Create(context, "entry", EDDICheckFunction);
            BasicBlock* bb1   = llvm::BasicBlock::Create(context, "check_block", EDDICheckFunction);
            BasicBlock* bb2   = llvm::BasicBlock::Create(context, "return_block", EDDICheckFunction);
            BasicBlock* bb3   = llvm::BasicBlock::Create(context, "exit_block", EDDICheckFunction);

            //entry:
            {
                BasicBlock *currentBasicBlock = entry;
                BranchInst::Create(bb1, currentBasicBlock);
            }
            // check_block:
            {
                BranchInst::Create(bb3, bb2, check_value, bb1); // BB1->BB2 or BB3
            }

            // return_block:                                     ; preds = %for.end, %check_block
            //     ret void

            // return_block:
                ReturnInst::Create(context, 0, bb2);

            // exit_block:
                std::vector<Value *> v; v.clear();
                createPrintfCall("eddimessage1", "EDDI Failed.\n", v, bb3, &module);

            // If CFTSS is supported, we can print the last N basic blocks that got executed
            if(supportsCFTSS(QEDMode))
            {
                Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "", bb3);
                Instruction *decrement              = BinaryOperator::Create(Instruction::Sub, loaded_cftss_array_pos, one, "dec", bb3);
                Instruction *mod_instruction        = BinaryOperator::Create(Instruction::URem, decrement, 
                                                    ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), "rem", bb3);
                new StoreInst(mod_instruction, cftss_array_pos, bb3);
                printLastBasicBlocks(module, EDDICheckFunction, context, bb3, bb_id_map);
            }
            else
            {
                createExitCall(one, bb3, &module);
                BranchInst::Create(bb2, bb3);
            }
        }
        void createCFCSSCheckFunction(Module &module, std::map<BasicBlock*, int>& bb_id_map)
        {
            assert (supportsCFCSS(CFCSS) && "CFCSS Check Function shouldn't be created");

            std::vector<Type*> Params;
            std::vector<Value *> temp;

            Params.pb(Type::getInt1Ty(context));

            llvm::FunctionType* ftype = llvm::FunctionType::get(Type::getVoidTy(context), Params, false);
            module.getOrInsertFunction(CFCSS_CHECK_FUNCTION_NAME, ftype);

            CFCSSCheckFunction = module.getFunction(CFCSS_CHECK_FUNCTION_NAME);

            std::vector<Argument *> arg_list;
            for each_custom(arg, *CFCSSCheckFunction, arg_begin, arg_end)
                arg_list.push_back(arg);
            
            BasicBlock* bb1 = llvm::BasicBlock::Create(context, "check_block", CFCSSCheckFunction);
            BasicBlock* bb2 = llvm::BasicBlock::Create(context, "return_block", CFCSSCheckFunction);
            BasicBlock* bb3 = llvm::BasicBlock::Create(context, "exit_block", CFCSSCheckFunction);

            BranchInst::Create(bb2, bb3, arg_list[0], bb1); // BB1->BB2 or BB3

            // return_block:                                     ; preds = %for.end, %check_block
            //     ret void

            // return_block:
                ReturnInst::Create(context, 0, bb2);

            //exit_block:
            std::vector<Value*> empty_vec;
            createPrintfCall("cfcss_error_msg", "CFCSS Failed.\n", empty_vec, bb3, &module);
            printLastBasicBlocks(module, CFCSSCheckFunction, context, bb3, bb_id_map);
        }
        ArrayType *getArrayType(Type *t, int N)
        {
            return ArrayType::get(t, N);
        }
        bool canCloneFunction(Function *F)
        {
            if(F->getName() == EDDI_CHECK_FUNCTION_NAME)
                return false;
            if(F->getName() == CFCSS_CHECK_FUNCTION_NAME)
                return false;
            return true;
        }
 
        std::vector<int> returnCallers(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            std::vector<int> res;
            for each_custom(iter, *F, use_begin, use_end)
            {
                CallInst* caller = dyn_cast<CallInst>(*iter);
                if (caller) res.pb(get_value_from_map(caller->getParent(), bb_id_map));
            }
            return res;
        }
        void insertStoresBeforeCalls(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            for each_custom(iter, *F, use_begin, use_end)
            {
                CallSite CS(*iter);
                Instruction *Call = CS.getInstruction();
                //CallInst* Call = dyn_cast<CallInst>(*iter);
                if(Call)
                {
                    //So this method isn't finding indirect calls... what?
                    //if (!Call->getCalledFunction()) printf("Indirect call detected.\n");
                    //else printf("Direct call detected.\n");
                    int bbid             = get_value_from_map(Call->getParent(), bb_id_map);
                    Value *tobestoredval = ConstantInt::get(i32, bbid, false);
                    new StoreInst(tobestoredval, global_cfcss_id, Call);
                } /*else {
                    printf("Indirect call to %s.\n", F->getName().data());
                }*/
            }
        }
        std::vector<int> returnExits(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            std::vector<int> res;
            FORE(iter, (*F))
            {
                ReturnInst * ret = dyn_cast<ReturnInst>(iter->getTerminator());
                if (ret && ret->getReturnValue() && ret->getParent()!=NULL && bb_id_map[ret->getParent()])
                    res.pb(get_value_from_map(ret->getParent(), bb_id_map));
            }
            return res;
        }

        void insertStoresBeforeExits(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            FORE(iter, (*F))
            {
                ReturnInst * ret = dyn_cast<ReturnInst>(iter->getTerminator());
                if (ret && ret->getReturnValue() && ret->getParent()!=NULL && bb_id_map[ret->getParent()])
                {
                    int bbid = get_value_from_map(ret->getParent(), bb_id_map);
                    Value *tobestoredval = ConstantInt::get(i32, bbid, false);
                    new StoreInst(tobestoredval, global_cfcss_id, ret);
                }
            }
        }
        void insertChecksAfterCalls(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            std::vector<int> exitBasicBlocks = returnExits(F, bb_id_map);
            for each_custom(iter, *F, use_begin, use_end)
            {
                CallSite CS(*iter);
                Instruction *Call = CS.getInstruction();
                Instruction *nextInstruction = getNextInstruction(Call);
                if(nextInstruction && Call && sz(exitBasicBlocks))
                {
                    createCFCSSChecks 
                        (                                
                            exitBasicBlocks,    // std::vector<int> possible_values,
                            nextInstruction,    // Instruction * insertBefore,
                            global_cfcss_id,    // Value *last_cftss_id,
                            "exit_cfcss_checks" // const Twine & name = ""
                        );
                }
            }
        }
        bool runOnModule(Module &M)
        {
            currentBasicBlock = 1;
            ValueDuplicateMap map;
            cloneGlobalVariables(M, map);

            if (supportsCFTSS(QEDMode))
            {
                std::vector<Constant *> temp;
                FORN(i, NUM_ELEMENTS_IN_CFTSS_ARRAY)
                    temp.pb(i32_zero);

                cftss_array     = new GlobalVariable (
                                                M, 
                                                getArrayType(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), 
                                                false, 
                                                GlobalValue::PrivateLinkage, 
                                                ConstantArray::get(getArrayType(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), temp), 
                                                "CFTSS_ARRAY"
                                            );
                cftss_array_pos = new GlobalVariable (
                                                M, 
                                                i32, 
                                                false, 
                                                GlobalValue::PrivateLinkage, 
                                                i32_zero, 
                                                "CFTSS_ARRAY_POS"
                                            );
                cftss_array_n   = new GlobalVariable (
                                                M, 
                                                i32, 
                                                false, 
                                                GlobalValue::PrivateLinkage, 
                                                i32_zero, 
                                                "CFTSS_ARRAY_N"
                                            );
                global_cfcss_id = new GlobalVariable (
                                                M, 
                                                i32, 
                                                false, 
                                                GlobalValue::PrivateLinkage, 
                                                i32_zero,
                                                "GLOBAL_CFCSS_ID"
                                            );
                // cftss_id->setThreadLocal(true);
            }

            std::map<BasicBlock *, int> bb_id_map;
            FORE(iter, M)
                if (!((*iter).isDeclaration()) && canCloneFunction(iter))
                    mapFunctionBasicBlocks(iter, bb_id_map, M);

            if (supportsEDDI(QEDMode))
                createEDDICheckFunction(M, bb_id_map);

            if (supportsCFCSS(QEDMode))
                createCFCSSCheckFunction(M, bb_id_map);


            if (supportsEDDI(QEDMode))
            {
                FORE(iter, M)
                    if(!((*iter).isDeclaration()) && prototypeNeedsToBeModified(iter))
                    {
                        modifyPrototype(iter,map);
                    }
            }

            // Iterate over all the functions and clone them
            FORE(iter, M)
                if (!((*iter).isDeclaration()) && canCloneFunction(iter))
                    cloneFunction(iter, map, bb_id_map, M);

            if (supportsCFCSS(QEDMode))
                FORE(iter, M)
                    if (!((*iter).isDeclaration()) && canCloneFunction(iter))
                    {
                        Function *F = iter;
                        if (!strcmp(F->getName().data(), "main")) continue;
                        std::vector<int> callers = returnCallers(iter, bb_id_map);
                        //Here's where it matters that the callers might be indirect...?
                        if(sz(callers))
                            createCFCSSChecks 
                                (                                
                                    callers,                                       // std::vector<int> possible_values,
                                    F->getEntryBlock().getFirstInsertionPt(),      // Instruction * insertBefore,
                                    global_cfcss_id,                               // Value *last_cftss_id,
                                    makeName(&F->getEntryBlock(), "_cfcss_checks") // const Twine & name = ""
                                );

                    insertStoresBeforeCalls (F, bb_id_map);
                    insertStoresBeforeExits (F, bb_id_map);
                    insertChecksAfterCalls  (F, bb_id_map);     
                }

            return true;            
        }
        void getAnalysisUsage(AnalysisUsage & info) const
        {
            info.addRequired<DominatorTree>();
        }
    };
}
char QED::ID = 0;
static RegisterPass<QED> X("hello", "Hello World Pass");

