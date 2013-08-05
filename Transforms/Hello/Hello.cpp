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
    EDDI        = 0x1,
    CFTSS       = 0x2,
    CFCSS       = 0x4,
    GlobalCFCSS = 0x8,
    Track_N     = 0x10
};

// Some Command Line Arguments will be parsed here
// static cl::opt<QEDLevel> QEDMode 
// (
//     "QED-Mode", 
//     cl::init(ALL), 
//     cl::desc("Choose QED Mode:"),
//     cl::value_desc("QED Mode"),
//     cl::values
//     (
//         clEnumVal(EDDI , "Enable EDDI Transformations"),
//         clEnumVal(CFTSS, "Enable CFTSS Transformations"),
//         clEnumVal(EDDIANDCFTSS, "Enable both EDDI and CFTSS Transformations"),
//         clEnumVal(CFCSS, "Enable CFCSS Transformations"),
//         clEnumVal(ALL,   "Enable All Transformations"),
//         clEnumValEnd
//     )
// );

static cl::opt<int> QEDMode
(
    "QED-Mode",
    cl::init(EDDI),
    cl::desc("Bit 1 = EDDI, Bit 2 = CFTSS, Bit 3 = CFCSS, Bit 4 = GlobalCFCSS, Bit 5 = Store number of blocks seen")
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
        Value             * one;
        LLVMContext       & context;
        IntegerType       * i1;
        IntegerType       * i8;
        IntegerType       * i32;
        IntegerType       * i64;
        ConstantInt       * i1_true;
        ConstantInt       * i1_false;
        ConstantInt       * i32_zero;
        int currentBasicBlock;
        // int NUM_ELEMENTS_IN_CFTSS_ARRAY;


        // GlobalVariable * last_cftss_id;
        GlobalVariable    * cftss_array;
        GlobalVariable    * cftss_array_pos;
        GlobalVariable    * cftss_array_n;
        GlobalVariable    * global_cfcss_id;

        //This is only used if NUM_CFTSS_BBS = 1, so as to avoid using the array above.
        GlobalVariable    * last_bb_id; 

        Function          * EDDICheckFunction;
        std::string EDDI_CHECK_FUNCTION_NAME;

        Function          * CFCSSCheckFunction;
        std::string CFCSS_CHECK_FUNCTION_NAME;

        Function          * ErrorReportingFn;
        std::string ERROR_REPORTER_NAME;

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
            ERROR_REPORTER_NAME       = "error_detected";

            assert ( (QEDMode<32) && "QED Mode cannot be greater than 31. Each bit represents one \
                option and there are only five options to choose.");

            // errs()<<"\n";
            // if(supportsEDDI(QEDMode))
            //     errs()<<"EDDI\n";

            // if(supportsCFTSS(QEDMode))
            //     errs()<<"CFTSS\n";

            // if(supportsCFCSS(QEDMode))
            //     errs()<<"CFCSS\n";

            // if(supportsGlobalCFCSS(QEDMode))
            //     errs()<<"GlobalCFCSS\n";

            // db(NUM_CFTSS_BB);
            // NUM_ELEMENTS_IN_CFTSS_ARRAY = NUM_CFTSS_BB;
            // db(NUM_ELEMENTS_IN_CFTSS_ARRAY);
        }
        bool supportsEDDI(int QEDMode)
        {
            return QEDMode & EDDI;
        }
        bool supportsCFTSS(int QEDMode)
        {
            return QEDMode & CFTSS;
        }
        bool supportsCFCSS(int QEDMode)
        {
            return QEDMode & CFCSS;
        }
        bool supportsGlobalCFCSS(int QEDMode)
        {
            return QEDMode & GlobalCFCSS;
        }
        bool supportsNumBlocks(int QEDMode)
        {
            return QEDMode & Track_N;
        }
        bool prototypeNeedsToBeModified(Function *F)
        {
            // db(F->getName());
            return  F!=NULL
                    && (!F->getBasicBlockList().empty() && F->size())
                    && F->getName().compare("main") 
                    && (F->getName().find("entry_point")==StringRef::npos)
                    && F->getName().compare(EDDI_CHECK_FUNCTION_NAME)
                    && F->getName().compare(CFCSS_CHECK_FUNCTION_NAME)
                    && F->getName().compare(ERROR_REPORTER_NAME);
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
            CmpInst::Predicate predicate = float_type ? CmpInst::FCMP_OEQ : CmpInst::ICMP_EQ;
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
        void createCFCSSChecks(
                                    std::vector<int> possible_values,
                                    Instruction * insertBefore, 
                                    Value *last_cftss_id,
                                    std::map<BasicBlock*, int> bb_id_map,
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
            #if 0
            BasicBlock* bb = insertBefore->getParent();
            // Trying to make CFCSS checks faster. First issue: there may be multiple checks per block. Each needs
            // unique IDs...
            /*  br reduced_res fail, pass 
                    (name_of_block_)cfcss_fail:
                        call ErrorReportingFn
                        br cfcss_pass
                    (name_of_block_)cfcss_pass:
                        (continue)
            */
            BasicBlock* passBlock = bb->splitBasicBlock(insertBefore, std::string("cfcss_pass"));
            BasicBlock* failBlock = BasicBlock::Create(context, std::string("cfcss_fail"), bb->getParent(), passBlock);
            std::vector<Value*> args;
            //TODO this creates extra copies. I will want to fix that!
            createPrintfCall("cfcssmessage1", "CFCSS Failed.\n", args, failBlock, bb->getParent()->getParent());
            if (supportsCFTSS(QEDMode))
            {
                CallInst::Create(ErrorReportingFn, args, "", failBlock);
            } else { //in which case we don't have the error-reporting function.
                createExitCall(one, failBlock, bb->getParent()->getParent());
            }
            BranchInst::Create(failBlock, failBlock); //never reached, but necessary for correctness
            //Note: ^^ isn't quite parallel with EDDI, and when factored use this one.
            bb->getTerminator()->eraseFromParent();
            BranchInst::Create(passBlock, failBlock, reduced_res, bb);

            //I think this is necessary for CFCSS to work properly.
            int id = get_value_from_map(bb, bb_id_map);
            //bb_id_map[passBlock] = id;
            //bb_id_map->insert(std::make_pair<BasicBlock*, int>(passBlock, id)); //if this is a pass-by-reference bug I will be angry
            bb_id_map[passBlock] = id;
            /*printf("Just inserted %s.%s into the map: value %d.\n", passBlock->getParent()->getName().data(),
                                                          passBlock->getName().data(),
                                                          get_value_from_map(passBlock, bb_id_map));
            */
            #endif
            std::vector<Value *> args;
            args.pb(reduced_res);
            // args.pb(ConstantInt::get(Type::getInt32Ty(context), current_basicblock_id, false));
            CallInst* toReturn = CallInst::Create(CFCSSCheckFunction, args, "", insertBefore);
            toReturn->setCallingConv(CallingConv::Fast);
            //return toReturn;
        }
        int get_value_from_map(BasicBlock *bb, std::map<BasicBlock *, int> &bb_id_map)
        {
            if(!bb_id_map[bb])
            {
                printf("Coudn't find basic block %s.%s in the map.\n", bb->getParent()->getName().data(), bb->getName().data());
                for(std::map<BasicBlock*, int>::iterator i = bb_id_map.begin(); i != bb_id_map.end(); i++) {
                    printf("\t%s.%s -> %d.\n", i->first->getParent()->getName().data(),i->first->getName().data(), i->second);
                }
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
            if (bb->getName().endswith("_pass") || bb->getName().endswith("_fail") || bb->getName().startswith("cfcss_"))
                return; //TODO factor
            //printf("Cloning %s.%s.\n", bb->getParent()->getName().data(), bb->getName().data());
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
                    modifyCallInstruction(call, map, toBeRemoved); //<-- this is where the problem is!
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
                Value * error = createReduction(Instruction::And, createdCheckInsts, bb->getTerminator(), makeName(bb, "_error"));
                /*  br error fail, pass 
                    (name_of_block_)fail:
                        call ErrorReportingFn
                        br pass
                    (name_of_block_)pass:
                        br (wherever it goes) -- it would be nice to optimize this.

                I might also be able to unify the code somewhat.
                 */   
                    BasicBlock* passBlock = bb->splitBasicBlock(bb->getTerminator(), bb->getName() + std::string("_pass"));
                    BasicBlock* failBlock = BasicBlock::Create(context, bb->getName() + std::string("_fail"), bb->getParent(), passBlock);
                    std::vector<Value*> args;
                    //TODO this creates extra copies. I will want to fix that!
                    createPrintfCall("eddimessage1", "EDDI Failed.\n", args, failBlock, M);
                    /*
                        ...where format is the GlobalVariable* that I already have
                        std::vector<Value *> arg_list;
                        Value * zero_zero[] = { i32_zero, i32_zero };
                        arg_list.push_back(ConstantExpr::getInBoundsGetElementPtr(format, zero_zero));
                        arg_list.insert(arg_list.end(), args.begin(), args.end());

                        CallInst * call = CallInst::Create(printf_func, arg_list, "", block);
                        call->setDoesNotThrow();
                      */
                    if (supportsCFTSS(QEDMode))
                    {
                        CallInst::Create(ErrorReportingFn, args, "", failBlock);
                    } else { //in which case we don't have the error-reporting function.
                        createExitCall(one, failBlock, M);
                    }
                    BranchInst::Create(failBlock, failBlock); //never reached, but necessary for correctness
                    bb->getTerminator()->eraseFromParent();
                    BranchInst::Create(passBlock, failBlock, error, bb);
                /*
                CallInst* eddi_call = CallInst::Create(EDDICheckFunction, error, "", bb->getTerminator());
                eddi_call->setCallingConv(CallingConv::Fast);
                */
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
        Instruction* storeID(BasicBlock* bb, Value* tobestoredval, Value* tostorein, std::map<BasicBlock*, int>& bb_id_map)
        {
            Instruction *store_inst = new StoreInst (tobestoredval, tostorein);
            {
                LLVMContext& C = store_inst->getContext();
                std::string bbid = int_to_string(get_value_from_map(bb, bb_id_map));
                std::string temp = "BasicBlockID-" + bbid;
                MDNode* N = MDNode::get(C, tobestoredval);
                store_inst->setMetadata(temp, N);
            }
            return store_inst;
        }
        void trackBasicBlock(BasicBlock *bb, std::map<BasicBlock *, int> &bb_id_map)
        {
            if (bb->getName().endswith("_pass") || bb->getName().endswith("_fail"))
            {
                return;
            } 
            std::vector<Instruction *> cftss_block;
            
            Value *tobestoredval                = ConstantInt::get(Type::getInt32Ty(context), get_value_from_map(bb, bb_id_map), false);

            //Increment N indicating that the number of reached basic blocks is one more.
            if (supportsNumBlocks(QEDMode))
            { 
                Instruction *loaded_cftss_array_n   = new LoadInst(cftss_array_n, "");
                cftss_block.pb(loaded_cftss_array_n);
                Instruction *increment_n            = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_n, one);
                cftss_block.pb(increment_n);
                cftss_block.pb(new StoreInst(increment_n, cftss_array_n));
            }
            if (NUM_ELEMENTS_IN_CFTSS_ARRAY > 1)
            {
            
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
            
                cftss_block.pb(storeID(bb, tobestoredval, get_element_ptr_inst, bb_id_map));
                Instruction *increment            = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_pos, one);
                cftss_block.pb(increment);
            
                Instruction *mod_instruction      = BinaryOperator::Create(Instruction::URem, increment, ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY));
                cftss_block.pb(mod_instruction);
            
                Instruction *final_store          = new StoreInst (mod_instruction, cftss_array_pos);
                cftss_block.pb(final_store);
            } else { //otherwise, it's not necessary to update the array
                cftss_block.pb(storeID(bb, tobestoredval, last_bb_id, bb_id_map));
            }

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
            if (bb->getName().endswith("_pass") || bb->getName().endswith("_fail") || bb->getName().startswith("cfcss_"))
            {
                return; //TODO factor out and check that it's necessary
            }
            Value *tobestoredval   = ConstantInt::get(Type::getInt32Ty(context), get_value_from_map(bb, bb_id_map), false);
            BasicBlock::iterator I = bb->begin();
            while (isPhi(I) || I==last_cftss_id) ++I;

            new StoreInst (tobestoredval, last_cftss_id, I);

            std::vector<int> possible_values;
            //AHA! Here I want to take every 'pass' predicate and replace it with _its_ non-fail predicate.
            for (pred_iterator PI = pred_begin(bb), E = pred_end(bb); PI != E; ++PI) 
            {
                BasicBlock *Pred = *PI;
                if (Pred->getName().startswith("cfcss_")) //CFCSS pass block: we need prerequisites
                {
                    BasicBlock* passPred = *pred_begin(Pred); //there's only the one prereq
                    possible_values.pb(get_value_from_map(passPred, bb_id_map));
                }
                //TODO else?
                else if (!(Pred->getName().endswith("_pass") || Pred->getName().endswith("_fail"))) //not clear if this exists yet
                {
                    possible_values.pb(get_value_from_map(Pred, bb_id_map));
                }
            }
            if (sz(possible_values))
            {
                createCFCSSChecks
                    (
                        possible_values, 
                        bb->getFirstInsertionPt(), 
                        last_cftss_id,
                        bb_id_map,
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


            // Start allocating IDs to basic blocks if the user expects CFTSS
            if (supportsCFTSS(QEDMode))
                trackBlockTree(dominator_tree.getBase().getRootNode(), bb_id_map);

            if (supportsCFCSS(QEDMode))
            {
                BasicBlock &entry = F->getEntryBlock();
                Instruction *last_cftss_id = new AllocaInst (Type::getInt32Ty(context), 0, "LAST_CFTSS_ID", entry.getFirstInsertionPt());
                controlFlowCheckBlockTree(dominator_tree.getBase().getRootNode(), last_cftss_id, bb_id_map);
            }

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
        //Unifying code between the two check functions.
        //Creates the basic blocks that test whether the check passes.
        //These blocks are called a lot in the program and would be a good place for optimizations.
        void createCheckBlocks(Module& module, Function** checkFunction, std::string& fnName, const char* error_name, const char* error_msg)
        {

            std::vector<Type*> Params;
            std::vector<Value *> temp;

            Params.pb(Type::getInt1Ty(context));

            llvm::FunctionType* ftype = llvm::FunctionType::get(Type::getVoidTy(context), Params, false);
            module.getOrInsertFunction(fnName, ftype);

            *checkFunction = module.getFunction(fnName);
            (*checkFunction)->setCallingConv(CallingConv::Fast);
            Argument *check_value = &(*checkFunction)->getArgumentList().front();

            BasicBlock* entry = llvm::BasicBlock::Create(context, "entry", *checkFunction);
            BasicBlock* bb2   = llvm::BasicBlock::Create(context, "return_block", *checkFunction);
            BasicBlock* bb3   = llvm::BasicBlock::Create(context, "exit_block", *checkFunction);

            // entry_block:
            {
                BranchInst::Create(bb2, bb3, check_value, entry);
            }

            // return_block:                                     ; preds = %for.end, %check_block
            //     ret void

            // return_block:
                ReturnInst::Create(context, 0, bb2);

            // exit_block:
            {
                std::vector<Value*> empty_vec;
                createPrintfCall(error_name, error_msg, empty_vec, bb3, &module);
            }

            if(supportsCFTSS(QEDMode))
            {
                //This prints a stack trace of basic blocks for the failed check.
                //printLastBasicBlocks(module, *checkFunction, context, bb3, bb2);
                if (NUM_ELEMENTS_IN_CFTSS_ARRAY == 1)
                {
                    Instruction *loaded_bb_val = new LoadInst(last_bb_id, "", bb3);
                    Value* temp[1];
                    temp[0] = loaded_bb_val;
                    createPrintfCall("cfcssmessage1", "Basic Block ID = %d\n", temp, bb3, &module);
                    createExitCall(one, bb3, &module);
                } else {
                    // Otherwise, branch to the exit function. This will unify code between the EDDI and CFCSS modes and allow
                    // for EDDI to be more easily elided into the function bodies, rather than as an expensive call.
                    std::vector<Value*> args;
                    CallInst::Create(ErrorReportingFn, args, "", bb3);
                }
                BranchInst::Create(bb2, bb3);
            }
            else
            {
                createExitCall(one, bb3, &module);
                BranchInst::Create(bb2, bb3);
            }
        }

        void createErrorReportingFunction(Module& module)
        {
            //Start by creating the function itself.
            std::vector<Type*> Params;
            llvm::FunctionType* ftype = llvm::FunctionType::get(Type::getVoidTy(context), Params, false);
            module.getOrInsertFunction(ERROR_REPORTER_NAME, ftype);
            ErrorReportingFn = module.getFunction(ERROR_REPORTER_NAME);
            //it remains to be seen if this is the smartest way through. But it makes sense
            BasicBlock* entry_bb = llvm::BasicBlock::Create(context, "entry", ErrorReportingFn);
            Instruction *i_iter = new AllocaInst (Type::getInt32Ty(context), 0, "i", entry_bb);
            new StoreInst(i32_zero, i_iter, entry_bb);

            BasicBlock* cond_bb = llvm::BasicBlock::Create(context, "for.cond", ErrorReportingFn);
            BasicBlock* body_bb = llvm::BasicBlock::Create(context, "for.body", ErrorReportingFn);
            BasicBlock* inc_bb = llvm::BasicBlock::Create(context, "for.inc", ErrorReportingFn);
            BasicBlock* end_bb = llvm::BasicBlock::Create(context, "for.end", ErrorReportingFn);

            // Basic Block 3 LLVM IR code:
            // This is where the control gets into if a check fails.
            // We basically want to print all the basic blocks list in this place.

            // If only one value is tracked, this is different, as there is just a single value,
            // rather than an array. Then, that value is printed, and the program exits.

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
                //Thanks to an off-by-one error, it's necessary to decrement first
                Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "", entry_bb);
                Value* toAdd                        = ConstantInt::get(Type::getInt32Ty(context), NUM_ELEMENTS_IN_CFTSS_ARRAY - 1);
                Instruction *decrement              = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_pos, toAdd, "dec1", entry_bb);
                Instruction *mod_instruction        = BinaryOperator::Create(Instruction::URem, decrement, 
                                                        ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), "rem", entry_bb);
                new StoreInst(mod_instruction, cftss_array_pos, entry_bb);  
                BranchInst::Create(cond_bb, entry_bb);
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
                BranchInst::Create(inc_bb, body_bb);
            }

            //for.inc:
            {
                Instruction *load_i                 = new LoadInst(i_iter, "", inc_bb);
                Instruction *increment              = BinaryOperator::Create(Instruction::Add, load_i, one, "inc", inc_bb);
                new StoreInst(increment, i_iter, inc_bb);
                if (NUM_ELEMENTS_IN_CFTSS_ARRAY > 1)
                {
                    Instruction *loaded_cftss_array_pos = new LoadInst(cftss_array_pos, "", inc_bb);
                    Value* toAdd                        = ConstantInt::get(Type::getInt32Ty(context), NUM_ELEMENTS_IN_CFTSS_ARRAY - 1);
                    //Instead of decrementing 1 and adding N, it's easier to just add N-1.
                    //Added N because urem computes remainder by converting to an unsigned int, which causes undesirable
                    // behavior, so it's easier to just deal with a positive number.
                    Instruction *decrement              = BinaryOperator::Create(Instruction::Add, loaded_cftss_array_pos, toAdd, "dec1", inc_bb);
                    Instruction *mod_instruction        = BinaryOperator::Create(Instruction::URem, decrement, 
                                                        ConstantInt::get(i32, NUM_ELEMENTS_IN_CFTSS_ARRAY), "rem", inc_bb);
                    new StoreInst(mod_instruction, cftss_array_pos, inc_bb);
                }
                BranchInst::Create(cond_bb, inc_bb);
            }
            //for.end:
            {
                createExitCall(one, end_bb, &module);
                ReturnInst::Create(context, 0, end_bb);
            }
        }

        void createCFCSSCheckFunction(Module &module)
        {
            assert (supportsCFCSS(CFCSS) && "CFCSS Check Function shouldn't be created");
            createCheckBlocks(module, &CFCSSCheckFunction, CFCSS_CHECK_FUNCTION_NAME, "cfcss_error_msg", "CFCSS Failed.\n");
        }
        int valueWrapper(BasicBlock* bb, std::map<BasicBlock*, int>& bb_id_map) {
            if (bb->getName().startswith("cfcss_") || bb->getName().endswith("_pass"))
            {
                BasicBlock* passPred = *pred_begin(bb); //there's only the one prereq
                if (passPred->getName().endswith("_pass")) passPred = *pred_begin(passPred);
                //TODO write this down and check that it makes sense.
                //printf("Called by %s <- %s.\n", caller->getParent()->getName().data(),
                //    passPred->getName().data());
                return get_value_from_map(passPred, bb_id_map);
            } else {
                //printf("Called by %s.\n", caller->getParent()->getName().data());
                return get_value_from_map(bb, bb_id_map);
            }
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
            if(F->getName() == ERROR_REPORTER_NAME) return false;
            return true;
        }
 
        std::vector<int> returnCallers(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            std::vector<int> res;
            for each_custom(iter, *F, use_begin, use_end)
            {
                CallInst* caller = dyn_cast<CallInst>(*iter);
                if (caller) {
                    if (caller->getParent()->getName().startswith("cfcss_") || caller->getParent()->getName().endswith("_pass"))
                    {
                        BasicBlock* passPred = *pred_begin(caller->getParent()); //there's only the one prereq
                        if (passPred->getName().endswith("_pass")) passPred = *pred_begin(passPred);
                        //TODO write this down and check that it makes sense.
                        //printf("Called by %s <- %s.\n", caller->getParent()->getName().data(),
                        //    passPred->getName().data());
                        res.pb(get_value_from_map(passPred, bb_id_map));
                    } else {
                        //printf("Called by %s.\n", caller->getParent()->getName().data());
                        res.pb(get_value_from_map(caller->getParent(), bb_id_map));
                    }
                }
            }
            return res;
        }
        void insertStoresBeforeCalls(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            for each_custom(iter, *F, use_begin, use_end)
            {
                CallSite CS(*iter);
                Instruction *Call = CS.getInstruction();
                if(Call)
                {
                    int bbid             = valueWrapper(Call->getParent(), bb_id_map);//get_value_from_map(Call->getParent(), bb_id_map);
                    Value *tobestoredval = ConstantInt::get(i32, bbid, false);
                    new StoreInst(tobestoredval, global_cfcss_id, Call);
                }
            }
        }
        std::vector<int> returnExits(Function *F, std::map<BasicBlock *, int> bb_id_map)
        {
            std::vector<int> res;
            FORE(iter, (*F))
            {
                ReturnInst * ret = dyn_cast<ReturnInst>(iter->getTerminator());
                if (ret && ret->getReturnValue() && ret->getParent()!=NULL && bb_id_map[ret->getParent()])
                    //res.pb(get_value_from_map(ret->getParent(), bb_id_map));
                    res.pb(valueWrapper(ret->getParent(), bb_id_map));
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
                    //int bbid = get_value_from_map(ret->getParent(), bb_id_map);
                    int bbid = valueWrapper(ret->getParent(), bb_id_map);
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
                            bb_id_map,          // std::map<BasicBlock*, int>& bb_id_map,
                            "exit_cfcss_checks" // const Twine & name = ""
                        );
                }
            }
        }
        bool runOnModule(Module &M)
        {
            currentBasicBlock = 1;
            ValueDuplicateMap map;

            if (supportsEDDI(QEDMode))
                cloneGlobalVariables(M, map);

            if (supportsCFTSS(QEDMode))
            {
                if (NUM_ELEMENTS_IN_CFTSS_ARRAY > 1)
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
                } else { //in which case we only need the one ID
                    last_bb_id      = new GlobalVariable(
                                                    M,
                                                    i32,
                                                    false,
                                                    GlobalValue::PrivateLinkage,
                                                    i32_zero,
                                                    "LAST_BB_ID"
                                                );
                }
                if (supportsNumBlocks(QEDMode))
                {
                    cftss_array_n   = new GlobalVariable (
                                                    M, 
                                                    i32, 
                                                    false, 
                                                    GlobalValue::PrivateLinkage, 
                                                    i32_zero, 
                                                    "CFTSS_ARRAY_N"
                                                );
                }
            }
            if(supportsGlobalCFCSS(QEDMode))
            {
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
            {
                FORE(iter, M)
                    if(!((*iter).isDeclaration()) && prototypeNeedsToBeModified(iter))
                    {
                        modifyPrototype(iter,map);
                    }
            }

            if (supportsCFTSS(QEDMode))
                createErrorReportingFunction(M);

            if (supportsCFCSS(QEDMode) || supportsGlobalCFCSS(QEDMode))
                createCFCSSCheckFunction(M);


            

            // Iterate over all the functions and clone them
            FORE(iter, M)
                if (!((*iter).isDeclaration()) && canCloneFunction(iter))
                    cloneFunction(iter, map, bb_id_map, M);

            if (supportsGlobalCFCSS(QEDMode))
                FORE(iter, M)
                    if (!((*iter).isDeclaration()) && canCloneFunction(iter))
                    {
                        Function *F = iter;
                        std::vector<int> callers = returnCallers(iter, bb_id_map);
                        if(sz(callers))
                            createCFCSSChecks 
                                (                                
                                    callers,                                       // std::vector<int> possible_values,
                                    F->getEntryBlock().getFirstInsertionPt(),      // Instruction * insertBefore,
                                    global_cfcss_id,                               // Value *last_cftss_id,
                                    bb_id_map,                                     // std::map<BasicBlock*, int>& bb_id_map,
                                    makeName(&F->getEntryBlock(), "_cfcss_checks") // const Twine & name = ""
                                );

                    insertStoresBeforeCalls (F, bb_id_map);
                    insertStoresBeforeExits (F, bb_id_map);
                    insertChecksAfterCalls  (F, bb_id_map);
                }

            //M.dump();

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

