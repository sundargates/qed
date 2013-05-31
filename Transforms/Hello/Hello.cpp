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
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Analysis/Dominators.h"


#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Support/CommandLine.h"

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
namespace
{
//     static unsigned NumRetVals(const Function *F)
//     {
//         if (F->getReturnType()->isVoidTy())
//         return 0;
//         else if (StructType *STy = dyn_cast<StructType>(F->getReturnType()))
//         return STy->getNumElements();
//         else
//         return 1;
//     }
    struct QED : public ModulePass
    {
        public:
        static char ID;
        Value *one;
        LLVMContext & context;
        Function *checkFunction;
        IntegerType * i1;
	    IntegerType * i8;
	    IntegerType * i32;
	    ConstantInt * i1_true;
	    ConstantInt * i1_false;
	    ConstantInt * i32_zero;
	    int currentBasicBlock;
	    GlobalVariable *cftss_id;
//         void modifyPrototype(Function *F)
//         {
//             // Start by computing a new prototype for the function, which is the same as
//             // the old function, but has 2X more arguments and a 2X return type.
//             FunctionType *FTy = F->getFunctionType();
//             std::vector<Type*> Params;
// 
//             // Set up to build a new list of parameter attributes.
//             SmallVector<AttributeSet, 8> AttributesVec;
//             const AttributeSet &PAL = F->getAttributes();
//             
//             // Find out the new return value.
//             Type *RetTy = FTy->getReturnType();
//             Type *NRetTy = NULL;
//             unsigned RetCount = NumRetVals(F);
// 
//             std::vector<Type*> RetTypes;
//             
//             //If return is type void, then we don't have to do much for QED
//             if (RetTy->isVoidTy())
//             {
//                 NRetTy = RetTy;
//             }
//             else
//             {
//                 StructType *STy = dyn_cast<StructType>(RetTy);
//                 // Look at each of the original return values individually.
//                 // This is the case for multiple return values
//                 if (STy)
//                 {
//                     FORN(i, RetCount)
//                     {
//                         RetTypes.push_back(STy->getElementType(i));
//                         RetTypes.push_back(STy->getElementType(i));
//                     }
//                 }
//                 // We used to return a single value.
//                 else
//                 {
//                     RetTypes.push_back(RetTy);
//                     RetTypes.push_back(RetTy);
//                 }
//                 // More than one return type? Return a struct with them. Also, if we used
//                 // to return a struct and didn't change the number of return values,
//                 // return a struct again. This prevents changing {something} into
//                 // something and {} into void.
//                 // Make the new struct packed if we used to return a packed struct
//                 // already.
//                 if (RetTypes.size() > 1)
//                     NRetTy = StructType::get(STy->getContext(), RetTypes, false);
//                 else
//                     NRetTy = Type::getVoidTy(F->getContext());
//                 
//                 assert(NRetTy && "No new return type found?");
//             }
//             
//             // The existing function return attributes.
//             AttributeSet RAttrs = PAL.getRetAttributes();
//             
//             //Add the return attributes to the new attributes set
//             if (RAttrs.hasAttributes(AttributeSet::ReturnIndex))
//                 AttributesVec.push_back(AttributeSet::get(NRetTy->getContext(), RAttrs));
//                 
//                 
//             // Construct the new parameter list from non-dead arguments. Also construct
//             // a new set of parameter attributes to correspond. Skip the first parameter
//             // attribute, since that belongs to the return value.
//             unsigned i = 0;
//             for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end();
//             I != E; ++I, ++i)
//             {
//                 Params.push_back(I->getType());
//                 Params.push_back(I->getType());
// 
//                 // Get the original parameter attributes (skipping the first one, that is
//                 // for the return value.
//                 // Push the attributes twice to reflect the fact that the
//                 // arguments have been duplicated.
//                 if (PAL.hasAttributes(i + 1))
//                 {
//                     AttrBuilder B(PAL, i + 1);
//                     AttrBuilder B(PAL, i + 1);
//                     AttributesVec.
//                     push_back(AttributeSet::get(F->getContext(), Params.size(), B));
//                     AttributesVec.
//                     push_back(AttributeSet::get(F->getContext(), Params.size(), B));
//                 }
//             }
// 
//             //Push the Function attributes
//             if (PAL.hasAttributes(AttributeSet::FunctionIndex))
//                 AttributesVec.push_back(AttributeSet::get(F->getContext(),
//                                           PAL.getFnAttributes()));
// 
//             // Reconstruct the AttributesList based on the vector we constructed.
//             AttributeSet NewPAL = AttributeSet::get(F->getContext(), AttributesVec);
// 
//             // Create the new function type based on the recomputed parameters.
//             FunctionType *NFTy = FunctionType::get(NRetTy, Params, FTy->isVarArg());
//             
//             // Create the new function body and insert it into the module...
//             Function *NF = Function::Create(NFTy, F->getLinkage());
//             NF->copyAttributesFrom(F);
//             NF->setAttributes(NewPAL);
//             
//             // Insert the new function before the old function, so we won't be processing
//             // it again.
//             F->getParent()->getFunctionList().insert(F, NF);
//             NF->takeName(F);
//             
//             
//             
//             // Loop over all of the callers of the function, transforming the call sites
//             // to pass in a 2X more arguments into the new function.
//             std::vector<Value*> Args;
//             while (!F->use_empty())
//             {
//                 CallSite CS(F->use_back());
//                 Instruction *Call = CS.getInstruction();
// 
//                 AttributesVec.clear();
//                 const AttributeSet &CallPAL = CS.getAttributes();
// 
//                 // The call return attributes.
//                 AttributeSet RAttrs = CallPAL.getRetAttributes();
// 
//                 // Add the return attributes to the AttributesVec
//                 if (RAttrs.hasAttributes(AttributeSet::ReturnIndex))
//                   AttributesVec.push_back(AttributeSet::get(NF->getContext(), RAttrs));
// 
//                 // Declare these outside of the loops, so we can reuse them for the second
//                 // loop, which loops the varargs.
//                 CallSite::arg_iterator I = CS.arg_begin();
//                 unsigned i = 0;
//                 // Loop over those operands, corresponding to the normal arguments to the
//                 // original function, and add those that are still alive.
//                 for (unsigned e = FTy->getNumParams(); i != e; ++I, ++i)
//                 {
//                     Args.push_back(*I);
//                     Argument *arg_dup = new Argument((*I)->getType(), makeName(*I, "_dup"));
//                     
//                     //this is the QED argument
//                     Args.push_back(arg_dup);
//                     
//                     // Get original parameter attributes, and add them twice
//                     // but skip return attributes.
//                     if (CallPAL.hasAttributes(i + 1))
//                     {
//                         AttrBuilder B(CallPAL, i + 1);
//                         AttributesVec.
//                         push_back(AttributeSet::get(F->getContext(), Args.size(), B));
//                         AttributesVec.
//                         push_back(AttributeSet::get(F->getContext(), Args.size(), B));
//                     }
//                 }
// 
//                 //TODO Not sure if this needs to be added?
//                 //Would it be possible to have QED arguments even in case of a dynamic
//                 //call sites?
//                 // Push any varargs arguments on the list. Don't forget their attributes.
//                 for (CallSite::arg_iterator E = CS.arg_end(); I != E; ++I, ++i)
//                 {
//                     Args.push_back(*I);
//                     if (CallPAL.hasAttributes(i + 1))
//                     {
//                         AttrBuilder B(CallPAL, i + 1);
//                         AttributesVec.
//                           push_back(AttributeSet::get(F->getContext(), Args.size(), B));
//                     }
//                 }
// 
//                 if (CallPAL.hasAttributes(AttributeSet::FunctionIndex))
//                     AttributesVec.push_back(AttributeSet::get(Call->getContext(),
//                                                     CallPAL.getFnAttributes()));
// 
//                 // Reconstruct the AttributesList based on the vector we constructed.
//                 AttributeSet NewCallPAL = AttributeSet::get(F->getContext(), AttributesVec);
// 
//                 Instruction *New;
//                 if (InvokeInst *II = dyn_cast<InvokeInst>(Call))
//                 {
//                     New = InvokeInst::Create(NF, II->getNormalDest(), II->getUnwindDest(),
//                                            Args, "", Call);
//                     cast<InvokeInst>(New)->setCallingConv(CS.getCallingConv());
//                     cast<InvokeInst>(New)->setAttributes(NewCallPAL);
//                 }
//                 else
//                 {
//                     New = CallInst::Create(NF, Args, "", Call);
//                     cast<CallInst>(New)->setCallingConv(CS.getCallingConv());
//                     cast<CallInst>(New)->setAttributes(NewCallPAL);
//                     if (cast<CallInst>(Call)->isTailCall())
//                         cast<CallInst>(New)->setTailCall();
//                 }
//                 New->setDebugLoc(Call->getDebugLoc());
// 
//                 Args.clear();
// 
//                 if (!Call->use_empty())
//                 {
//                     if (New->getType() == Call->getType())
//                     {
//                         // Return type not changed? Just replace users then.
//                         // This means this is a void type
//                         Call->replaceAllUsesWith(New);
//                         New->takeName(Call);
//                     } 
//                     else
//                     {
//                         assert(NRetTy->isStructTy() && "Return type is a struct");
//                         Instruction *InsertPt = Call;
//                         if (InvokeInst *II = dyn_cast<InvokeInst>(Call))
//                         {
//                             BasicBlock::iterator IP = II->getNormalDest()->begin();
//                             while (isa<PHINode>(IP)) ++IP;
//                             InsertPt = IP;
//                         }
// 
//                         // We used to return a struct. Instead of doing smart stuff with all the
//                         // uses of this struct, we will just rebuild it using
//                         // extract/insertvalue chaining and let instcombine clean that up.
//                         //
//                         // Start out building up our return value from undef
//                         Value *RetVal = UndefValue::get(RetTy);
//                         FORN(i, RetCount)
//                         {
//                             Value *V;
//                             V = ExtractValueInst::Create(New, i, "newret", InsertPt);
//                             
//                            // Insert the value at the old position
//                             RetVal = InsertValueInst::Create(RetVal, V, i, "oldret", InsertPt);
//                         }
//                         // Now, replace all uses of the old call instruction with the return
//                         // struct we built
//                         Call->replaceAllUsesWith(RetVal);
//                         New->takeName(Call);
//                     }
//                 }
//                 // Finally, remove the old call from the program, reducing the use-count of
//                 // F.
//                 Call->eraseFromParent();
//             }
//             
//             
//             // Since we have now created the new function, splice the body of the old
//             // function right into the new function, leaving the old rotting hulk of the
//             // function empty.
//             NF->getBasicBlockList().splice(NF->begin(), F->getBasicBlockList());
// 
//             // Loop over the argument list, transferring uses of the old arguments over to
//             // the new arguments, also transferring over the names as well.
//             i = 0;
//             for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(),
//                I2 = NF->arg_begin(); I != E; ++I, ++i)
//             {
//                 // If this is a live argument, move the name and users over to the new
//                 // version.
//                 I->replaceAllUsesWith(I2);
//                 I2->takeName(I);
//                 
//                 //Append by two as the next argument is the duplicate argument
//                 ++I2;
//                 ++I2;
//             }
//             // If we change the return value of the function we must rewrite any return
//             // instructions.  Check this now.
//             for (Function::iterator BB = NF->begin(), E = NF->end(); BB != E; ++BB)
//                 if (ReturnInst *RI = dyn_cast<ReturnInst>(BB->getTerminator()))
//                 {
//                     Value *RetVal;
//                     if (NFTy->getReturnType()->isVoidTy())
//                     {
//                       RetVal = 0;
//                     }
//                     else
//                     {
//                         // assert (RetTy->isStructTy());
//                         // The original return value was a struct, insert
//                         // extractvalue/insertvalue chains to extract only the values we need
//                         // to return and insert them into our new result.
//                         // This does generate messy code, but we'll let it to instcombine to
//                         // clean that up.
//                         
//                         Value *OldRet = RI->getOperand(0);
//                         // Start out building up our return value from undef
//                         RetVal = UndefValue::get(NRetTy);
//                         FORN(i, RetCount)
//                         {
//                             ExtractValueInst *EV = ExtractValueInst::Create(OldRet, i,
//                                                                           "oldret", RI);
//                             RetVal = InsertValueInst::Create(RetVal, EV, i,
//                                                              "newret", RI);
//                         }
//                 }
//                 // Replace the return instruction with one returning the new return
//                 // value (possibly 0 if we became void).
//                 ReturnInst::Create(F->getContext(), RetVal, RI);
//                 BB->getInstList().erase(RI);
//             }
// 
//             // Patch the pointer to LLVM function in debug info descriptor.
// //             FunctionDIMap::iterator DI = FunctionDIs.find(F);
// //             if (DI != FunctionDIs.end())
// //                 DI->second.replaceFunction(NF);
// 
//             // Now that the old function is dead, delete it.
//             F->eraseFromParent();
//         }
        QED() : ModulePass(ID), context(getGlobalContext())
        {
            one = ConstantInt::get(Type::getInt32Ty(context),1);
            i1 = Type::getInt1Ty(context);
	        i8 = Type::getInt8Ty(context);
	        i32 = Type::getInt32Ty(context);
	        i1_true = ConstantInt::get(i1, true);
	        i1_false = ConstantInt::get(i1, false);
	        i32_zero = ConstantInt::get(i32, 0);
        }
        bool prototypeNeedsToBeModified(Function *F)
        {
            return !F->getBasicBlockList().empty() && F->size() && F->getName().compare("main") 
            	&& (F->getName().find("entry_point")==StringRef::npos)
            	&& F->getName().compare("check_function");
        }
		unsigned bitWidth(Type * type)
		{
			return type->isPointerTy() ? 32 : type->getPrimitiveSizeInBits();
		}

        void cloneGlobal(GlobalVariable * global, Module &M, ValueDuplicateMap & map)
		{
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
				if (I->getName().startswith("llvm.") || I->getName().startswith(".llvm."))
					continue;
				cloneGlobal(I, M, map);
			}
		}
        void modifyPrototype(Function * func, ValueDuplicateMap & map)
        {
            /* Modify function type to reflect duplicated arguments, muxed return type */
            FunctionType * type = func->getFunctionType();
            Type * return_type = type->getReturnType();

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
            unsigned address_space = func->getType()->getAddressSpace();
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
            SmallVector<AttributeSet, 8> AttributesVec;
            const AttributeSet &PAL = func->getAttributes();
            AttributeSet RAttrs = PAL.getRetAttributes();
            
            //Add the return attributes to the new attributes set
            if (RAttrs.hasAttributes(AttributeSet::ReturnIndex))
                AttributesVec.push_back(AttributeSet::get(context, RAttrs));
                
                
            // Construct the new parameter list from non-dead arguments. Also construct
            // a new set of parameter attributes to correspond. Skip the first parameter
            // attribute, since that belongs to the return value.
            unsigned i = 0;
            unsigned size = 0;
            for (Function::arg_iterator I = func->arg_begin(), E = func->arg_end();
            I != E; ++I, ++i)
            {
                // Get the original parameter attributes (skipping the first one, that is
                // for the return value.
                // Push the attributes twice to reflect the fact that the
                // arguments have been duplicated.
                size += 2;
                if (PAL.hasAttributes(i + 1))
                {
                    AttrBuilder B(PAL, i + 1);
                    AttrBuilder B_dup(PAL, i + 1);
                    AttributesVec.
                    push_back(AttributeSet::get(context, size-1, B));
                    AttributesVec.
                    push_back(AttributeSet::get(context, size, B_dup));
                }
            }

            //Push the Function attributes
            if (PAL.hasAttributes(AttributeSet::FunctionIndex))
                AttributesVec.push_back(AttributeSet::get(func->getContext(),
                                          PAL.getFnAttributes()));

            // Reconstruct the AttributesList based on the vector we constructed.
            AttributeSet NewPAL = AttributeSet::get(func->getContext(), AttributesVec);
            func->setAttributes(NewPAL);

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
            // 	instruction->dump();
            // 	Instruction *NI = instruction->clone();
            // 	map[instruction] = NI;
            // 	mapOperands(NI, map);
            // 	return NI;
            // }
            // value->dump();
            // errs()<<"The above operand does not have a replacement?\n";
            return mp(value, false);
        }
        bool isCloneable(Instruction *inst)
        {
        	bool success = true;
            success &= !isa<TerminatorInst>(inst);
            // success &= !isa<PHINode>(inst);
            CallInst *call = dyn_cast<CallInst>(inst);
            success &= !call || (call && (call->isInlineAsm() || call->getCalledFunction()->getName() == "printf"));
            return success;
        }
        bool isPhi(Instruction *inst)
        {
        	bool success = true;
            success &= isa<PHINode>(inst);
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
            new_call->setAttributes(call->getAttributes());

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
			        return BinaryOperator::Create(op, input1, input2, name, insertBefore);
		    }
		}
        void cloneBasicBlock(BasicBlock *bb, Function *F, Module *M, ValueDuplicateMap & map, std::map<BasicBlock *, bool> &visited, 
        	std::vector< std::pair<Instruction *, Value *> > &toBeReplaced)
        {
            // errs()<<bb->getName()<<"\n";
            std::string bbname = bb->getName();
            // int currentSplit = 0;
    		if(visited[bb])
    		{
    			errs()<<"this block has been visited before it seems?";
    			return;
    		}
    		visited[bb] = true;
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
                    if(I->mayReturn() && hasOutput(I) && !isPhi(I))
                        previous = true;
                }
                // else
                // if(isPhi(iter))
                // {
                // 	skip++;
                // 	I = iter;
                // 	NI = I->clone();
                // 	mapOperands(NI, map);
                // 	map[I] = NI;
                // 	if(I->hasName())
                //         NI->setName(makeName(I, "_dup"));
                //     NI->insertAfter(I);
                // }
	            
	        }
            FORN(i, sz(toBeRemoved))
            {
                CallInst *temp = toBeRemoved[i];
                temp->eraseFromParent();
            }

            if(sz(createdCheckInsts))
            {
            	Value * error = createReduction(Instruction::Or, createdCheckInsts, bb->getTerminator(), makeName(bb, "_error"));
            	// Function * exit_func = getExternalFunction("exit", exit_type, module);
            	// assert(exit_func);
            	// CallInst::Create(checkFunction, error, "", bb->getTerminator());
            }
            Value *tobestoredval = ConstantInt::get(Type::getInt32Ty(context), currentBasicBlock++, false);
    		new StoreInst (tobestoredval, cftss_id, bb->getFirstInsertionPt());
            
   //          int pos = 0;
   //          previous = false;
   //          BasicBlock::iterator iter;
			// BasicBlock *current = bb;
			// BasicBlock::iterator terminator = current->end();
			// Value *condition = NULL;
   //          // errs()<<bb->getName()<<" We did not come here\n";
			// for(iter = current->begin();iter!=terminator;)
			// {
   //              assert(iter && "This cannot be null");
			// 	if(previous)
			// 	{
			// 		assert((condition!=NULL) && "Condition Value not set");
			// 		// condition->dump();
   //                  // errs()<<"Are we here1?\n";
   //                  // std::string temp = makeName(current, "_s");
   //                  // errs()<<"Are we here2?\n";
			// 		BasicBlock *newlycreated = bb->splitBasicBlock	(iter, "");
   //                  // errs()<<"Are we here3?\n";
					
			// 		BasicBlock *fall_back = BasicBlock::Create(context, "", F, newlycreated);
			// 		createExitCall(one, fall_back, M);
			// 		BranchInst *branchinst = BranchInst::Create(newlycreated, fall_back, condition, bb->getTerminator());
			// 		branchinst = BranchInst::Create(newlycreated, fall_back);
			// 		// branchinst = dyn_cast<BranchInst>(bb->getTerminator());
			// 		bb->getTerminator()->eraseFromParent();
					
					
			// 		visited[newlycreated] = true;
			// 		visited[fall_back] = true;
					
			// 		//Update the parameters after the basic block got created
			// 		iter = newlycreated->begin();

			// 		terminator = newlycreated->end();
			// 		current = newlycreated;
   //                  // errs()<<current->getName()<<"\n";
					
			// 		condition = NULL;
			// 		previous = false;
			// 		continue;
			// 	}
			// 	if(pos >= sz(createdCheckInsts))	break;
			// 	if(pos < sz(createdCheckInsts) && iter->isIdenticalTo(createdCheckInsts[pos]))
			// 	{
			// 		pos++;
			// 		condition = iter;
			// 		errs()<<condition->getName()<<"\n";
			// 		previous = true;
			// 	}
   //              iter++;
			// }
			// if(pos!=sz(createdCheckInsts))	errs()<<"THere definitely is an error here\n";
			// errs()<<bb->getName()<<" We did not come here2\n";
        }
        void cloneBlockTree(DomTreeNodeBase<BasicBlock> * root, Function * function, Module *M, ValueDuplicateMap & map, std::map<BasicBlock *, bool> &visited, 
        	std::vector< std::pair<Instruction *, Value *> > &toBeReplaced)
        {
            cloneBasicBlock(root->getBlock(), function, M, map, visited, toBeReplaced);
            for each(child, *root)
                cloneBlockTree(*child, function, M, map, visited, toBeReplaced);
        }
        void printName(Value *v)
        {
            errs()<<v->getName()<<"\n";
        }
        void cloneFunction(Function *F, ValueDuplicateMap & global_map, Module &M)
        {
            // printName(F);
            if(F->getName() == "check_function")
            	return;
            std::	map<BasicBlock *, bool> visited;

            std::vector< std::pair<Instruction *, Value *> > toBeReplaced;
            toBeReplaced.clear();

            DominatorTree & dominator_tree = getAnalysis<DominatorTree>(*F);
            ValueDuplicateMap map;
        	map.insert(global_map.begin(), global_map.end());
            cloneBlockTree(dominator_tree.getBase().getRootNode(), F, &M, map, visited, toBeReplaced);

            FORN(i,sz(toBeReplaced))
            {
            	std::pair<Value *, bool> t = mapValue(toBeReplaced[i].second, map);
            	if(t.second)
            	{
            		// toBeReplaced[i].second->dump();
            		// t.first->dump();
            		if(!remapOperand(toBeReplaced[i].first, toBeReplaced[i].second, t.first))
            			db("Error on Replacing");
            	}
            	// else
            	// 	t.first->dump();
            }
            // visited.clear();
            // db("Second Pass");
            // cloneBlockTree(dominator_tree.getBase().getRootNode(), F, &M, map, visited, true);
                
            if (prototypeNeedsToBeModified(F))
            {
                FORE(iter, (*F))
                {
                    ReturnInst * ret = dyn_cast<ReturnInst>(iter->getTerminator());
                    if (ret && ret->getReturnValue())
                    {
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
        void createErrorCheckFunction(Module &module)
        {
        	std::vector<Type*> Params;
        	Params.pb(Type::getInt1Ty(context));
        	llvm::FunctionType* ftype = llvm::FunctionType::get(Type::getVoidTy(context), Params, false);
        	module.getOrInsertFunction("check_function", ftype);
        	// Function * realFunc = dyn_cast<Function *>(func);
        	checkFunction = module.getFunction("check_function");
        	Argument *check_value = &checkFunction->getArgumentList().front();
        	
        	BasicBlock* bb1 = llvm::BasicBlock::Create(context, "check_block", checkFunction);
        	BasicBlock* bb3 = llvm::BasicBlock::Create(context, "return_block", checkFunction);
        	BasicBlock* bb2 = llvm::BasicBlock::Create(context, "exit_block", checkFunction);
        	// IRBuilder<> Builder(Entry);
        	std::vector<Value *> v;
        	// s
        	v.pb(cftss_id);
        	createPrintfCall("printfresult", "This was the CFTSSID was = %d\n", v, bb2, &module);
        	createExitCall(one, bb2, &module);
        	BranchInst *branchinst = BranchInst::Create(bb3, bb2, check_value, bb1);
        	branchinst = BranchInst::Create(bb3, bb2);

        	llvm::ReturnInst::Create(context, 0, bb3);


        }
        bool runOnModule(Module &M)
        {
        	currentBasicBlock = 1;
			ValueDuplicateMap map;
			cloneGlobalVariables(M, map);
			cftss_id = new GlobalVariable(M, Type::getInt32Ty(context), false, GlobalValue::PrivateLinkage, ConstantInt::get(Type::getInt32Ty(context), 0, false), "CFTSSID");
			createErrorCheckFunction(M);
			FORE(iter, M)
				if(!((*iter).isDeclaration()) && prototypeNeedsToBeModified(iter))
				{
					modifyPrototype(iter,map);
				}

			FORE(iter, M)
				if (!((*iter).isDeclaration()))
					cloneFunction(iter, map, M);
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

// STATISTIC(HelloCounter, "Counts number of functions greeted");
// 
// namespace {
//   // Hello - The first implementation, without getAnalysisUsage.
//   struct Hello : public FunctionPass {
//     static char ID; // Pass identification, replacement for typeid
//     Hello() : FunctionPass(ID) {}
// 
//     virtual bool runOnFunction(Function &F) {
//       ++HelloCounter;
//       errs() << "Hello: ";
//       errs().write_escaped(F.getName()) << '\n';
//       AttributeSet a=F.getAttributes();
//       a.dump();
//       return false;
//     }
//   };
// }
// 
// char Hello::ID = 0;
// static RegisterPass<Hello> X("hello", "Hello World Pass");
// 
// namespace {
//   // Hello2 - The second implementation with getAnalysisUsage implemented.
//   struct Hello2 : public FunctionPass {
//     static char ID; // Pass identification, replacement for typeid
//     Hello2() : FunctionPass(ID) {}
// 
//     virtual bool runOnFunction(Function &F) {
//       ++HelloCounter;
//       errs() << "Hello: ";
//       errs().write_escaped(F.getName()) << '\n';
//       return false;
//     }
// 
//     // We don't modify the program, so we preserve all analyses
//     virtual void getAnalysisUsage(AnalysisUsage &AU) const {
//       AU.setPreservesAll();
//     }
//   };
// }
// 
// char Hello2::ID = 0;
// static RegisterPass<Hello2>
// Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");
