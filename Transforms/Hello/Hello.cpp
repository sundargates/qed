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
            	CallInst::Create(checkFunction, error, "", bb->getTerminator());
            }
            Value *tobestoredval = ConstantInt::get(Type::getInt32Ty(context), currentBasicBlock++, false);
    		new StoreInst (tobestoredval, cftss_id, bb->getFirstInsertionPt());
            
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
        	BasicBlock* bb2 = llvm::BasicBlock::Create(context, "return_block", checkFunction);
        	BasicBlock* bb3 = llvm::BasicBlock::Create(context, "exit_block", checkFunction);
        	std::vector<Value *> v;

            Instruction *loadres = new LoadInst(cftss_id, "", bb3);
        	v.pb(loadres);
        	createPrintfCall("printfresult", "The last basic block that got executed was = %d\n", v, bb3, &module);
        	createExitCall(one, bb3, &module);
        	BranchInst *branchinst = BranchInst::Create(bb2, bb3, check_value, bb1);
        	branchinst = BranchInst::Create(bb2, bb3);

        	llvm::ReturnInst::Create(context, 0, bb2);


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

