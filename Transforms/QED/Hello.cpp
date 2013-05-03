#include "foreach.h"

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Constants.h"
#include "llvm/Intrinsics.h"
#include "llvm/LLVMContext.h"
#include "llvm/Instructions.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <stdio.h>

using namespace llvm;
namespace {

enum QEDMode
{
    MINIMAL,
    FULL
};

static cl::opt<QEDMode> qed_mode
(
    "mode",
    cl::desc("Set QED mode:"),
    cl::values(clEnumValN(MINIMAL, "minimal", "Minimize QED overhead"),
               clEnumValN(FULL, "full", "Maximize QED coverage"),
               clEnumValEnd),
    cl::init(FULL)
);

enum CheckInsertionMode
{
    CHECK_INPUT,
    CHECK_OUTPUT
};

static cl::opt<CheckInsertionMode> check_insertion_mode
(
    "check",
    cl::desc("Set QED check insertion mode:"),
    cl::values(clEnumValN(CHECK_INPUT, "input", "Check DFG input"),
               clEnumValN(CHECK_OUTPUT, "output", "Check DFG output"),
               clEnumValEnd),
    cl::init(CHECK_INPUT)
);

struct QEDPass : ModulePass
{
    typedef ValueToValueMapTy ValueDuplicateMap;
    static char ID;

    LLVMContext & context;
    Type * void_type;
    IntegerType * i1;
    IntegerType * i8;
    IntegerType * i32;
    ConstantInt * i1_true;
    ConstantInt * i1_false;
    ConstantInt * i32_zero;
    MDNode * qed_dup;

    QEDPass() : ModulePass(ID), context(getGlobalContext())
    {
        void_type = Type::getVoidTy(context);
        i1 = Type::getInt1Ty(context);
        i8 = Type::getInt8Ty(context);
        i32 = Type::getInt32Ty(context);
        i1_true = ConstantInt::get(i1, true);
        i1_false = ConstantInt::get(i1, false);
        i32_zero = ConstantInt::get(i32, 0);
        qed_dup = MDNode::get(context, i1_true);
    }

    std::string makeName(Value * value, const char * suffix)
    {
        return value->hasName() ? value->getName().str() + suffix : std::string();
    }

    unsigned bitWidth(Type * type)
    {
        return type->isPointerTy() ? 32 : type->getPrimitiveSizeInBits();
    }

    Value * mapValue(Value * value, ValueDuplicateMap & map)
    {
        Value * direct_match = map.lookup(value);
        if (direct_match)
        {
            return direct_match;
        }

        Constant * constant = dyn_cast<Constant>(value);
        if (constant)
        {
            Type * type = constant->getType();
            std::vector<Constant *> operands;
            for each_custom(operand, *constant, op_begin, op_end)
            {
                operands.push_back(cast<Constant>(mapValue(*operand, map)));
            }
            ConstantExpr * constant_expr = dyn_cast<ConstantExpr>(constant);
            if (constant_expr)
            {
                return constant_expr->getWithOperands(operands, type);
            }
            else if (isa<ConstantArray>(constant))
            {
                return ConstantArray::get(cast<ArrayType>(type), operands);
            }
            else if (isa<ConstantStruct>(constant))
            {
                return ConstantStruct::get(cast<StructType>(type), operands);
            }
            else if (isa<ConstantVector>(constant))
            {
                return ConstantVector::get(operands);
            }
            else
            {
                return constant;
            }
        }

        return value;
    }

    void mapInstruction(Instruction * instr, ValueDuplicateMap & map)
    {
        for each_custom(operand, *instr, op_begin, op_end)
        {
            *operand = mapValue(*operand, map);
        }
    }

    void muxFunction(Function * func, ValueDuplicateMap & map)
    /*! Duplicate all function parameters and double width of return value */
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

        Type * new_return_type;
        if (return_type->isVoidTy())
        {
            new_return_type = Type::getVoidTy(context);
        }
        else
        {
            unsigned return_bits = bitWidth(return_type);
            new_return_type = Type::getIntNTy(context, 2 * return_bits);
        }

        FunctionType * new_type = FunctionType::get(new_return_type, arg_types, type->isVarArg());
        unsigned address_space = func->getType()->getAddressSpace();
        func->mutateType(PointerType::get(new_type, address_space));

        /* Duplicate arguments */
        std::vector<Argument *> arg_list;
        for each_custom(arg, *func, arg_begin, arg_end)
        {
            arg_list.push_back(arg);
        }
        for each(arg, arg_list)
        {
            Argument * arg_dup = new Argument((*arg)->getType(), makeName(*arg, "_dup"));
            func->getArgumentList().insertAfter(*arg, arg_dup);
            map[*arg] = arg_dup;
        }

        /* Modify attributes to reflect duplicated arguments */
        AttrListPtr attributes = func->getAttributes();
        AttrListPtr new_attributes;
        new_attributes = new_attributes.addAttr(0, attributes.getRetAttributes());
        new_attributes = new_attributes.addAttr(~0, attributes.getFnAttributes());
        for (unsigned index = 0; index < type->getNumParams(); index++)
        {
            Attributes arg_attributes = attributes.getParamAttributes(index + 1);
            new_attributes = new_attributes.addAttr(2 * index + 1, arg_attributes);
            new_attributes = new_attributes.addAttr(2 * index + 2, arg_attributes);
        }
        func->setAttributes(new_attributes);
    }

    void muxCallInst(CallInst * call, ValueDuplicateMap & map)
    /*! Duplicate all call instruction parameters, demux the return value
        Depends on muxFunction being called on all functions to produce the function type map */
    {
        std::vector<Value *> args;
        for (unsigned index = 0; index < call->getNumArgOperands(); index++)
        {
            Value * arg = call->getArgOperand(index);
            args.push_back(arg);
            args.push_back(mapValue(arg, map));
        }
        Function * function = call->getCalledFunction();
        CallInst * new_call = CallInst::Create(function, args, "", call);
        new_call->setAttributes(call->getAttributes());

        Type * result_type = call->getType();
        Type * packed_type = new_call->getType();
        if (!result_type->isVoidTy())
        {
            unsigned result_size = bitWidth(result_type);
            assert(result_size);
            Type * result_bits_type = Type::getIntNTy(context, result_size);
            bool pointer = result_type->isPointerTy();

            Value * result_bits = new TruncInst(new_call, result_bits_type, "", call);
            BinaryOperator * shifty = BinaryOperator::Create(Instruction::LShr, new_call, ConstantInt::get(packed_type, result_size), "", call);
            Value * result_dup_bits = new TruncInst(shifty, result_bits_type, "", call);
            Value * result = pointer ? new IntToPtrInst(result_bits, result_type, call->getName(), call) : result_bits;
            Value * result_dup = pointer ? new IntToPtrInst(result_dup_bits, result_type, makeName(call, "_dup"), call) : result_dup_bits;

            assert(call->getType() == result->getType());
            call->replaceAllUsesWith(result);
            map[result] = result_dup;
        }
        call->eraseFromParent();
    }

    void muxReturnInst(ReturnInst * ret, ValueDuplicateMap & map)
    /*! Replace the return value with a mux of the value and its duplicate
        Depends on value duplicate map being complete */
    {
        Value * value = ret->getReturnValue();
        assert(value);
        Type * type = value->getType();
        assert(type);
        unsigned value_size = bitWidth(type);
        assert(value_size);
        Type * value_bits_type = Type::getIntNTy(context, value_size);
        Type * value_mux_type = Type::getIntNTy(context, 2 * value_size);
        Value * value_dup = mapValue(value, map);
        bool pointer = type->isPointerTy();

        Value * value_bits = pointer ? new PtrToIntInst(value, value_bits_type, "", ret) : value;
        Value * value_dup_bits = pointer ? new PtrToIntInst(value_dup, value_bits_type, "", ret) : value_dup;
        Value * value_bits2 = new ZExtInst(value_bits, value_mux_type, "", ret);
        Value * value_dup_bits2 = new ZExtInst(value_dup_bits, value_mux_type, "", ret);
        BinaryOperator * shifty = BinaryOperator::Create(Instruction::Shl, value_dup_bits2, ConstantInt::get(value_mux_type, value_size), "", ret);
        BinaryOperator * mux_value = BinaryOperator::Create(Instruction::Or, value_bits2, shifty, makeName(ret->getOperand(0), "_muxed"), ret);

        ret->setOperand(0, mux_value);
    }

    Instruction * cloneInstruction(Instruction * inst, ValueDuplicateMap & map)
    {
        Instruction * inst_dup = inst->clone();
        mapInstruction(inst_dup, map);
        inst_dup->setName(makeName(inst, "_dup"));
        inst_dup->setMetadata("qed_dup", qed_dup);
        inst_dup->insertAfter(inst);
        return inst_dup;
    }

    GlobalVariable * cloneGlobal(GlobalVariable * global, Module * module)
    {
        std::string name = makeName(global, "_dup");
        PointerType * type = global->getType();
        GlobalVariable * global_dup = new GlobalVariable(type->getElementType(), global->isConstant(),
                                                         global->getLinkage(), global->getInitializer(), name,
                                                         global->isThreadLocal(), type->getAddressSpace());
        global_dup->copyAttributesFrom(global);
        module->getGlobalList().insertAfter(global, global_dup);
        return global_dup;
    }

    CmpInst * createCheckInst(Value * a, Value * b, const Twine & name, Instruction * insertBefore)
    {
        bool float_type = a->getType()->isFPOrFPVectorTy();
        CmpInst::OtherOps op = float_type ? Instruction::FCmp : Instruction::ICmp;
        CmpInst::Predicate predicate = float_type ? CmpInst::FCMP_ONE : CmpInst::ICMP_NE;
        CmpInst * cmp = CmpInst::Create(op, predicate, a, b, name, insertBefore);
        return cmp;
    }

    Value * createReduction(Instruction::BinaryOps op, ArrayRef<Value *> inputs,
                            Instruction * insertBefore, const Twine & name = "")
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

    Constant * createStringConstant(const std::string & string)
    {
        std::vector<Constant *> necklace;
        for each(character, string)
        {
            necklace.push_back(ConstantInt::get(i8, *character));
        }
        return ConstantArray::get(ArrayType::get(i8, string.size()), necklace);
    }

    Function * getExternalFunction(StringRef name, FunctionType * type, Module * module)
    {
        module->getOrInsertFunction(name, type);
        Function * function = module->getFunction(name);
        assert(function);
        return function;
    }

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

    CallInst * createExitCall(Value * status, BasicBlock * block, Module * module)
    {
        FunctionType * exit_type = FunctionType::get(void_type, i32, false);
        Function * exit_func = getExternalFunction("exit", exit_type, module);
        CallInst * call = CallInst::Create(exit_func, status, "", block);
        call->setDoesNotThrow();
        return call;
    }

    bool isCallLike(Instruction * inst)
    {
        return isa<CallInst>(inst) || isa<AllocaInst>(inst) || isa<LoadInst>(inst) || isa<StoreInst>(inst);
    }

    bool isOutput(Value * value, BasicBlock * block)
    {
        for each_custom(use, *value, use_begin, use_end)
        {
            Instruction * user = dyn_cast<Instruction>(*use);
            if (user && (isa<TerminatorInst>(user) || isa<PHINode>(user) ||
                         isCallLike(user) || user->getParent() != block))
            {
                return true;
            }
        }
        return false;
    }

    bool isDefined(Function * func)
    {
        return !func->getBasicBlockList().empty();
    }

    bool isMuxable(Function * func)
    {
        switch (qed_mode)
        {
        case MINIMAL:
            return false;
        case FULL:
            return isDefined(func) && func->getName() != "main";
        }
    }

    bool isDuplicable(Instruction * inst)
    {
        switch (qed_mode)
        {
        case MINIMAL:
            return !isa<TerminatorInst>(inst) && !isa<PHINode>(inst) && !isCallLike(inst);
        case FULL:
            return !isa<TerminatorInst>(inst) && !isa<AllocaInst>(inst);
        }
    }

    void cloneBlock(BasicBlock * block, Function * function, ValueDuplicateMap & map)
    {
        std::vector<Value *> error_vec;
        std::vector<Instruction *> inst_list;
        TerminatorInst * terminator = block->getTerminator();
        for each(inst, *block)
        {
            if (isDuplicable(inst))
            {
                inst_list.push_back(inst);
            }
        }
        for each(inst, inst_list)
        {
            CallInst * call = dyn_cast<CallInst>(*inst);
            if (call)
            {
                if (isMuxable(call->getCalledFunction()))
                {
                    muxCallInst(call, map);
                }
            }
            else
            {
                Instruction * inst_dup = cloneInstruction(*inst, map);
                map[*inst] = inst_dup;
                if (isOutput(*inst, block))
                {
                    CmpInst * error = createCheckInst(*inst, inst_dup, makeName(*inst, "_error"), terminator);
                    error_vec.push_back(error);
                }
            }
        }
        if (!error_vec.empty())
        {
            Value * error = createReduction(Instruction::Or, error_vec, terminator, makeName(block, "_error"));
            assert(error);
            Function * output_func = Intrinsic::getDeclaration(function->getParent(), Intrinsic::output, i1);
            assert(output_func);
            CallInst::Create(output_func, error, "", terminator);
        }
    }

    void cloneBlockTree(DomTreeNodeBase<BasicBlock> * root, Function * function, ValueDuplicateMap & map)
    {
        cloneBlock(root->getBlock(), function, map);
        for each(child, *root)
        {
            cloneBlockTree(*child, function, map);
        }
    }

    bool runOnFunction(Function * function, ValueDuplicateMap & global_map)
    {
        assert(isDefined(function));
        ValueDuplicateMap map;
        map.insert(global_map.begin(), global_map.end());
        DominatorTree & dominator_tree = getAnalysis<DominatorTree>(*function);

        cloneBlockTree(dominator_tree.getBase().getRootNode(), function, map);

        if (isMuxable(function))
        {
            for each(block, *function)
            {
                ReturnInst * ret = dyn_cast<ReturnInst>(block->getTerminator());
                if (ret && ret->getReturnValue())
                {
                    muxReturnInst(ret, map);
                }
            }
        }

        for each(mapping, map)
        {
            PHINode * phi_dup = dyn_cast<PHINode>(mapping->second);
            if (phi_dup)
            {
                mapInstruction(phi_dup, map);
            }
        }
        return true;
    }

    bool runOnModule(Module & module)
    {
        ValueDuplicateMap map;
        for each(function, module)
        {
            if (isMuxable(function))
            {
                muxFunction(function, map);
            }
        }
        for each(function, module)
        {
            if (isDefined(function))
            {
                runOnFunction(function, map);
            }
        }
        return true;
    }

    void getAnalysisUsage(AnalysisUsage & info) const
    {
        info.addRequired<DominatorTree>();
    }
};

char QEDPass::ID;
static RegisterPass<QEDPass> qed("qed", "Transform for Quick Error Detection");

} /* End anonymous namespace */
