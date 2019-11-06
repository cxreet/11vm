#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Scalar/EnableProfiling.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/IRBuilder.h"
#include <set>
#include <map>
#include <string.h>
#include <iostream>
#include <fstream>
#include <sstream>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "enable-profiling"

namespace llvm {
void initializeEnableProfilingPassPass(PassRegistry&);
} // end namespace llvm

namespace {
class EnableProfilingPass : public ModulePass {
  APInt Duplicate;
  APInt Amend;

public:
  static char ID;
	static map<string, int> TaintedFuncs;
	void read_indexes();

  EnableProfilingPass()
    : ModulePass(ID) {
    initializeEnableProfilingPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnModule(Module &M) override;

	void instrumentFunction(Function& F, Module& M, int idx);

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<LoopInfoWrapperPass>();
  }

	void replace(std::string& str, const std::string& from, const std::string& to) {
		if(from.empty())
			return;
		size_t start_pos = 0;
		while((start_pos = str.find(from, start_pos)) != std::string::npos) {
			str.replace(start_pos, from.length(), to);
			start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
		}
	}
	//===========string split begins===========
	template<typename Out>
		void split(const std::string &s, char delim, Out result) {
			std::stringstream ss(s);
			std::string item;
			while (std::getline(ss, item, delim)) {
				*(result++) = item;
			}
		}

	std::vector<std::string> split(const std::string &s, char delim) {
		std::vector<std::string> elems;
		split(s, delim, std::back_inserter(elems));
		return elems;
	}
	//============string split ends==============
	
	Value* getOrCreateGlobalString(Module& M, string val, string name)
	{
		GlobalVariable* g_v = M.getGlobalVariable(name);
		Type* char_ty = Type::getInt8Ty(M.getContext());
		Type* array_ty = ArrayType::get(char_ty, val.length()+1);
		if (!g_v)
		{
			GlobalVariable* new_g_v = new GlobalVariable(M, array_ty, false, GlobalValue::ExternalWeakLinkage, 0, name);
			new_g_v->setAlignment(1);

			Constant *initializer = ConstantDataArray::getString(M.getContext(), val, true);
			new_g_v->setInitializer(initializer);

			g_v = new_g_v;
		}
		//g_v = M.getGlobalVariable(name);
		
		assert(g_v);

		std::vector<Constant*> indices;
		ConstantInt* const_int = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 8));
		indices.push_back(const_int);
		indices.push_back(const_int);
		Constant* g_v_ptr = ConstantExpr::getGetElementPtr(array_ty, g_v, indices);
		return g_v_ptr;
	}
	
	void record_cov(Module& M, Function& F, int id)
	{
		// first basic block
		BasicBlock* entry_bb = &(F.getEntryBlock());
		IRBuilder <> builder(M.getContext());

		// get or create shmget, shmat, shmdt
		// declare dso_local i32 @shmget(i32, i64, i32)
		Function *shm_get = M.getFunction("shmget");
		if (!shm_get)
		{
			Type* result_ty = IntegerType::get(M.getContext(), 32);
			vector<Type*> param_tys;
			param_tys.push_back(IntegerType::get(M.getContext(), 32));
			param_tys.push_back(IntegerType::get(M.getContext(), 64));
		  param_tys.push_back(IntegerType::get(M.getContext(), 32));
			FunctionType *func_ty = FunctionType::get(result_ty, param_tys, false);
			shm_get = Function::Create(func_ty, GlobalValue::ExternalLinkage, "shmget", &M);
			AttributeList al;
			shm_get->setAttributes(al);
		}
		// declare dso_local i8* @shmat(i32, i8*, i32)
		Function *shm_at = M.getFunction("shmat");
		if (!shm_at)
		{
			Type* result_ty = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
			vector<Type*> param_tys;
			param_tys.push_back(IntegerType::get(M.getContext(), 32));
			param_tys.push_back(PointerType::get(IntegerType::get(M.getContext(), 8), 0));
		  param_tys.push_back(IntegerType::get(M.getContext(), 32));
			FunctionType *func_ty = FunctionType::get(result_ty, param_tys, false);
			shm_at = Function::Create(func_ty, GlobalValue::ExternalLinkage, "shmat", &M);
			AttributeList al;
			shm_at->setAttributes(al);
		}
		// declare dso_local i32 @shmdt(i8*)
		Function *shm_dt = M.getFunction("shmdt");
		if (!shm_dt)
		{
			Type* result_ty = IntegerType::get(M.getContext(), 32);
			vector<Type*> param_tys;
			param_tys.push_back(PointerType::get(IntegerType::get(M.getContext(), 8), 0));
			FunctionType *func_ty = FunctionType::get(result_ty, param_tys, false);
			shm_dt = Function::Create(func_ty, GlobalValue::ExternalLinkage, "shmdt", &M);
			AttributeList al;
			shm_dt->setAttributes(al);
		}

		// the new basic blocks for instrumentation:
		// if (!is_func_recorded) {
		//  is_func_recorded = true;
		// 	if (cov_sh_mem == 0) {
		// 		x = shmget(...);
		// 		cov_sh_mem = shmat(x, ...);
		// 	}
		// 	cov_sh_mem[...] |= mask;
		// }
		// entry:
		//
		BasicBlock* record_bb = BasicBlock::Create(M.getContext(), entry_bb->getName() + ".record_cov", &F, entry_bb);
		BasicBlock* get_shm_bb = BasicBlock::Create(M.getContext(), entry_bb->getName() + ".get_shm", &F, record_bb);
		BasicBlock* check_shm_bb = BasicBlock::Create(M.getContext(), entry_bb->getName() + ".check_shm", &F, get_shm_bb);
		BasicBlock* check_record_bb = BasicBlock::Create(M.getContext(), entry_bb->getName() + ".check_record", &F, check_shm_bb);

		// create global variable for recording only once, initialized to 0
		string func_name = F.getName().str();
		string is_func_recorded = "is_" + func_name + "_recorded";
		Type* i8Ty = builder.getInt8Ty();
		GlobalVariable* is_recorded = new GlobalVariable(M, i8Ty, false, 
				GlobalValue::PrivateLinkage, ConstantInt::get(i8Ty, 0), is_func_recorded);

		// create global variable for shared memory:sh_mem, initialized to 0
		string cov_sh_mem_name = "cov_sh_mem";
		PointerType* i32PtrTy = PointerType::get(IntegerType::get(M.getContext(), 32), 0);
		//PointerType* i32PtrPtrTy = PointerType::get(i32PtrTy, 0);
		GlobalVariable* cov_sh_mem = M.getGlobalVariable(cov_sh_mem_name);
		if (!cov_sh_mem) {
			cov_sh_mem = new GlobalVariable(M, i32PtrTy, false,
				GlobalVariable::ExternalWeakLinkage, ConstantPointerNull::get(i32PtrTy), cov_sh_mem_name);
			cov_sh_mem->setAlignment(4);
		}

		// if is_func_name_recorded == 0
		builder.SetInsertPoint(check_record_bb);
		Value* load_inst = builder.CreateLoad(i8Ty, is_recorded);
		Value* cmp_inst = builder.CreateICmpEQ(load_inst, ConstantInt::get(i8Ty, 0));
		builder.CreateCondBr(cmp_inst, check_shm_bb, entry_bb);

		// set is_func_name_recorded = 1, record the coverage
		builder.SetInsertPoint(check_shm_bb);
		builder.CreateStore(ConstantInt::get(i8Ty, 1), is_recorded);
		Value* load_cov_sh_mem = builder.CreateLoad(i32PtrTy, cov_sh_mem);
		Value* cmp_cov_sh_mem = builder.CreateICmpEQ(load_cov_sh_mem, ConstantPointerNull::get(i32PtrTy));
		builder.CreateCondBr(cmp_cov_sh_mem, get_shm_bb, record_bb);

		//%x = call i32 @shmget(285738243, i64 458168, i32 432)
		builder.SetInsertPoint(get_shm_bb);
		vector<Value*> shm_get_params;
		shm_get_params.push_back(ConstantInt::get(builder.getInt32Ty(), 285738243));
		shm_get_params.push_back(ConstantInt::get(builder.getInt64Ty(), 458168));
		shm_get_params.push_back(ConstantInt::get(builder.getInt32Ty(), 144));
		Value* shmget_call = builder.CreateCall(shm_get, shm_get_params, "call_shmget");
		//%y = call i8* @shmat(i32 %x, i8* null, i32 0)
		vector<Value*> shm_at_params;
		shm_at_params.push_back(shmget_call);
		shm_at_params.push_back(ConstantPointerNull::get(PointerType::get(IntegerType::get(M.getContext(), 8), 0)));
		shm_at_params.push_back(ConstantInt::get(builder.getInt32Ty(), 0));
		Value* shmat_call = builder.CreateCall(shm_at, shm_at_params, "call_shmat");
		Value* shmat_call_int_ptr = builder.CreateBitCast(shmat_call, PointerType::get(IntegerType::get(M.getContext(), 32), 0));
		builder.CreateStore(shmat_call_int_ptr, cov_sh_mem);
		// call i32 @shmdt(i8* %y)
		/*
		vector<Value*> shm_dt_params;
		shm_dt_params.push_back(shmat_call);
		builder.CreateCall(shm_dt, shm_dt_params, "call_shmdt");
		*/
		builder.CreateBr(record_bb);

		//  record id
		builder.SetInsertPoint(record_bb);

		//load_cov_sh_mem = builder.CreateLoad(i32PtrTy, cov_sh_mem);
		PHINode* phi_cov_sh_mem = builder.CreatePHI(i32PtrTy, 2);
		phi_cov_sh_mem->addIncoming(shmat_call_int_ptr, get_shm_bb);
		phi_cov_sh_mem->addIncoming(load_cov_sh_mem, check_shm_bb);
		Value* id_val = ConstantInt::get(builder.getInt32Ty(), id);
		Value* which_int = builder.CreateUDiv(id_val, ConstantInt::get(builder.getInt32Ty(), 32));
		Value* which_bit = builder.CreateURem(id_val, ConstantInt::get(builder.getInt32Ty(), 32));
		Value* bit_mask = builder.CreateShl(ConstantInt::get(builder.getInt32Ty(), 1), which_bit);
		vector<Value*> indexes;
		indexes.push_back(which_int);
		Value* shared_mem_val_ptr = builder.CreateInBoundsGEP(phi_cov_sh_mem, indexes);
		Value* shared_mem_val = builder.CreateLoad(builder.getInt32Ty(), shared_mem_val_ptr);
		Value* new_shared_mem_val = builder.CreateOr(shared_mem_val, bit_mask);
		builder.CreateStore(new_shared_mem_val, shared_mem_val_ptr);
		builder.CreateBr(entry_bb);
	}	
};
} // end anonymous namespace

char EnableProfilingPass::ID = 0;
map<string, int> EnableProfilingPass::TaintedFuncs = map<string, int>();

INITIALIZE_PASS_BEGIN(EnableProfilingPass, "enable-profiling",
		"Do profiling for each function. ",
		false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_END(EnableProfilingPass, "enable-profiling",
                    "Do profiling for each function.",
                    false, false)

void EnableProfilingPass::instrumentFunction(Function& F, Module& M, int idx)
{
	if (F.isDeclaration() || F.isIntrinsic() || F.empty())
		return;
	//errs() << F << '\n';
	record_cov(M, F, idx);
	//errs() << F << '\n';
}

void EnableProfilingPass::read_indexes()
{
	const char* index_file = "/home/chenxiong/static_out/index.txt";

	ifstream infile = ifstream(index_file);
	if (!infile.is_open())
		return;
	
	string line;
	while (getline(infile, line))
	{
		vector<string> tokens = split(line, ' ');
		int idx = 0;
		if (tokens[0][0] == '+')
		{
			idx = stoi(tokens[0].substr(1));
		} else {
			idx = stoi(tokens[0]);
		}

		int l = tokens[1].length();
		if (tokens[1][l-1] == '\n')
			TaintedFuncs[tokens[1].substr(0, l-1)] = idx;
		else
			TaintedFuncs[tokens[1]] = idx;
	}
	infile.close();
}

bool EnableProfilingPass::runOnModule(Module &M) {
	
	if (TaintedFuncs.size() == 0)
	{
		read_indexes();
	}
	
	StringRef module_name = M.getName();
	StringRef base_code = StringRef("../../base");
	StringRef testing_code = StringRef("../../testing");
	StringRef buildtools_code = StringRef("../../buildtools");
	StringRef chrome_test_code = StringRef("../../chrome/test");
	if (module_name.startswith(base_code) || module_name.startswith(testing_code) ||
			module_name.startswith(buildtools_code)  || module_name.startswith(chrome_test_code))
	{
		errs() << "skip " << module_name << '\n';
		return false;
	}

	for (Function &F : M)
	{
		string func_name = F.getName().str();
		if (TaintedFuncs.find(func_name) == TaintedFuncs.end())
			continue;
		instrumentFunction(F, M, TaintedFuncs[func_name]);
	}

	std::string module_path = M.getName().str();
	errs() << "++++ " << module_path << '\n';

	replace(module_path, "/", "@");
	replace(module_path, ".", "$");
	module_path = "/home/chenxiong/" + module_path;

	std::error_code EC;
	llvm::raw_fd_ostream OS(module_path, EC, sys::fs::F_None);
	WriteBitcodeToFile(M, OS);
	OS.flush();

  return true;
}

namespace llvm {
ModulePass* createEnableProfilingPass() {
  return new EnableProfilingPass();
}
} // end namespace llvm
