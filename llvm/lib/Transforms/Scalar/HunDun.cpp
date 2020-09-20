#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Scalar/DumpIR.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/IRBuilder.h"
#include <set>
#include <map>
#include <unordered_map>
#include <string.h>
#include <iostream>
#include <fstream>
#include <sstream>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "hundun"

namespace llvm {
	void initializeHunDunPassPass(PassRegistry&);
}

namespace {
class HunDunPass : public ModulePass {
		
public:
	static char ID;
	//static uint32_t idx;

private:
	uint32_t shm_size;
	string out_dir;

public:

	HunDunPass() : ModulePass(ID) {
		initializeHunDunPassPass(*PassRegistry::getPassRegistry());
	}

	HunDunPass(uint32_t hundun_shm_size, string hundun_out_dir)
		: ModulePass(ID) {
		this->shm_size = hundun_shm_size;
		this->out_dir = hundun_out_dir;
		initializeHunDunPassPass(*PassRegistry::getPassRegistry());
	}

	bool runOnModule(Module &M) override;

private:
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

	void saveIR(Module &M) {
		std::string module_path = M.getName().str();
		replace(module_path, "/", "@");
		replace(module_path, ".", "$");

		module_path = this->out_dir + "/" + module_path + ".bc";
		errs() << "saving ir " << module_path << '\n';
		std::error_code EC;
		llvm::raw_fd_ostream OS(module_path, EC, sys::fs::F_None);
		WriteBitcodeToFile(M, OS);
		OS.flush();
	}
};
}

char HunDunPass::ID = 42;
//uint32_t HunDunPass::idx = 0;

INITIALIZE_PASS_BEGIN(HunDunPass, "hundun", "HunDun.", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass);
INITIALIZE_PASS_END(HunDunPass, "hundun", "HunDun.", false, false)

bool HunDunPass::runOnModule(Module &M) {
	// only for saving IR
	if (this->shm_size == 0) {
		saveIR(M);
		return false;
	}
	
	std::unordered_map<string, int> name_2_idx;
	std::string module_path = M.getName().str();
	replace(module_path, "/", "@");
	replace(module_path, ".", "$");
	std::string id_file_name = this->out_dir + "/" + module_path + ".bc.id";
	std::ifstream infile(id_file_name.data());
	if (infile.is_open()){
		string line;
		while (getline(infile, line)) {
			vector<string> tokens = split(line, ' ');
			string func_name = tokens[0];
			string::size_type sz;
			int idx = stoi(tokens[1], &sz);
			name_2_idx[func_name] = idx;
		}
	}

	infile.close();

	// do instrumentation
  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

	// instrument function for profiling
	for (Function &F : M) {
		// skip special functions
		if (F.isDeclaration() || F.isIntrinsic() || F.empty())
			continue;

		// first basic block
		BasicBlock* entry_bb = &(F.getEntryBlock());
    BasicBlock::iterator IP = entry_bb->getFirstInsertionPt();
    IRBuilder<> IRB(&(*IP));

    unsigned int cur_loc = name_2_idx[F.getName().str()];
		errs() << "HunDun:" << F.getName() << ' ' << cur_loc << '\n';
    ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

    /* Load SHM pointer */

    LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
    MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    Value *MapPtrIdx =
        IRB.CreateGEP(MapPtr, CurLoc);

    /* Update bitmap */
    IRB.CreateStore(ConstantInt::get(Int8Ty, 1), MapPtrIdx)
        ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
	}

	return true;
}

namespace llvm {
	ModulePass* createHunDunPass(uint32_t hundun_shm_size, string hundun_out_dir) {
		return new HunDunPass(hundun_shm_size, hundun_out_dir);
	}
}