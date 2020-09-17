#ifndef LLVM_TRANSFORMS_SCALAR_HUNDUN_H
#define LLVM_TRANSFORMS_SCALAR_HUNDUN_H

#include "llvm/Pass.h"

namespace llvm {
	ModulePass* createHunDunPass(uint32_t hundun_shm_size, std::string hundun_out_dir);
}
#endif
