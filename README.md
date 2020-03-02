# 11vm

1. `mkdir build & cd build`
2. `cmake -G "Unix Makefiles" -DLLVM_ENABLE_PROJECTS="clang;lld" -DCMAKE_BUILD_TYPE=Release -LLVM_TARGETS_TO_BUILD=X86 ../llvm`
3. `make -j\`nproc\``
