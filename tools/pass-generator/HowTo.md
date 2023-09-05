Optimize a program with a generated matcher
-------------------------------------------

- Build a souper branch with generalization support. (https://github.com/manasij7479/souper/tree/generalization)
- Obtain or generate matcher source code and copy it to $SOUPER_SRC/tools/pass-generator/src/gen.cpp.inc
- Build the matcher - Separate build directory somewhere and cmake $SOUPER_SRC/tools/pass-generator/; make
- The shared library location (path + file name) generated by step #3 goes in the env var SOUPER_MATCHER_LIB
- $SOUPER_BUILD/mclang and $SOUPER_BUILD/mclang++ can used as a drop in replacement to clang. The extra env variable SOUPER_DISABLE_LLVM_PEEPHOLES has to be set to mimic the experimental setup in the paper.
