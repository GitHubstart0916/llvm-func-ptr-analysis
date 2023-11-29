#!/bin/bash
run_single_case() {
#  echo $1
  if [ $1 -lt 10 ]; then
        echo "run test0${1}.c"
        #clang-10 -O0 -g3 -S -emit-llvm test0${1}.c -o test0${1}.ll && llvm-as-10 test0${1}.ll -o test0${1}.bc
        clang-10 -O0 -g3 -c -emit-llvm test0${1}.c -o test0${1}.bc
        ../cmake-build-debug/assignment3 test0${1}.bc | tee test0${1}.out
#        echo ""
  fi
  if [ $1 -ge 10 ]; then
        echo "run test${1}.c"
        #clang-10 -O0 -g3 -S -emit-llvm test${1}.c -o test${1}.ll && llvm-as-10 test${1}.ll -o test${1}.bc
        clang-10 -O0 -g3 -c -emit-llvm test${1}.c -o test${1}.bc
        ../cmake-build-debug/assignment3 test${1}.bc | tee test${1}.out
#        echo ""
  fi
}
#clang-10 -O0 -g -S -emit-llvm test05.c -o temp.ll && llvm-as-10 temp.ll -o temp.bc && ../cmake-build-debug/llvmassignment temp.bc

if [ $# -ne 2 ]; then
   echo "param error"
fi

if [ $1 == "-s" ]; then
  run_single_case $2
fi

if [ $1 == "-a" ]; then
    for (( i = 0; i < $2; i++ )); do
        run_single_case $i
    done
fi