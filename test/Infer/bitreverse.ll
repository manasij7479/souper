; REQUIRES: solver, solver-model

; RUN: %llvm-as -o %t1 %s
; RUN: %souper %solver -souper-infer-iN %t1 > %t2
; RUN: %FileCheck %s -check-prefix=SUCCESS < %t2

; SUCCESS: cand %0 -2147483648:i32

; Function Attrs: nounwind readnone
declare i32 @llvm.bitreverse.i32(i32) #0

define i32 @foo(i32 %x) {
entry:
  %rev = call i32 @llvm.bitreverse.i32(i32 1)
  ret i32 %rev
}
