; REQUIRES: solver

; RUN: %llvm-as -o %t %s
; RUN: %souper %solver -check %t

; Function Attrs: nounwind readnone
declare i2 @llvm.bitreverse.i2(i2) #0
declare i1 @llvm.bitreverse.i1(i1) #0


define i1 @foo1(i1) local_unnamed_addr #0 {
  %rev = call i1 @llvm.bitreverse.i1(i1 %0)
  %cmp1 = icmp eq i1 %rev, %0, !expected !1
  ret i1 %0
}

define i2 @foo2(i2) local_unnamed_addr #0 {
  %b1 = shl i2 %0, 1
  %b2 = and i2 %0, 2
  %b3 = lshr i2 %b2, 1
  %b4 = or i2 %b1, %b3
  %rev = call i2 @llvm.bitreverse.i2(i2 %0)
  %cmp1 = icmp eq i2 %rev, %b4, !expected !1
  ret i2 %0
}

!1 = !{i1 1}
