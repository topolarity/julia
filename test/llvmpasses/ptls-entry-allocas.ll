; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='LowerPTLSPass<imaging>,function(MCInvariantVerifier),verify' -S %s | FileCheck %s

; Imaging-mode pgcstack lowering splits the entry block at the getter call.
; The entry block keeps a contiguous leading run of allocas ending at that
; call (codegen anchors its alloca insertion point on the call itself), so
; the split leaves every alloca in the entry block. MCInvariantVerifier
; enforces the convention on the lowered output.
target triple = "x86_64-unknown-linux-gnu"

declare ptr @julia.get_pgcstack()

; CHECK-LABEL: define void @allocas_stay_static(
; CHECK-NEXT: top:
; CHECK-NEXT: %slot1 = alloca [6 x i64]
; CHECK-NEXT: %slot2 = alloca i64
define void @allocas_stay_static(i64 %n) {
top:
  %slot1 = alloca [6 x i64], align 8
  %slot2 = alloca i64, align 8
  %pg = call ptr @julia.get_pgcstack()
  store ptr %pg, ptr %slot1, align 8
  br label %loop

loop:
  %iv = phi i64 [ 0, %top ], [ %iv.next, %loop ]
  store i64 %iv, ptr %slot2, align 8
  %iv.next = add i64 %iv, 1
  %done = icmp eq i64 %iv.next, %n
  br i1 %done, label %exit, label %loop

exit:
  ret void
}
