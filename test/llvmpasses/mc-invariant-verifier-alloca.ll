; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: not --crash opt --load-pass-plugin=libjulia-codegen%shlibext -passes='function(MCInvariantVerifier)' -S %s 2>&1 | FileCheck %s

; A constant-size alloca outside the entry block is a dynamic alloca in
; disguise: fresh stack on every visit of its block (unbounded growth in a
; loop), var-sized-frame handling for the whole function. The lowering
; section must never strand one (e.g. by splitting the entry block).
; CHECK: Constant-size alloca outside the entry block
define void @stranded_alloca(i64 %n) {
top:
  br label %loop

loop:
  %iv = phi i64 [ 0, %top ], [ %iv.next, %loop ]
  %slot = alloca [2 x i64], align 8
  store i64 %iv, ptr %slot, align 8
  %iv.next = add i64 %iv, 1
  %done = icmp eq i64 %iv.next, %n
  br i1 %done, label %exit, label %loop

exit:
  ret void
}
