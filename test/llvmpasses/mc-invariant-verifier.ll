; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='function(MCInvariantVerifier),verify' -S %s | FileCheck %s

; Legal post-lowering IR: entry-block static allocas, genuinely variable-size
; allocas, and marker intrinsics that survive lowering are all accepted.
declare void @llvm.lifetime.start.p0(i64, ptr)

; CHECK-LABEL: @legal_lowered
define void @legal_lowered(i64 %n, i1 %c) {
top:
  %static = alloca [4 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 32, ptr %static)
  br i1 %c, label %then, label %exit

then:
  %dynamic = alloca i64, i64 %n, align 8
  store i64 %n, ptr %dynamic, align 8
  br label %exit

exit:
  ret void
}
