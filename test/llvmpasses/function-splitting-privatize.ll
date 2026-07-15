; This file is a part of Julia. License is MIT: https://julialang.org/license

; Regression test: privatizeRootBuffers clones a shared GC-frame alloca and its
; address chain (an addrspacecast for slot 0, a gep+8 for slot 1) into each
; region. The clone of each address computation must be inserted after its
; base, not at the block's first insertion point, or the cloned gep/cast lands
; ahead of the alloca it derives from and fails to dominate its uses. The
; `verify` in the pipeline catches that regression.

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,verify' -julia-split-function-threshold=20 -julia-split-block-threshold=16 -julia-split-block-insts=16 -julia-split-region-insts=0 -S %s | FileCheck %s

define ptr addrspace(10) @priv(ptr addrspace(10) %a, ptr addrspace(10) %b, i64 %n) {
top:
  %frame = alloca [2 x ptr addrspace(10)], align 16
  %e0 = add i64 %n, 1
  %e1 = add i64 %e0, 2
  %e2 = add i64 %e1, 3
  %e3 = add i64 %e2, 4
  %e4 = add i64 %e3, 5
  %e5 = add i64 %e4, 6
  %e6 = add i64 %e5, 7
  %e7 = add i64 %e6, 8
  %e8 = add i64 %e7, 9
  %e9 = add i64 %e8, 10
  %e10 = add i64 %e9, 11
  %e11 = add i64 %e10, 12
  %e12 = add i64 %e11, 13
  %e13 = add i64 %e12, 14
  %e14 = add i64 %e13, 15
  %e15 = add i64 %e14, 16
  %e16 = add i64 %e15, 17
  %e17 = add i64 %e16, 18
  %e18 = add i64 %e17, 19
  %e19 = add i64 %e18, 20
  %s0 = addrspacecast ptr %frame to ptr addrspace(11)
  %g1 = getelementptr inbounds i8, ptr %frame, i64 8
  %s1 = addrspacecast ptr %g1 to ptr addrspace(11)
  store ptr addrspace(10) %a, ptr addrspace(11) %s0, align 8
  store ptr addrspace(10) %b, ptr addrspace(11) %s1, align 8
  %r0 = load ptr addrspace(10), ptr addrspace(11) %s0, align 8
  %r1 = load ptr addrspace(10), ptr addrspace(11) %s1, align 8
  %x0 = ptrtoint ptr addrspace(10) %r0 to i64
  %x1 = ptrtoint ptr addrspace(10) %r1 to i64
  %w0 = add i64 %x0, %x1
  %w1 = add i64 %w0, %x1
  %w2 = add i64 %w1, %x1
  %w3 = add i64 %w2, %x1
  %w4 = add i64 %w3, %x1
  %w5 = add i64 %w4, %x1
  %w6 = add i64 %w5, %x1
  %w7 = add i64 %w6, %x1
  %w8 = add i64 %w7, %x1
  %w9 = add i64 %w8, %x1
  %w10 = add i64 %w9, %x1
  %w11 = add i64 %w10, %x1
  %w12 = add i64 %w11, %x1
  %w13 = add i64 %w12, %x1
  %w14 = add i64 %w13, %x1
  %w15 = add i64 %w14, %x1
  %w16 = add i64 %w15, %x1
  %w17 = add i64 %w16, %x1
  %w18 = add i64 %w17, %x1
  %w19 = add i64 %w18, %x1
  %p = inttoptr i64 %w19 to ptr addrspace(10)
  ret ptr addrspace(10) %p
}

; The pass runs (a region was outlined); the file passing `verify` is the
; actual assertion.
; CHECK: @priv.julia_split
