; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,function(GCInvariantVerifier),verify' -julia-split-block-threshold=30 -julia-split-chunk-size=16 -S %s | FileCheck %s --check-prefix=CALLER
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,function(GCInvariantVerifier),verify' -julia-split-block-threshold=30 -julia-split-chunk-size=16 -S %s | FileCheck %s --check-prefix=CALLEE
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,function(GCInvariantVerifier),verify' -julia-split-block-threshold=30 -julia-split-chunk-size=16 -julia-split-direct-arg-limit=4 -S %s | FileCheck %s --check-prefix=SPILL
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,function(GCInvariantVerifier,LateLowerGCFrame),verify' -julia-split-block-threshold=30 -julia-split-chunk-size=16 -S %s | FileCheck %s --check-prefix=LOWER
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,function(GCInvariantVerifier),verify' -julia-split-function-threshold=50 -julia-split-chunk-size=40 -S %s | FileCheck %s --check-prefix=MULTI
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,JuliaFunctionSplitting,verify' -julia-split-function-threshold=50 -julia-split-chunk-size=40 -S %s | FileCheck %s --check-prefix=IDEM

declare ptr @julia.get_pgcstack()
declare ptr addrspace(10) @jl_box_int64(i64)
declare void @use(ptr addrspace(10))
declare void @use2(ptr addrspace(10), ptr addrspace(10))
declare i32 @sigsetjmp_ish() returns_twice
declare swiftcc void @callee_with_roots(ptr, ptr)
declare void @pop_handler_ish(ptr, i32) "julia.eh_state"

; Outlined functions carry the "julia.split-function" provenance marker and are
; never re-split by a second invocation of the pass (the pipeline runs it
; twice): the children exceed the 50-instruction function threshold here, so
; without the marker the second run would wrap each one in a shim.
; IDEM-NOT: julia_split.julia_split
; IDEM: define internal {{.*}}julia_split
; IDEM-NOT: julia_split.julia_split

; A long straight-line block of untracked arithmetic is chunked and outlined.
; CALLER-LABEL: define double @straightline(
; CALLER: call void @straightline.julia_split
; CALLER: ret double
; CALLEE: define internal void @straightline.julia_split
; CALLEE-SAME: #[[SPLIT_ATTRS:[0-9]+]]
; CALLEE: fadd double
define double @straightline(double %x) {
top:
  %v1 = fadd double %x, 1.000000e+00
  %v2 = fadd double %v1, 1.000000e+00
  %v3 = fadd double %v2, 1.000000e+00
  %v4 = fadd double %v3, 1.000000e+00
  %v5 = fadd double %v4, 1.000000e+00
  %v6 = fadd double %v5, 1.000000e+00
  %v7 = fadd double %v6, 1.000000e+00
  %v8 = fadd double %v7, 1.000000e+00
  %v9 = fadd double %v8, 1.000000e+00
  %v10 = fadd double %v9, 1.000000e+00
  %v11 = fadd double %v10, 1.000000e+00
  %v12 = fadd double %v11, 1.000000e+00
  %v13 = fadd double %v12, 1.000000e+00
  %v14 = fadd double %v13, 1.000000e+00
  %v15 = fadd double %v14, 1.000000e+00
  %v16 = fadd double %v15, 1.000000e+00
  %v17 = fadd double %v16, 1.000000e+00
  %v18 = fadd double %v17, 1.000000e+00
  %v19 = fadd double %v18, 1.000000e+00
  %v20 = fadd double %v19, 1.000000e+00
  %v21 = fadd double %v20, 1.000000e+00
  %v22 = fadd double %v21, 1.000000e+00
  %v23 = fadd double %v22, 1.000000e+00
  %v24 = fadd double %v23, 1.000000e+00
  %v25 = fadd double %v24, 1.000000e+00
  %v26 = fadd double %v25, 1.000000e+00
  %v27 = fadd double %v26, 1.000000e+00
  %v28 = fadd double %v27, 1.000000e+00
  %v29 = fadd double %v28, 1.000000e+00
  %v30 = fadd double %v29, 1.000000e+00
  %v31 = fadd double %v30, 1.000000e+00
  %v32 = fadd double %v31, 1.000000e+00
  %v33 = fadd double %v32, 1.000000e+00
  %v34 = fadd double %v33, 1.000000e+00
  %v35 = fadd double %v34, 1.000000e+00
  %v36 = fadd double %v35, 1.000000e+00
  %v37 = fadd double %v36, 1.000000e+00
  %v38 = fadd double %v37, 1.000000e+00
  %v39 = fadd double %v38, 1.000000e+00
  %v40 = fadd double %v39, 1.000000e+00
  %v41 = fadd double %v40, 1.000000e+00
  %v42 = fadd double %v41, 1.000000e+00
  %v43 = fadd double %v42, 1.000000e+00
  %v44 = fadd double %v43, 1.000000e+00
  %v45 = fadd double %v44, 1.000000e+00
  %v46 = fadd double %v45, 1.000000e+00
  %v47 = fadd double %v46, 1.000000e+00
  %v48 = fadd double %v47, 1.000000e+00
  %v49 = fadd double %v48, 1.000000e+00
  %v50 = fadd double %v49, 1.000000e+00
  %v51 = fadd double %v50, 1.000000e+00
  %v52 = fadd double %v51, 1.000000e+00
  %v53 = fadd double %v52, 1.000000e+00
  %v54 = fadd double %v53, 1.000000e+00
  %v55 = fadd double %v54, 1.000000e+00
  %v56 = fadd double %v55, 1.000000e+00
  %v57 = fadd double %v56, 1.000000e+00
  %v58 = fadd double %v57, 1.000000e+00
  %v59 = fadd double %v58, 1.000000e+00
  %v60 = fadd double %v59, 1.000000e+00
  ret double %v60
}

; A tracked (addrspace 10) value used in every chunk is passed as an argument
; (assumed rooted by the caller), and callees containing safepoints
; materialize their own pgcstack.
; CALLER-LABEL: define void @tracked(
; CALLER: call void @tracked.julia_split
; CALLEE: define internal void @tracked.julia_split
; CALLEE-SAME: ptr addrspace(10)
; CALLEE: call ptr @julia.get_pgcstack()
; CALLEE: call ptr addrspace(10) @jl_box_int64(
define void @tracked(ptr addrspace(10) %b0) {
top:
  %pg = call ptr @julia.get_pgcstack()
  %b1 = call ptr addrspace(10) @jl_box_int64(i64 1)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b1)
  %b2 = call ptr addrspace(10) @jl_box_int64(i64 2)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b2)
  %b3 = call ptr addrspace(10) @jl_box_int64(i64 3)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b3)
  %b4 = call ptr addrspace(10) @jl_box_int64(i64 4)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b4)
  %b5 = call ptr addrspace(10) @jl_box_int64(i64 5)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b5)
  %b6 = call ptr addrspace(10) @jl_box_int64(i64 6)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b6)
  %b7 = call ptr addrspace(10) @jl_box_int64(i64 7)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b7)
  %b8 = call ptr addrspace(10) @jl_box_int64(i64 8)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b8)
  %b9 = call ptr addrspace(10) @jl_box_int64(i64 9)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b9)
  %b10 = call ptr addrspace(10) @jl_box_int64(i64 10)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b10)
  %b11 = call ptr addrspace(10) @jl_box_int64(i64 11)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b11)
  %b12 = call ptr addrspace(10) @jl_box_int64(i64 12)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b12)
  %b13 = call ptr addrspace(10) @jl_box_int64(i64 13)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b13)
  %b14 = call ptr addrspace(10) @jl_box_int64(i64 14)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b14)
  %b15 = call ptr addrspace(10) @jl_box_int64(i64 15)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b15)
  %b16 = call ptr addrspace(10) @jl_box_int64(i64 16)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b16)
  %b17 = call ptr addrspace(10) @jl_box_int64(i64 17)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b17)
  %b18 = call ptr addrspace(10) @jl_box_int64(i64 18)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b18)
  %b19 = call ptr addrspace(10) @jl_box_int64(i64 19)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b19)
  %b20 = call ptr addrspace(10) @jl_box_int64(i64 20)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b20)
  %b21 = call ptr addrspace(10) @jl_box_int64(i64 21)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b21)
  %b22 = call ptr addrspace(10) @jl_box_int64(i64 22)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b22)
  %b23 = call ptr addrspace(10) @jl_box_int64(i64 23)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b23)
  %b24 = call ptr addrspace(10) @jl_box_int64(i64 24)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b24)
  %b25 = call ptr addrspace(10) @jl_box_int64(i64 25)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b25)
  %b26 = call ptr addrspace(10) @jl_box_int64(i64 26)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b26)
  %b27 = call ptr addrspace(10) @jl_box_int64(i64 27)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b27)
  %b28 = call ptr addrspace(10) @jl_box_int64(i64 28)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b28)
  %b29 = call ptr addrspace(10) @jl_box_int64(i64 29)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b29)
  %b30 = call ptr addrspace(10) @jl_box_int64(i64 30)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b30)
  %b31 = call ptr addrspace(10) @jl_box_int64(i64 31)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b31)
  %b32 = call ptr addrspace(10) @jl_box_int64(i64 32)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b32)
  %b33 = call ptr addrspace(10) @jl_box_int64(i64 33)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b33)
  %b34 = call ptr addrspace(10) @jl_box_int64(i64 34)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b34)
  %b35 = call ptr addrspace(10) @jl_box_int64(i64 35)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b35)
  %b36 = call ptr addrspace(10) @jl_box_int64(i64 36)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b36)
  %b37 = call ptr addrspace(10) @jl_box_int64(i64 37)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b37)
  %b38 = call ptr addrspace(10) @jl_box_int64(i64 38)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b38)
  %b39 = call ptr addrspace(10) @jl_box_int64(i64 39)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b39)
  %b40 = call ptr addrspace(10) @jl_box_int64(i64 40)
  call void @use2(ptr addrspace(10) %b0, ptr addrspace(10) %b40)
  ret void
}

; With a small direct-arg limit, boundary values are spilled through an
; all-tracked alloca, which the caller's GC lowering turns into GC frame
; slots, instead of a wide argument list.
; SPILL-LABEL: define void @wide_interface(
; SPILL: %gcspill{{.*}} = alloca ptr addrspace(10), i32
; SPILL: call void @wide_interface.julia_split
; SPILL: load ptr addrspace(10)
define void @wide_interface(i64 %n) {
top:
  %w0 = call ptr addrspace(10) @jl_box_int64(i64 0)
  %w1 = call ptr addrspace(10) @jl_box_int64(i64 1)
  %w2 = call ptr addrspace(10) @jl_box_int64(i64 2)
  %w3 = call ptr addrspace(10) @jl_box_int64(i64 3)
  %w4 = call ptr addrspace(10) @jl_box_int64(i64 4)
  %w5 = call ptr addrspace(10) @jl_box_int64(i64 5)
  %w6 = call ptr addrspace(10) @jl_box_int64(i64 6)
  %w7 = call ptr addrspace(10) @jl_box_int64(i64 7)
  %w8 = call ptr addrspace(10) @jl_box_int64(i64 8)
  %w9 = call ptr addrspace(10) @jl_box_int64(i64 9)
  %w10 = call ptr addrspace(10) @jl_box_int64(i64 10)
  %w11 = call ptr addrspace(10) @jl_box_int64(i64 11)
  %w12 = call ptr addrspace(10) @jl_box_int64(i64 12)
  %w13 = call ptr addrspace(10) @jl_box_int64(i64 13)
  %w14 = call ptr addrspace(10) @jl_box_int64(i64 14)
  %w15 = call ptr addrspace(10) @jl_box_int64(i64 15)
  %w16 = call ptr addrspace(10) @jl_box_int64(i64 16)
  %w17 = call ptr addrspace(10) @jl_box_int64(i64 17)
  %w18 = call ptr addrspace(10) @jl_box_int64(i64 18)
  %w19 = call ptr addrspace(10) @jl_box_int64(i64 19)
  %w20 = call ptr addrspace(10) @jl_box_int64(i64 20)
  %w21 = call ptr addrspace(10) @jl_box_int64(i64 21)
  %w22 = call ptr addrspace(10) @jl_box_int64(i64 22)
  %w23 = call ptr addrspace(10) @jl_box_int64(i64 23)
  call void @use(ptr addrspace(10) %w0)
  call void @use(ptr addrspace(10) %w1)
  call void @use(ptr addrspace(10) %w2)
  call void @use(ptr addrspace(10) %w3)
  call void @use(ptr addrspace(10) %w4)
  call void @use(ptr addrspace(10) %w5)
  call void @use(ptr addrspace(10) %w6)
  call void @use(ptr addrspace(10) %w7)
  call void @use(ptr addrspace(10) %w8)
  call void @use(ptr addrspace(10) %w9)
  call void @use(ptr addrspace(10) %w10)
  call void @use(ptr addrspace(10) %w11)
  call void @use(ptr addrspace(10) %w12)
  call void @use(ptr addrspace(10) %w13)
  call void @use(ptr addrspace(10) %w14)
  call void @use(ptr addrspace(10) %w15)
  call void @use(ptr addrspace(10) %w16)
  call void @use(ptr addrspace(10) %w17)
  call void @use(ptr addrspace(10) %w18)
  call void @use(ptr addrspace(10) %w19)
  call void @use(ptr addrspace(10) %w20)
  call void @use(ptr addrspace(10) %w21)
  call void @use(ptr addrspace(10) %w22)
  call void @use(ptr addrspace(10) %w23)
  ret void
}

; The returns_twice (exception-handler setjmp) call is never outlined.
; CALLER-LABEL: define double @pinned(
; CALLER: call void @pinned.julia_split
; CALLER: call i32 @sigsetjmp_ish()
; CALLER: ret double
define double @pinned(double %x) {
top:
  %p1 = fadd double %x, 1.000000e+00
  %p2 = fadd double %p1, 1.000000e+00
  %p3 = fadd double %p2, 1.000000e+00
  %p4 = fadd double %p3, 1.000000e+00
  %p5 = fadd double %p4, 1.000000e+00
  %p6 = fadd double %p5, 1.000000e+00
  %p7 = fadd double %p6, 1.000000e+00
  %p8 = fadd double %p7, 1.000000e+00
  %p9 = fadd double %p8, 1.000000e+00
  %p10 = fadd double %p9, 1.000000e+00
  %p11 = fadd double %p10, 1.000000e+00
  %p12 = fadd double %p11, 1.000000e+00
  %p13 = fadd double %p12, 1.000000e+00
  %p14 = fadd double %p13, 1.000000e+00
  %p15 = fadd double %p14, 1.000000e+00
  %p16 = fadd double %p15, 1.000000e+00
  %p17 = fadd double %p16, 1.000000e+00
  %p18 = fadd double %p17, 1.000000e+00
  %p19 = fadd double %p18, 1.000000e+00
  %p20 = fadd double %p19, 1.000000e+00
  %p21 = fadd double %p20, 1.000000e+00
  %p22 = fadd double %p21, 1.000000e+00
  %p23 = fadd double %p22, 1.000000e+00
  %p24 = fadd double %p23, 1.000000e+00
  %p25 = fadd double %p24, 1.000000e+00
  %p26 = fadd double %p25, 1.000000e+00
  %p27 = fadd double %p26, 1.000000e+00
  %p28 = fadd double %p27, 1.000000e+00
  %p29 = fadd double %p28, 1.000000e+00
  %p30 = fadd double %p29, 1.000000e+00
  %jb = call i32 @sigsetjmp_ish()
  %p31 = fadd double %p30, 1.000000e+00
  %p32 = fadd double %p31, 1.000000e+00
  %p33 = fadd double %p32, 1.000000e+00
  %p34 = fadd double %p33, 1.000000e+00
  %p35 = fadd double %p34, 1.000000e+00
  %p36 = fadd double %p35, 1.000000e+00
  %p37 = fadd double %p36, 1.000000e+00
  %p38 = fadd double %p37, 1.000000e+00
  %p39 = fadd double %p38, 1.000000e+00
  %p40 = fadd double %p39, 1.000000e+00
  %p41 = fadd double %p40, 1.000000e+00
  %p42 = fadd double %p41, 1.000000e+00
  %p43 = fadd double %p42, 1.000000e+00
  %p44 = fadd double %p43, 1.000000e+00
  %p45 = fadd double %p44, 1.000000e+00
  %p46 = fadd double %p45, 1.000000e+00
  %p47 = fadd double %p46, 1.000000e+00
  %p48 = fadd double %p47, 1.000000e+00
  %p49 = fadd double %p48, 1.000000e+00
  %p50 = fadd double %p49, 1.000000e+00
  %p51 = fadd double %p50, 1.000000e+00
  %p52 = fadd double %p51, 1.000000e+00
  %p53 = fadd double %p52, 1.000000e+00
  %p54 = fadd double %p53, 1.000000e+00
  %p55 = fadd double %p54, 1.000000e+00
  %p56 = fadd double %p55, 1.000000e+00
  %p57 = fadd double %p56, 1.000000e+00
  %p58 = fadd double %p57, 1.000000e+00
  %p59 = fadd double %p58, 1.000000e+00
  %p60 = fadd double %p59, 1.000000e+00
  ret double %p60
}

; Calls marked "julia.eh_state" at their declaration (exception-handler state
; manipulation: enter/pop handler, excstack save/restore) are never outlined —
; the handler frames they touch are scoped to the C stack frame that entered
; the handler.
; CALLER-LABEL: define double @ehstate(
; CALLER: call void @ehstate.julia_split
; CALLER: call void @pop_handler_ish(ptr null, i32 1)
; CALLER: ret double
define double @ehstate(double %x) {
top:
  %e1 = fadd double %x, 1.000000e+00
  %e2 = fadd double %e1, 1.000000e+00
  %e3 = fadd double %e2, 1.000000e+00
  %e4 = fadd double %e3, 1.000000e+00
  %e5 = fadd double %e4, 1.000000e+00
  %e6 = fadd double %e5, 1.000000e+00
  %e7 = fadd double %e6, 1.000000e+00
  %e8 = fadd double %e7, 1.000000e+00
  %e9 = fadd double %e8, 1.000000e+00
  %e10 = fadd double %e9, 1.000000e+00
  %e11 = fadd double %e10, 1.000000e+00
  %e12 = fadd double %e11, 1.000000e+00
  %e13 = fadd double %e12, 1.000000e+00
  %e14 = fadd double %e13, 1.000000e+00
  %e15 = fadd double %e14, 1.000000e+00
  %e16 = fadd double %e15, 1.000000e+00
  %e17 = fadd double %e16, 1.000000e+00
  %e18 = fadd double %e17, 1.000000e+00
  %e19 = fadd double %e18, 1.000000e+00
  %e20 = fadd double %e19, 1.000000e+00
  %e21 = fadd double %e20, 1.000000e+00
  %e22 = fadd double %e21, 1.000000e+00
  %e23 = fadd double %e22, 1.000000e+00
  %e24 = fadd double %e23, 1.000000e+00
  %e25 = fadd double %e24, 1.000000e+00
  %e26 = fadd double %e25, 1.000000e+00
  %e27 = fadd double %e26, 1.000000e+00
  %e28 = fadd double %e27, 1.000000e+00
  %e29 = fadd double %e28, 1.000000e+00
  %e30 = fadd double %e29, 1.000000e+00
  call void @pop_handler_ish(ptr null, i32 1)
  %e31 = fadd double %e30, 1.000000e+00
  %e32 = fadd double %e31, 1.000000e+00
  %e33 = fadd double %e32, 1.000000e+00
  %e34 = fadd double %e33, 1.000000e+00
  %e35 = fadd double %e34, 1.000000e+00
  %e36 = fadd double %e35, 1.000000e+00
  %e37 = fadd double %e36, 1.000000e+00
  %e38 = fadd double %e37, 1.000000e+00
  %e39 = fadd double %e38, 1.000000e+00
  %e40 = fadd double %e39, 1.000000e+00
  %e41 = fadd double %e40, 1.000000e+00
  %e42 = fadd double %e41, 1.000000e+00
  %e43 = fadd double %e42, 1.000000e+00
  %e44 = fadd double %e43, 1.000000e+00
  %e45 = fadd double %e44, 1.000000e+00
  %e46 = fadd double %e45, 1.000000e+00
  %e47 = fadd double %e46, 1.000000e+00
  %e48 = fadd double %e47, 1.000000e+00
  %e49 = fadd double %e48, 1.000000e+00
  %e50 = fadd double %e49, 1.000000e+00
  %e51 = fadd double %e50, 1.000000e+00
  %e52 = fadd double %e51, 1.000000e+00
  %e53 = fadd double %e52, 1.000000e+00
  %e54 = fadd double %e53, 1.000000e+00
  %e55 = fadd double %e54, 1.000000e+00
  %e56 = fadd double %e55, 1.000000e+00
  %e57 = fadd double %e56, 1.000000e+00
  %e58 = fadd double %e57, 1.000000e+00
  %e59 = fadd double %e58, 1.000000e+00
  %e60 = fadd double %e59, 1.000000e+00
  ret double %e60
}

; A callsite with a "julia.return_roots" buffer is never outlined: the buffer
; must stay an alloca in the same function as the call (LateLowerGCFrame
; registers it as a GC frame array and aborts on a pointer argument), and it
; must outlive reads of the sret aggregate.
; CALLER-LABEL: define double @retroots(
; CALLER: call void @retroots.julia_split
; CALLER: call swiftcc void @callee_with_roots(ptr %sret, ptr "julia.return_roots"="2" %roots)
; CALLER: ret double
define double @retroots(double %x) {
top:
  %sret = alloca [2 x i64], align 8
  %roots = alloca [2 x ptr addrspace(10)], align 8
  %q1 = fadd double %x, 1.000000e+00
  %q2 = fadd double %q1, 1.000000e+00
  %q3 = fadd double %q2, 1.000000e+00
  %q4 = fadd double %q3, 1.000000e+00
  %q5 = fadd double %q4, 1.000000e+00
  %q6 = fadd double %q5, 1.000000e+00
  %q7 = fadd double %q6, 1.000000e+00
  %q8 = fadd double %q7, 1.000000e+00
  %q9 = fadd double %q8, 1.000000e+00
  %q10 = fadd double %q9, 1.000000e+00
  %q11 = fadd double %q10, 1.000000e+00
  %q12 = fadd double %q11, 1.000000e+00
  %q13 = fadd double %q12, 1.000000e+00
  %q14 = fadd double %q13, 1.000000e+00
  %q15 = fadd double %q14, 1.000000e+00
  %q16 = fadd double %q15, 1.000000e+00
  %q17 = fadd double %q16, 1.000000e+00
  %q18 = fadd double %q17, 1.000000e+00
  %q19 = fadd double %q18, 1.000000e+00
  %q20 = fadd double %q19, 1.000000e+00
  %q21 = fadd double %q20, 1.000000e+00
  %q22 = fadd double %q21, 1.000000e+00
  %q23 = fadd double %q22, 1.000000e+00
  %q24 = fadd double %q23, 1.000000e+00
  %q25 = fadd double %q24, 1.000000e+00
  %q26 = fadd double %q25, 1.000000e+00
  %q27 = fadd double %q26, 1.000000e+00
  %q28 = fadd double %q27, 1.000000e+00
  %q29 = fadd double %q28, 1.000000e+00
  %q30 = fadd double %q29, 1.000000e+00
  call swiftcc void @callee_with_roots(ptr %sret, ptr "julia.return_roots"="2" %roots)
  %q31 = fadd double %q30, 1.000000e+00
  %q32 = fadd double %q31, 1.000000e+00
  %q33 = fadd double %q32, 1.000000e+00
  %q34 = fadd double %q33, 1.000000e+00
  %q35 = fadd double %q34, 1.000000e+00
  %q36 = fadd double %q35, 1.000000e+00
  %q37 = fadd double %q36, 1.000000e+00
  %q38 = fadd double %q37, 1.000000e+00
  %q39 = fadd double %q38, 1.000000e+00
  %q40 = fadd double %q39, 1.000000e+00
  %q41 = fadd double %q40, 1.000000e+00
  %q42 = fadd double %q41, 1.000000e+00
  %q43 = fadd double %q42, 1.000000e+00
  %q44 = fadd double %q43, 1.000000e+00
  %q45 = fadd double %q44, 1.000000e+00
  %q46 = fadd double %q45, 1.000000e+00
  %q47 = fadd double %q46, 1.000000e+00
  %q48 = fadd double %q47, 1.000000e+00
  %q49 = fadd double %q48, 1.000000e+00
  %q50 = fadd double %q49, 1.000000e+00
  %q51 = fadd double %q50, 1.000000e+00
  %q52 = fadd double %q51, 1.000000e+00
  %q53 = fadd double %q52, 1.000000e+00
  %q54 = fadd double %q53, 1.000000e+00
  %q55 = fadd double %q54, 1.000000e+00
  %q56 = fadd double %q55, 1.000000e+00
  %q57 = fadd double %q56, 1.000000e+00
  %q58 = fadd double %q57, 1.000000e+00
  %q59 = fadd double %q58, 1.000000e+00
  %q60 = fadd double %q59, 1.000000e+00
  ret double %q60
}

; Derived (addrspace 11) pointers never escape an outlined chunk: their
; derivation spine is rematerialized in the caller (hoisted to the region
; preheader when computable from values available before the region).
; CALLER-LABEL: define double @derived(
; CALLER: .remat = addrspacecast ptr addrspace(10)
; CALLER: call void @derived.julia_split
define double @derived(ptr addrspace(10) %obj, double %x) !dbg !5 {
top:
  %d1 = fadd double %x, 1.000000e+00
  %d2 = fadd double %d1, 1.000000e+00
  %d3 = fadd double %d2, 1.000000e+00
  %d4 = fadd double %d3, 1.000000e+00
  %d5 = fadd double %d4, 1.000000e+00
  %d6 = fadd double %d5, 1.000000e+00
  %d7 = fadd double %d6, 1.000000e+00
  %d8 = fadd double %d7, 1.000000e+00
  %d9 = fadd double %d8, 1.000000e+00
  %d10 = fadd double %d9, 1.000000e+00
  %d11 = fadd double %d10, 1.000000e+00
  %d12 = fadd double %d11, 1.000000e+00
  %d13 = fadd double %d12, 1.000000e+00
  %d14 = fadd double %d13, 1.000000e+00
  %d15 = fadd double %d14, 1.000000e+00
  %d16 = fadd double %d15, 1.000000e+00
  %d17 = fadd double %d16, 1.000000e+00
  %d18 = fadd double %d17, 1.000000e+00
  %d19 = fadd double %d18, 1.000000e+00
  %d20 = fadd double %d19, 1.000000e+00
  %dcast = addrspacecast ptr addrspace(10) %obj to ptr addrspace(11), !dbg !9
  %dptr = getelementptr inbounds double, ptr addrspace(11) %dcast, i64 2, !dbg !9
  %l21 = load double, ptr addrspace(11) %dptr, align 8
  %d21 = fadd double %d20, %l21
  %l22 = load double, ptr addrspace(11) %dptr, align 8
  %d22 = fadd double %d21, %l22
  %l23 = load double, ptr addrspace(11) %dptr, align 8
  %d23 = fadd double %d22, %l23
  %l24 = load double, ptr addrspace(11) %dptr, align 8
  %d24 = fadd double %d23, %l24
  %l25 = load double, ptr addrspace(11) %dptr, align 8
  %d25 = fadd double %d24, %l25
  %l26 = load double, ptr addrspace(11) %dptr, align 8
  %d26 = fadd double %d25, %l26
  %l27 = load double, ptr addrspace(11) %dptr, align 8
  %d27 = fadd double %d26, %l27
  %l28 = load double, ptr addrspace(11) %dptr, align 8
  %d28 = fadd double %d27, %l28
  %l29 = load double, ptr addrspace(11) %dptr, align 8
  %d29 = fadd double %d28, %l29
  %l30 = load double, ptr addrspace(11) %dptr, align 8
  %d30 = fadd double %d29, %l30
  %l31 = load double, ptr addrspace(11) %dptr, align 8
  %d31 = fadd double %d30, %l31
  %l32 = load double, ptr addrspace(11) %dptr, align 8
  %d32 = fadd double %d31, %l32
  %l33 = load double, ptr addrspace(11) %dptr, align 8
  %d33 = fadd double %d32, %l33
  %l34 = load double, ptr addrspace(11) %dptr, align 8
  %d34 = fadd double %d33, %l34
  %l35 = load double, ptr addrspace(11) %dptr, align 8
  %d35 = fadd double %d34, %l35
  %l36 = load double, ptr addrspace(11) %dptr, align 8
  %d36 = fadd double %d35, %l36
  %l37 = load double, ptr addrspace(11) %dptr, align 8
  %d37 = fadd double %d36, %l37
  %l38 = load double, ptr addrspace(11) %dptr, align 8
  %d38 = fadd double %d37, %l38
  %l39 = load double, ptr addrspace(11) %dptr, align 8
  %d39 = fadd double %d38, %l39
  %l40 = load double, ptr addrspace(11) %dptr, align 8
  %d40 = fadd double %d39, %l40
  %l41 = load double, ptr addrspace(11) %dptr, align 8
  %d41 = fadd double %d40, %l41
  %l42 = load double, ptr addrspace(11) %dptr, align 8
  %d42 = fadd double %d41, %l42
  %l43 = load double, ptr addrspace(11) %dptr, align 8
  %d43 = fadd double %d42, %l43
  %l44 = load double, ptr addrspace(11) %dptr, align 8
  %d44 = fadd double %d43, %l44
  %l45 = load double, ptr addrspace(11) %dptr, align 8
  %d45 = fadd double %d44, %l45
  %l46 = load double, ptr addrspace(11) %dptr, align 8
  %d46 = fadd double %d45, %l46
  %l47 = load double, ptr addrspace(11) %dptr, align 8
  %d47 = fadd double %d46, %l47
  %l48 = load double, ptr addrspace(11) %dptr, align 8
  %d48 = fadd double %d47, %l48
  %l49 = load double, ptr addrspace(11) %dptr, align 8
  %d49 = fadd double %d48, %l49
  %l50 = load double, ptr addrspace(11) %dptr, align 8
  %d50 = fadd double %d49, %l50
  %l51 = load double, ptr addrspace(11) %dptr, align 8
  %d51 = fadd double %d50, %l51
  %l52 = load double, ptr addrspace(11) %dptr, align 8
  %d52 = fadd double %d51, %l52
  %l53 = load double, ptr addrspace(11) %dptr, align 8
  %d53 = fadd double %d52, %l53
  %l54 = load double, ptr addrspace(11) %dptr, align 8
  %d54 = fadd double %d53, %l54
  %l55 = load double, ptr addrspace(11) %dptr, align 8
  %d55 = fadd double %d54, %l55
  %l56 = load double, ptr addrspace(11) %dptr, align 8
  %d56 = fadd double %d55, %l56
  %l57 = load double, ptr addrspace(11) %dptr, align 8
  %d57 = fadd double %d56, %l57
  %l58 = load double, ptr addrspace(11) %dptr, align 8
  %d58 = fadd double %d57, %l58
  %l59 = load double, ptr addrspace(11) %dptr, align 8
  %d59 = fadd double %d58, %l59
  %l60 = load double, ptr addrspace(11) %dptr, align 8
  %d60 = fadd double %d59, %l60
  ret double %d60
}

; The outlined functions are internal, marked noinline, and carry the
; provenance marker that stops later pass invocations from re-splitting them.
; CALLEE: attributes #[[SPLIT_ATTRS]] = {
; CALLEE-SAME: noinline
; CALLEE-SAME: "julia.split-function"

; After LateLowerGCFrame, outlined callees with safepoints get their own GC frame.
; LOWER: define internal void @tracked.julia_split
; LOWER: @julia.new_gc_frame(

; Debug info: the @derived remat spine carries a location inlined from
; @inlinee. There must be exactly one compile unit and one subprogram per
; function after splitting (the verifier RUN lines catch cloned duplicates).
!llvm.module.flags = !{!0}
!llvm.dbg.cu = !{!1}
!0 = !{i32 2, !"Debug Info Version", i32 3}
!1 = distinct !DICompileUnit(language: DW_LANG_Julia, file: !2, producer: "julia", isOptimized: true, runtimeVersion: 0, emissionKind: NoDebug)
!2 = !DIFile(filename: "t.jl", directory: ".")
!3 = !{}
!4 = !DISubroutineType(types: !3)
!5 = distinct !DISubprogram(name: "derived", linkageName: "julia_derived", scope: null, file: !2, line: 1, type: !4, scopeLine: 1, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !1)
!6 = distinct !DISubprogram(name: "inlinee", linkageName: "julia_inlinee", scope: null, file: !2, line: 90, type: !4, scopeLine: 90, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !1)
!7 = !DILocation(line: 5, column: 1, scope: !5)
!9 = !DILocation(line: 99, column: 3, scope: !6, inlinedAt: !7)

; A function made of many small diamonds (no oversized block) is split into
; multi-block regions when it exceeds the function threshold.
; MULTI-LABEL: define double @diamonds(
; MULTI: call {{.*}}@diamonds.julia_split
; MULTI: define internal {{.*}}@diamonds.julia_split
; MULTI: br i1
define double @diamonds(double %x) {
top:
  br label %cond1
cond1:
  %c1 = fcmp ogt double %x, 5.000000e-01
  br i1 %c1, label %t1, label %f1
t1:
  %tv1 = fadd double %x, 1.250000e-01
  br label %j1
f1:
  %fv1 = fmul double %x, 7.500000e-01
  br label %j1
j1:
  %v1 = phi double [ %tv1, %t1 ], [ %fv1, %f1 ]
  br label %cond2
cond2:
  %c2 = fcmp ogt double %v1, 5.000000e-01
  br i1 %c2, label %t2, label %f2
t2:
  %tv2 = fadd double %v1, 1.250000e-01
  br label %j2
f2:
  %fv2 = fmul double %v1, 7.500000e-01
  br label %j2
j2:
  %v2 = phi double [ %tv2, %t2 ], [ %fv2, %f2 ]
  br label %cond3
cond3:
  %c3 = fcmp ogt double %v2, 5.000000e-01
  br i1 %c3, label %t3, label %f3
t3:
  %tv3 = fadd double %v2, 1.250000e-01
  br label %j3
f3:
  %fv3 = fmul double %v2, 7.500000e-01
  br label %j3
j3:
  %v3 = phi double [ %tv3, %t3 ], [ %fv3, %f3 ]
  br label %cond4
cond4:
  %c4 = fcmp ogt double %v3, 5.000000e-01
  br i1 %c4, label %t4, label %f4
t4:
  %tv4 = fadd double %v3, 1.250000e-01
  br label %j4
f4:
  %fv4 = fmul double %v3, 7.500000e-01
  br label %j4
j4:
  %v4 = phi double [ %tv4, %t4 ], [ %fv4, %f4 ]
  br label %cond5
cond5:
  %c5 = fcmp ogt double %v4, 5.000000e-01
  br i1 %c5, label %t5, label %f5
t5:
  %tv5 = fadd double %v4, 1.250000e-01
  br label %j5
f5:
  %fv5 = fmul double %v4, 7.500000e-01
  br label %j5
j5:
  %v5 = phi double [ %tv5, %t5 ], [ %fv5, %f5 ]
  br label %cond6
cond6:
  %c6 = fcmp ogt double %v5, 5.000000e-01
  br i1 %c6, label %t6, label %f6
t6:
  %tv6 = fadd double %v5, 1.250000e-01
  br label %j6
f6:
  %fv6 = fmul double %v5, 7.500000e-01
  br label %j6
j6:
  %v6 = phi double [ %tv6, %t6 ], [ %fv6, %f6 ]
  br label %cond7
cond7:
  %c7 = fcmp ogt double %v6, 5.000000e-01
  br i1 %c7, label %t7, label %f7
t7:
  %tv7 = fadd double %v6, 1.250000e-01
  br label %j7
f7:
  %fv7 = fmul double %v6, 7.500000e-01
  br label %j7
j7:
  %v7 = phi double [ %tv7, %t7 ], [ %fv7, %f7 ]
  br label %cond8
cond8:
  %c8 = fcmp ogt double %v7, 5.000000e-01
  br i1 %c8, label %t8, label %f8
t8:
  %tv8 = fadd double %v7, 1.250000e-01
  br label %j8
f8:
  %fv8 = fmul double %v7, 7.500000e-01
  br label %j8
j8:
  %v8 = phi double [ %tv8, %t8 ], [ %fv8, %f8 ]
  br label %cond9
cond9:
  %c9 = fcmp ogt double %v8, 5.000000e-01
  br i1 %c9, label %t9, label %f9
t9:
  %tv9 = fadd double %v8, 1.250000e-01
  br label %j9
f9:
  %fv9 = fmul double %v8, 7.500000e-01
  br label %j9
j9:
  %v9 = phi double [ %tv9, %t9 ], [ %fv9, %f9 ]
  br label %cond10
cond10:
  %c10 = fcmp ogt double %v9, 5.000000e-01
  br i1 %c10, label %t10, label %f10
t10:
  %tv10 = fadd double %v9, 1.250000e-01
  br label %j10
f10:
  %fv10 = fmul double %v9, 7.500000e-01
  br label %j10
j10:
  %v10 = phi double [ %tv10, %t10 ], [ %fv10, %f10 ]
  br label %cond11
cond11:
  %c11 = fcmp ogt double %v10, 5.000000e-01
  br i1 %c11, label %t11, label %f11
t11:
  %tv11 = fadd double %v10, 1.250000e-01
  br label %j11
f11:
  %fv11 = fmul double %v10, 7.500000e-01
  br label %j11
j11:
  %v11 = phi double [ %tv11, %t11 ], [ %fv11, %f11 ]
  br label %cond12
cond12:
  %c12 = fcmp ogt double %v11, 5.000000e-01
  br i1 %c12, label %t12, label %f12
t12:
  %tv12 = fadd double %v11, 1.250000e-01
  br label %j12
f12:
  %fv12 = fmul double %v11, 7.500000e-01
  br label %j12
j12:
  %v12 = phi double [ %tv12, %t12 ], [ %fv12, %f12 ]
  br label %cond13
cond13:
  %c13 = fcmp ogt double %v12, 5.000000e-01
  br i1 %c13, label %t13, label %f13
t13:
  %tv13 = fadd double %v12, 1.250000e-01
  br label %j13
f13:
  %fv13 = fmul double %v12, 7.500000e-01
  br label %j13
j13:
  %v13 = phi double [ %tv13, %t13 ], [ %fv13, %f13 ]
  br label %cond14
cond14:
  %c14 = fcmp ogt double %v13, 5.000000e-01
  br i1 %c14, label %t14, label %f14
t14:
  %tv14 = fadd double %v13, 1.250000e-01
  br label %j14
f14:
  %fv14 = fmul double %v13, 7.500000e-01
  br label %j14
j14:
  %v14 = phi double [ %tv14, %t14 ], [ %fv14, %f14 ]
  br label %cond15
cond15:
  %c15 = fcmp ogt double %v14, 5.000000e-01
  br i1 %c15, label %t15, label %f15
t15:
  %tv15 = fadd double %v14, 1.250000e-01
  br label %j15
f15:
  %fv15 = fmul double %v14, 7.500000e-01
  br label %j15
j15:
  %v15 = phi double [ %tv15, %t15 ], [ %fv15, %f15 ]
  br label %cond16
cond16:
  %c16 = fcmp ogt double %v15, 5.000000e-01
  br i1 %c16, label %t16, label %f16
t16:
  %tv16 = fadd double %v15, 1.250000e-01
  br label %j16
f16:
  %fv16 = fmul double %v15, 7.500000e-01
  br label %j16
j16:
  %v16 = phi double [ %tv16, %t16 ], [ %fv16, %f16 ]
  br label %cond17
cond17:
  %c17 = fcmp ogt double %v16, 5.000000e-01
  br i1 %c17, label %t17, label %f17
t17:
  %tv17 = fadd double %v16, 1.250000e-01
  br label %j17
f17:
  %fv17 = fmul double %v16, 7.500000e-01
  br label %j17
j17:
  %v17 = phi double [ %tv17, %t17 ], [ %fv17, %f17 ]
  br label %cond18
cond18:
  %c18 = fcmp ogt double %v17, 5.000000e-01
  br i1 %c18, label %t18, label %f18
t18:
  %tv18 = fadd double %v17, 1.250000e-01
  br label %j18
f18:
  %fv18 = fmul double %v17, 7.500000e-01
  br label %j18
j18:
  %v18 = phi double [ %tv18, %t18 ], [ %fv18, %f18 ]
  br label %cond19
cond19:
  %c19 = fcmp ogt double %v18, 5.000000e-01
  br i1 %c19, label %t19, label %f19
t19:
  %tv19 = fadd double %v18, 1.250000e-01
  br label %j19
f19:
  %fv19 = fmul double %v18, 7.500000e-01
  br label %j19
j19:
  %v19 = phi double [ %tv19, %t19 ], [ %fv19, %f19 ]
  br label %cond20
cond20:
  %c20 = fcmp ogt double %v19, 5.000000e-01
  br i1 %c20, label %t20, label %f20
t20:
  %tv20 = fadd double %v19, 1.250000e-01
  br label %j20
f20:
  %fv20 = fmul double %v19, 7.500000e-01
  br label %j20
j20:
  %v20 = phi double [ %tv20, %t20 ], [ %fv20, %f20 ]
  br label %cond21
cond21:
  %c21 = fcmp ogt double %v20, 5.000000e-01
  br i1 %c21, label %t21, label %f21
t21:
  %tv21 = fadd double %v20, 1.250000e-01
  br label %j21
f21:
  %fv21 = fmul double %v20, 7.500000e-01
  br label %j21
j21:
  %v21 = phi double [ %tv21, %t21 ], [ %fv21, %f21 ]
  br label %cond22
cond22:
  %c22 = fcmp ogt double %v21, 5.000000e-01
  br i1 %c22, label %t22, label %f22
t22:
  %tv22 = fadd double %v21, 1.250000e-01
  br label %j22
f22:
  %fv22 = fmul double %v21, 7.500000e-01
  br label %j22
j22:
  %v22 = phi double [ %tv22, %t22 ], [ %fv22, %f22 ]
  br label %cond23
cond23:
  %c23 = fcmp ogt double %v22, 5.000000e-01
  br i1 %c23, label %t23, label %f23
t23:
  %tv23 = fadd double %v22, 1.250000e-01
  br label %j23
f23:
  %fv23 = fmul double %v22, 7.500000e-01
  br label %j23
j23:
  %v23 = phi double [ %tv23, %t23 ], [ %fv23, %f23 ]
  br label %cond24
cond24:
  %c24 = fcmp ogt double %v23, 5.000000e-01
  br i1 %c24, label %t24, label %f24
t24:
  %tv24 = fadd double %v23, 1.250000e-01
  br label %j24
f24:
  %fv24 = fmul double %v23, 7.500000e-01
  br label %j24
j24:
  %v24 = phi double [ %tv24, %t24 ], [ %fv24, %f24 ]
  br label %cond25
cond25:
  %c25 = fcmp ogt double %v24, 5.000000e-01
  br i1 %c25, label %t25, label %f25
t25:
  %tv25 = fadd double %v24, 1.250000e-01
  br label %j25
f25:
  %fv25 = fmul double %v24, 7.500000e-01
  br label %j25
j25:
  %v25 = phi double [ %tv25, %t25 ], [ %fv25, %f25 ]
  br label %cond26
cond26:
  %c26 = fcmp ogt double %v25, 5.000000e-01
  br i1 %c26, label %t26, label %f26
t26:
  %tv26 = fadd double %v25, 1.250000e-01
  br label %j26
f26:
  %fv26 = fmul double %v25, 7.500000e-01
  br label %j26
j26:
  %v26 = phi double [ %tv26, %t26 ], [ %fv26, %f26 ]
  br label %cond27
cond27:
  %c27 = fcmp ogt double %v26, 5.000000e-01
  br i1 %c27, label %t27, label %f27
t27:
  %tv27 = fadd double %v26, 1.250000e-01
  br label %j27
f27:
  %fv27 = fmul double %v26, 7.500000e-01
  br label %j27
j27:
  %v27 = phi double [ %tv27, %t27 ], [ %fv27, %f27 ]
  br label %cond28
cond28:
  %c28 = fcmp ogt double %v27, 5.000000e-01
  br i1 %c28, label %t28, label %f28
t28:
  %tv28 = fadd double %v27, 1.250000e-01
  br label %j28
f28:
  %fv28 = fmul double %v27, 7.500000e-01
  br label %j28
j28:
  %v28 = phi double [ %tv28, %t28 ], [ %fv28, %f28 ]
  br label %cond29
cond29:
  %c29 = fcmp ogt double %v28, 5.000000e-01
  br i1 %c29, label %t29, label %f29
t29:
  %tv29 = fadd double %v28, 1.250000e-01
  br label %j29
f29:
  %fv29 = fmul double %v28, 7.500000e-01
  br label %j29
j29:
  %v29 = phi double [ %tv29, %t29 ], [ %fv29, %f29 ]
  br label %cond30
cond30:
  %c30 = fcmp ogt double %v29, 5.000000e-01
  br i1 %c30, label %t30, label %f30
t30:
  %tv30 = fadd double %v29, 1.250000e-01
  br label %j30
f30:
  %fv30 = fmul double %v29, 7.500000e-01
  br label %j30
j30:
  %v30 = phi double [ %tv30, %t30 ], [ %fv30, %f30 ]
  br label %done
done:
  ret double %v30
}
