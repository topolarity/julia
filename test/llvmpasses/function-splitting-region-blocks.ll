; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,verify' -julia-split-function-threshold=20 -julia-split-region-insts=400 -julia-split-region-blocks=0 -S %s | FileCheck %s --check-prefix=NOCAP
; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='JuliaFunctionSplitting,verify' -julia-split-function-threshold=20 -julia-split-region-insts=400 -julia-split-region-blocks=8 -S %s | FileCheck %s --check-prefix=BLKCAP

declare ptr @julia.get_pgcstack()

; A branchy chain of 20 small diamonds (~7 instructions across 3 blocks each).
; Without a block cap the function is under every enabled region cap (141
; instructions < the 400-instruction target, no safepoints, block cap
; disabled), so outlining must NOT trigger at all: a function under every cap
; already satisfies every per-function cost bound the caps enforce, and
; extracting it (previously: essentially whole, into one same-sized region)
; would pay interface marshalling and a boundary call for zero compile
; benefit. With -julia-split-region-blocks=8 the same function exceeds the
; block cap and the region grower must cut roughly every eight blocks (between
; two and three diamonds), yielding several regions. The per-region compile
; cost of the CFG-walk passes (GVN's PHI-translated non-local memory-dependency
; analysis) grows with instructions x branchy blocks, which is what the cap
; bounds.

; NOCAP-LABEL: define double @blockdense(
; NOCAP-NOT: call void @blockdense.julia_split
; NOCAP-NOT: define internal void @blockdense.julia_split

; BLKCAP-LABEL: define double @blockdense(
; BLKCAP-COUNT-3: call void @blockdense.julia_split

define double @blockdense(double %x) {
entry:
  %v0 = fadd double %x, 5.000000e-01
  br label %d0h
d0h:
  %c0 = fcmp ogt double %v0, 0.000000e+00
  br i1 %c0, label %d0a, label %d0b
d0a:
  %a0 = fadd double %v0, 1.000000e+00
  br label %d0m
d0b:
  %b0 = fmul double %v0, 2.000000e+00
  br label %d0m
d0m:
  %v1 = phi double [ %a0, %d0a ], [ %b0, %d0b ]
  br label %d1h
d1h:
  %c1 = fcmp ogt double %v1, 0.000000e+00
  br i1 %c1, label %d1a, label %d1b
d1a:
  %a1 = fadd double %v1, 1.000000e+00
  br label %d1m
d1b:
  %b1 = fmul double %v1, 2.000000e+00
  br label %d1m
d1m:
  %v2 = phi double [ %a1, %d1a ], [ %b1, %d1b ]
  br label %d2h
d2h:
  %c2 = fcmp ogt double %v2, 0.000000e+00
  br i1 %c2, label %d2a, label %d2b
d2a:
  %a2 = fadd double %v2, 1.000000e+00
  br label %d2m
d2b:
  %b2 = fmul double %v2, 2.000000e+00
  br label %d2m
d2m:
  %v3 = phi double [ %a2, %d2a ], [ %b2, %d2b ]
  br label %d3h
d3h:
  %c3 = fcmp ogt double %v3, 0.000000e+00
  br i1 %c3, label %d3a, label %d3b
d3a:
  %a3 = fadd double %v3, 1.000000e+00
  br label %d3m
d3b:
  %b3 = fmul double %v3, 2.000000e+00
  br label %d3m
d3m:
  %v4 = phi double [ %a3, %d3a ], [ %b3, %d3b ]
  br label %d4h
d4h:
  %c4 = fcmp ogt double %v4, 0.000000e+00
  br i1 %c4, label %d4a, label %d4b
d4a:
  %a4 = fadd double %v4, 1.000000e+00
  br label %d4m
d4b:
  %b4 = fmul double %v4, 2.000000e+00
  br label %d4m
d4m:
  %v5 = phi double [ %a4, %d4a ], [ %b4, %d4b ]
  br label %d5h
d5h:
  %c5 = fcmp ogt double %v5, 0.000000e+00
  br i1 %c5, label %d5a, label %d5b
d5a:
  %a5 = fadd double %v5, 1.000000e+00
  br label %d5m
d5b:
  %b5 = fmul double %v5, 2.000000e+00
  br label %d5m
d5m:
  %v6 = phi double [ %a5, %d5a ], [ %b5, %d5b ]
  br label %d6h
d6h:
  %c6 = fcmp ogt double %v6, 0.000000e+00
  br i1 %c6, label %d6a, label %d6b
d6a:
  %a6 = fadd double %v6, 1.000000e+00
  br label %d6m
d6b:
  %b6 = fmul double %v6, 2.000000e+00
  br label %d6m
d6m:
  %v7 = phi double [ %a6, %d6a ], [ %b6, %d6b ]
  br label %d7h
d7h:
  %c7 = fcmp ogt double %v7, 0.000000e+00
  br i1 %c7, label %d7a, label %d7b
d7a:
  %a7 = fadd double %v7, 1.000000e+00
  br label %d7m
d7b:
  %b7 = fmul double %v7, 2.000000e+00
  br label %d7m
d7m:
  %v8 = phi double [ %a7, %d7a ], [ %b7, %d7b ]
  br label %d8h
d8h:
  %c8 = fcmp ogt double %v8, 0.000000e+00
  br i1 %c8, label %d8a, label %d8b
d8a:
  %a8 = fadd double %v8, 1.000000e+00
  br label %d8m
d8b:
  %b8 = fmul double %v8, 2.000000e+00
  br label %d8m
d8m:
  %v9 = phi double [ %a8, %d8a ], [ %b8, %d8b ]
  br label %d9h
d9h:
  %c9 = fcmp ogt double %v9, 0.000000e+00
  br i1 %c9, label %d9a, label %d9b
d9a:
  %a9 = fadd double %v9, 1.000000e+00
  br label %d9m
d9b:
  %b9 = fmul double %v9, 2.000000e+00
  br label %d9m
d9m:
  %v10 = phi double [ %a9, %d9a ], [ %b9, %d9b ]
  br label %d10h
d10h:
  %c10 = fcmp ogt double %v10, 0.000000e+00
  br i1 %c10, label %d10a, label %d10b
d10a:
  %a10 = fadd double %v10, 1.000000e+00
  br label %d10m
d10b:
  %b10 = fmul double %v10, 2.000000e+00
  br label %d10m
d10m:
  %v11 = phi double [ %a10, %d10a ], [ %b10, %d10b ]
  br label %d11h
d11h:
  %c11 = fcmp ogt double %v11, 0.000000e+00
  br i1 %c11, label %d11a, label %d11b
d11a:
  %a11 = fadd double %v11, 1.000000e+00
  br label %d11m
d11b:
  %b11 = fmul double %v11, 2.000000e+00
  br label %d11m
d11m:
  %v12 = phi double [ %a11, %d11a ], [ %b11, %d11b ]
  br label %d12h
d12h:
  %c12 = fcmp ogt double %v12, 0.000000e+00
  br i1 %c12, label %d12a, label %d12b
d12a:
  %a12 = fadd double %v12, 1.000000e+00
  br label %d12m
d12b:
  %b12 = fmul double %v12, 2.000000e+00
  br label %d12m
d12m:
  %v13 = phi double [ %a12, %d12a ], [ %b12, %d12b ]
  br label %d13h
d13h:
  %c13 = fcmp ogt double %v13, 0.000000e+00
  br i1 %c13, label %d13a, label %d13b
d13a:
  %a13 = fadd double %v13, 1.000000e+00
  br label %d13m
d13b:
  %b13 = fmul double %v13, 2.000000e+00
  br label %d13m
d13m:
  %v14 = phi double [ %a13, %d13a ], [ %b13, %d13b ]
  br label %d14h
d14h:
  %c14 = fcmp ogt double %v14, 0.000000e+00
  br i1 %c14, label %d14a, label %d14b
d14a:
  %a14 = fadd double %v14, 1.000000e+00
  br label %d14m
d14b:
  %b14 = fmul double %v14, 2.000000e+00
  br label %d14m
d14m:
  %v15 = phi double [ %a14, %d14a ], [ %b14, %d14b ]
  br label %d15h
d15h:
  %c15 = fcmp ogt double %v15, 0.000000e+00
  br i1 %c15, label %d15a, label %d15b
d15a:
  %a15 = fadd double %v15, 1.000000e+00
  br label %d15m
d15b:
  %b15 = fmul double %v15, 2.000000e+00
  br label %d15m
d15m:
  %v16 = phi double [ %a15, %d15a ], [ %b15, %d15b ]
  br label %d16h
d16h:
  %c16 = fcmp ogt double %v16, 0.000000e+00
  br i1 %c16, label %d16a, label %d16b
d16a:
  %a16 = fadd double %v16, 1.000000e+00
  br label %d16m
d16b:
  %b16 = fmul double %v16, 2.000000e+00
  br label %d16m
d16m:
  %v17 = phi double [ %a16, %d16a ], [ %b16, %d16b ]
  br label %d17h
d17h:
  %c17 = fcmp ogt double %v17, 0.000000e+00
  br i1 %c17, label %d17a, label %d17b
d17a:
  %a17 = fadd double %v17, 1.000000e+00
  br label %d17m
d17b:
  %b17 = fmul double %v17, 2.000000e+00
  br label %d17m
d17m:
  %v18 = phi double [ %a17, %d17a ], [ %b17, %d17b ]
  br label %d18h
d18h:
  %c18 = fcmp ogt double %v18, 0.000000e+00
  br i1 %c18, label %d18a, label %d18b
d18a:
  %a18 = fadd double %v18, 1.000000e+00
  br label %d18m
d18b:
  %b18 = fmul double %v18, 2.000000e+00
  br label %d18m
d18m:
  %v19 = phi double [ %a18, %d18a ], [ %b18, %d18b ]
  br label %d19h
d19h:
  %c19 = fcmp ogt double %v19, 0.000000e+00
  br i1 %c19, label %d19a, label %d19b
d19a:
  %a19 = fadd double %v19, 1.000000e+00
  br label %d19m
d19b:
  %b19 = fmul double %v19, 2.000000e+00
  br label %d19m
d19m:
  %v20 = phi double [ %a19, %d19a ], [ %b19, %d19b ]
  br label %done
done:
  ret double %v20
}
