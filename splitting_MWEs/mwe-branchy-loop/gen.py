#!/usr/bin/env python3
# branchy-loop COUNTER-EXAMPLE: branchy, call-dense LOOP that our splitting pass does NOT
# help (yet). A loop whose body is N diamonds; each diamond is a range check on
# the induction variable whose arms each make a leaf call and merge (phi),
# threading an accumulator. ~4N blocks in one loop body.
#
# This reproduces super-linear compile (LoopStrengthReduce / IndVarSimplify /
# ConstraintElimination / InstCombine on the huge loop body) but NEITHER
# block- nor function-splitting bounds it: the splitter forms regions from
# blocks and cannot outline a single loop's interior, so the loop stays whole
# and the loop-scoped passes still see all N diamonds. Measured (julia
# pipeline, N=2000): off 15.2s / B 15.8s / F 15.1s -- both levers are no-ops.
#
# Kept as a known limitation / future-work candidate: generalizing the splitter
# to cut loop bodies (or hoist/outline loop sub-regions) would extend coverage
# to this shape. Contrast mwe-branchy-calls-acyclic (outlinable) once it exists.
#
#   opt -load-pass-plugin=libjulia-codegen.so --passes='julia<llvm_only;no_lower_intrinsics>' \
#       [-julia-split-...] -time-passes q.ll -o /dev/null
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
L = ["declare i64 @leaf(i64)",
     "define i64 @f(i64 %n) {",
     "entry:",
     "  br label %loop",
     "loop:",
     "  %iv = phi i64 [ 0, %entry ], [ %ivn, %latch ]",
     f"  %acc0 = phi i64 [ 0, %entry ], [ %acc{N}, %latch ]"]
for i in range(N):
    L += [f"  %c{i} = icmp ult i64 %iv, {1000000 + i}",
          f"  br i1 %c{i}, label %then{i}, label %else{i}",
          f"then{i}:",
          f"  %t{i} = call i64 @leaf(i64 %iv)",
          f"  br label %m{i}",
          f"else{i}:",
          f"  %e{i} = call i64 @leaf(i64 %acc{i})",
          f"  br label %m{i}",
          f"m{i}:",
          f"  %ph{i} = phi i64 [ %t{i}, %then{i} ], [ %e{i}, %else{i} ]",
          f"  %acc{i+1} = add i64 %acc{i}, %ph{i}"]
L += ["  br label %latch",
      "latch:",
      "  %ivn = add nuw nsw i64 %iv, 1",
      "  %done = icmp eq i64 %ivn, %n",
      "  br i1 %done, label %exit, label %loop",
      "exit:",
      f"  ret i64 %acc{N}",
      "}"]
print("\n".join(L))
