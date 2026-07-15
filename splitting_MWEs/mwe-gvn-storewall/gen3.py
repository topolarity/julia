#!/usr/bin/env python3
# CLEAN block-vs-instruction discriminator. FIXED N redundant-forward units
# (2N memory ops, 5N core instructions), partitioned into NB blocks by UNCONDITIONAL
# branches (1 instr each). Varying NB moves block count ~200x while total instructions
# move only ~+NB (a few %). Straight-line so acc threads by dominance (no phi).
#   gen3.py N NB   ->  opt -passes=gvn
import sys
N  = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
NB = int(sys.argv[2]) if len(sys.argv) > 2 else 100
per = max(1, (N + NB - 1) // NB)
L = ["define double @f(ptr noalias %base) {", "entry:",
     "  store double 1.0, ptr %base, align 8", "  br label %b0", "b0:"]
acc = "0.0"; blk = 0
for i in range(N):
    L += [f"  %sp{i} = getelementptr inbounds double, ptr %base, i64 {i+1}",
          f"  store double {acc}, ptr %sp{i}, align 8",
          f"  %lv{i} = load double, ptr %base, align 8",
          f"  %mv{i} = fadd double %lv{i}, {acc}"]
    acc = f"%mv{i}"
    if (i + 1) % per == 0 and i + 1 < N:
        blk += 1
        L += [f"  br label %b{blk}", f"b{blk}:"]
L += [f"  ret double {acc}", "}"]
print("\n".join(L))
