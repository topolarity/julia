#!/usr/bin/env python3
# MWE: JuliaLICM is super-linear (O(K^2)) when it hoists many GC allocations
# out of a single loop. Each hoisted `julia.gc_alloc_obj` is moved to the
# preheader via the MemorySSA updater, and every such move re-runs
# MemorySSA::renameBlock over the (growing) preheader, which is O(#memory-defs
# in that block). K hoists x O(K) rename = O(K^2). (perf: renameBlock ~46%,
# runEscapeAnalysis ~0.3% -- the cost is the MSSA update, NOT escape analysis.)
#
# Ingredients that are each REQUIRED to reach the pathology:
#   1. `julia.gc_alloc_obj` calls -- JuliaLICM early-exits (llvm-julia-licm.cpp
#      :157) unless the module declares gc_alloc_obj / write_barrier /
#      gc_preserve_begin, so plain-LLVM allocas never trigger it.
#   2. loop-INVARIANT args (%pg, %ty, constant size) so the alloc is a hoist
#      candidate (makeLoopInvariant on the args must succeed).
#   3. NON-escaping: the object pointer is only used for stores INTO it (never
#      stored elsewhere / returned / passed to an unknown call), so escape
#      analysis says "hoistable" and the alloc is actually moved.
#   4. keep the alloc live: read field 0 back and fold it into the returned
#      accumulator, or dead-code elimination removes the alloc before LICM.
#
# It is the ALLOC COUNT K (hoists) that is quadratic; M (field ops/alloc) is
# ~linear (it only lengthens the escape walk / memset, not the MSSA rename).
#
#   python3 gen.py K [M]
#   # NB: run JuliaLICM IN ISOLATION -- the full Julia pipeline's AllocOpt
#   # promotes these non-escaping allocs away before JuliaLICM sees them:
#   opt --load-pass-plugin=libjulia-codegen.so \
#       --passes='function(loop-simplify,loop-mssa(JuliaLICM))' -time-passes q.ll -o /dev/null
import sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 1600
M = int(sys.argv[2]) if len(sys.argv) > 2 else 8
L = ["declare noalias nonnull ptr addrspace(10) @julia.gc_alloc_obj(ptr, i64, ptr addrspace(10))",
     "define i64 @f(ptr %pg, ptr addrspace(10) %ty, i64 %n) {", "entry:",
     "  br label %loop", "loop:",
     "  %iv = phi i64 [ 0, %entry ], [ %ivn, %loop ]",
     "  %acc = phi i64 [ 0, %entry ], [ %accn, %loop ]"]
acc = "%acc"
for i in range(K):
    L.append(f"  %box{i} = call noalias nonnull ptr addrspace(10) @julia.gc_alloc_obj(ptr %pg, i64 {8*M}, ptr addrspace(10) %ty)")
    L.append(f"  %c{i} = addrspacecast ptr addrspace(10) %box{i} to ptr addrspace(11)")
    for j in range(M):
        L.append(f"  %g{i}_{j} = getelementptr inbounds i8, ptr addrspace(11) %c{i}, i64 {8*j}")
        L.append(f"  store i64 %iv, ptr addrspace(11) %g{i}_{j}, align 8")
    L.append(f"  %ld{i} = load i64, ptr addrspace(11) %g{i}_0, align 8")
    L.append(f"  %s{i} = add i64 {acc}, %ld{i}"); acc = f"%s{i}"
L += [f"  %accn = add i64 {acc}, 1", "  %ivn = add i64 %iv, 1",
      "  %cc = icmp slt i64 %ivn, %n", "  br i1 %cc, label %loop, label %exit",
      "exit:", "  %r = phi i64 [ %accn, %loop ]", "  ret i64 %r", "}"]
print("\n".join(L))
