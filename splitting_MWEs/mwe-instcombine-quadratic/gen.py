#!/usr/bin/env python3
# MWE: InstCombine O(calls x block-size) quadratic on a huge block, the SAME
# path that hits large-N tracked ReverseDiff (NOTES.md: N=48 425s->98s, gdb
# 24/24 in renumberInstructions). Chain:
#   InstCombinerImpl::visitCallBase -> isKnownNonZero(ptr arg)
#     -> isValidAssumeForContext -> Instruction::comesBefore
#     -> BasicBlock::renumberInstructions  (O(block-size), once per stale query)
#
# THREE ingredients, all necessary AND all surviving the real pipeline:
#  (1) many calls with a POINTER arg -> visitCallBase runs isKnownNonZero on it
#      to infer nonnull (this is the query that reaches the assume);
#  (2) a `nonnull` OPERAND-BUNDLE assume per pointer -- llvm.assume(i1 true)
#      ["nonnull"(ptr %p)]. This is the form Julia emits for tracked pointers,
#      and CRUCIALLY it SURVIVES EarlyCSE/InstSimplify. (An `icmp ne, 0`-
#      conditioned assume does NOT: EarlyCSE marks the icmp true and the assume
#      is discharged before any InstCombine -> the quadratic then only shows in
#      bare `opt -passes=instcombine`, never in-pipeline. That was the old
#      version of this MWE and it was a misleading bare-only reproducer.);
#  (3) interleaved foldable `add %p,%p -> shl` that InstCombine rewrites,
#      invalidating the block's instruction-ordering cache so every comesBefore
#      re-runs renumberInstructions. Without (3) the cache stays valid -> linear.
#
# Cost O(calls x block-size) = O(N^2). Chunking the block (Julia's
# BasicBlockSplitting at the pre-InstCombine split#1 position) bounds each
# renumber -> linear. Verified BOTH bare and IN-PIPELINE (unlike the old form):
#   N=8000: bare 6.2s; julia pipeline off 6.1s; split#1(bb<=2000) 0.086s (~75x).
#
#   python3 gen.py N > q_N.ll
#   opt -passes='function(instcombine)' -time-passes q_N.ll -o /dev/null   # O(N^2)
#   # in-pipeline (survives EarlyCSE) + split#1 fix:
#   opt --load-pass-plugin=libjulia-codegen.so --passes='julia<no_lower_intrinsics>' \
#       [-julia-split-builtin-early=false -julia-split-builtin-late=false \
#        -julia-split-bb-at-split1 -julia-split-block-threshold=2000 -julia-split-block-insts=2000] \
#       -time-passes q_N.ll -o /dev/null
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
CHUNK = int(sys.argv[2]) if len(sys.argv) > 2 else 0   # 0 = one huge block; >0 = br every CHUNK
L = ["declare void @llvm.assume(i1)", "declare i64 @use(ptr, i64)",
     "define i64 @f(ptr %base) {", "entry:",
     "  %seed = load i64, ptr %base, align 8"]
if CHUNK: L.append("  br label %b0"); L.append("b0:")
prev = "%seed"; blk = 0
for i in range(N):
    L.append(f"  %gp{i} = getelementptr inbounds ptr, ptr %base, i64 {i+1}")
    L.append(f"  %p{i} = load ptr, ptr %gp{i}, align 8")                        # opaque pointer
    L.append(f'  call void @llvm.assume(i1 true) [ "nonnull"(ptr %p{i}) ]')     # (2) survives EarlyCSE
    L.append(f"  %m{i} = add i64 {prev}, {prev}")                               # (3) -> shl, invalidates order cache
    L.append(f"  %q{i} = call i64 @use(ptr %p{i}, i64 %m{i})")                  # (1) visitCallBase -> isKnownNonZero(%p{i})
    prev = f"%q{i}"
    if CHUNK and (i + 1) % CHUNK == 0 and i + 1 < N:
        blk += 1; L.append(f"  br label %b{blk}"); L.append(f"b{blk}:")
L += [f"  ret i64 {prev}", "}"]
print("\n".join(L))
