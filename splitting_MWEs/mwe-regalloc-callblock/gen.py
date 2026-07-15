#!/usr/bin/env python3
# MWE: GreedyRegisterAllocator super-linear on a giant block of calls with
# rooted values live across the safepoints (shape 2). Each of N calls yields a
# value; all are stored back afterwards, so every value is live from its call
# to its store -- between the last call and the first store all N are live at
# once, and RA's interference/eviction over that block is super-linear in N.
# Values are consumed by stores (not an arithmetic reduction) so the cost lands
# in register allocation, not MachineCombiner.
#
#   python3 gen.py N [CHUNK]     # CHUNK>0 = br every CHUNK calls (bounds it)
#   llc -O2 q.ll -o /dev/null
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
CHUNK = int(sys.argv[2]) if len(sys.argv) > 2 else 0
L = [f"@buf = external global [{N} x i64]", "declare i64 @make()",
     "define void @f() {", "entry:"]
if CHUNK: L.append("  br label %b0"); L.append("b0:")
blk = 0
for i in range(N):
    L.append(f"  %v{i} = call i64 @make()")
    if CHUNK and (i + 1) % CHUNK == 0:
        blk += 1; L.append(f"  br label %b{blk}"); L.append(f"b{blk}:")
for i in range(N):
    L.append(f"  store i64 %v{i}, ptr getelementptr([{N} x i64], ptr @buf, i64 0, i64 {i})")
L += ["  ret void", "}"]
print("\n".join(L))
