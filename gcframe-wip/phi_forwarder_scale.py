#!/usr/bin/env python3
# Scalable benchmark for pointer-phi ("forwarder") liveness in
# PreciseLifetimeEnds. Each unit fills one of two stack buffers in a branch
# arm and reads the chosen buffer through a pointer phi at the join — the
# shape SimplifyCFG's sinking produces from memory-phi copies. Without
# forwarder handling the pass must bail (address escapes into the phi), the
# buffers keep function-long live ranges, and the frame scales as ~32*N
# bytes. With edge-substituting forwarder liveness every pair dies at its
# join read and the frame is O(1).
#
# Usage: phi_forwarder_scale.py <julia-root> [N ...]
import subprocess
import re
import sys
import os

root = sys.argv[1]
Ns = [int(a) for a in sys.argv[2:]] or [4, 16, 64]

def gen(n):
    out = []
    out.append("declare void @use_value(i64)")
    out.append("define void @scale(i1 %c, i64 %x) {")
    out.append("top:")
    for i in range(1, n + 1):
        out.append(f"  %A{i} = alloca [2 x i64], align 8")
        out.append(f"  %B{i} = alloca [2 x i64], align 8")
    out.append("  br label %u1head")
    for i in range(1, n + 1):
        nxt = f"u{i+1}head" if i < n else "done"
        out.append(f"u{i}head:")
        out.append(f"  br i1 %c, label %u{i}a, label %u{i}b")
        out.append(f"u{i}a:")
        out.append(f"  call void @llvm.lifetime.start.p0(i64 -1, ptr %A{i})")
        out.append(f"  store i64 %x, ptr %A{i}, align 8")
        out.append(f"  %A{i}hi = getelementptr inbounds i8, ptr %A{i}, i64 8")
        out.append(f"  store i64 {i}, ptr %A{i}hi, align 8")
        out.append(f"  br label %u{i}join")
        out.append(f"u{i}b:")
        out.append(f"  call void @llvm.lifetime.start.p0(i64 -1, ptr %B{i})")
        out.append(f"  store i64 {i}, ptr %B{i}, align 8")
        out.append(f"  %B{i}hi = getelementptr inbounds i8, ptr %B{i}, i64 8")
        out.append(f"  store i64 %x, ptr %B{i}hi, align 8")
        out.append(f"  br label %u{i}join")
        out.append(f"u{i}join:")
        out.append(f"  %p{i} = phi ptr [ %A{i}, %u{i}a ], [ %B{i}, %u{i}b ]")
        out.append(f"  %v{i} = load i64, ptr %p{i}, align 8")
        out.append(f"  call void @use_value(i64 %v{i})")
        out.append(f"  br label %{nxt}")
    out.append("done:")
    out.append("  ret void")
    out.append("}")
    return "\n".join(out) + "\n"

def stacksize(ll_path):
    mir = subprocess.run(
        [os.path.join(root, "usr/tools/llc"), "-O2", "-stop-after=prologepilog",
         "-o", "-", ll_path],
        capture_output=True, text=True, check=True).stdout
    return int(re.search(r"stackSize:\s+(\d+)", mir).group(1))

print(f"{'N':>6} {'raw (no ends)':>14} {'after pass':>12}")
for n in Ns:
    raw = f"/tmp/pfs_{n}.ll"
    opted = f"/tmp/pfs_{n}_opt.ll"
    with open(raw, "w") as f:
        f.write(gen(n))
    subprocess.run(
        [os.path.join(root, "usr/tools/opt"),
         "--load-pass-plugin=" + os.path.join(root, "usr/lib/libjulia-codegen.so"),
         "-passes=function(PreciseLifetimeEnds)", "-S", raw, "-o", opted],
        check=True)
    ends = open(opted).read().count("lifetime.end")
    print(f"{n:>6} {stacksize(raw):>14} {stacksize(opted):>12}   (ends inserted: {ends})")
