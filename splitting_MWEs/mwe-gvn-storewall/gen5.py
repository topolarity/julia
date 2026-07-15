#!/usr/bin/env python3
# Complementary discriminator: FIX blocks/branchiness (N units, D diamonds) and
# FIX memory-ops (N loads+stores); vary only PAD dummy fp instructions per unit.
# Only raw instruction count moves; block count, branchiness, mem-ops all fixed.
# Theory (cost = branchy non-local walk) predicts ~FLAT GVN.
#   gen5.py N D PAD
import sys
N   = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
D   = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
PAD = int(sys.argv[3]) if len(sys.argv) > 3 else 0
L = ["define double @f(ptr noalias %base) {", "entry:",
     "  store double 1.0, ptr %base, align 8", "  br label %u0"]
acc = "0.0"
for i in range(N):
    nxt = f"u{i+1}" if i + 1 < N else "done"
    L.append(f"u{i}:")
    L += [f"  %sp{i} = getelementptr inbounds double, ptr %base, i64 {i+1}",
          f"  store double {acc}, ptr %sp{i}, align 8",
          f"  %lv{i} = load double, ptr %base, align 8",
          f"  %mv{i} = fadd double %lv{i}, {acc}"]
    p = f"%mv{i}"
    for k in range(PAD):                      # raw-instruction padding (no memory, no branch)
        L.append(f"  %pad{i}_{k} = fadd double {p}, 1.0"); p = f"%pad{i}_{k}"
    if i < D:
        L += [f"  %c{i} = fcmp ogt double {p}, 0.0",
              f"  br i1 %c{i}, label %a{i}, label %b{i}",
              f"a{i}:", f"  %av{i} = fadd double {p}, 1.0", f"  br label %m{i}",
              f"b{i}:", f"  %bv{i} = fmul double {p}, 2.0", f"  br label %m{i}",
              f"m{i}:", f"  %pv{i} = phi double [ %av{i}, %a{i} ], [ %bv{i}, %b{i} ]",
              f"  br label %{nxt}"]
        acc = f"%pv{i}"
    else:
        L.append(f"  br label %{nxt}"); acc = p
L += ["done:", f"  ret double {acc}", "}"]
print("\n".join(L))
