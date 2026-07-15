#!/usr/bin/env python3
# BRANCHINESS discriminator. Fixed N redundant-forward units (fixed mem-ops).
# First D units are BRANCHY (diamond: fcmp/br + 2 arms + phi); the rest are STRAIGHT
# but PADDED with the same number of fp instructions, so TOTAL INSTRUCTIONS and
# MEMORY OPS are ~constant while the number of conditional merges (branchiness /
# PHI-translation surface) varies with D. Isolates branchiness from size.
#   gen4.py N D
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
D = int(sys.argv[2]) if len(sys.argv) > 2 else 0
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
    if i < D:
        # branchy: diamond (2 arms + phi merge)
        L += [f"  %c{i} = fcmp ogt double %mv{i}, 0.0",
              f"  br i1 %c{i}, label %a{i}, label %b{i}",
              f"a{i}:", f"  %av{i} = fadd double %mv{i}, 1.0", f"  br label %m{i}",
              f"b{i}:", f"  %bv{i} = fmul double %mv{i}, 2.0", f"  br label %m{i}",
              f"m{i}:", f"  %pv{i} = phi double [ %av{i}, %a{i} ], [ %bv{i}, %b{i} ]",
              f"  br label %{nxt}"]
        acc = f"%pv{i}"
    else:
        # straight but PADDED with the same count of fp ops (no branch merge)
        L += [f"  %av{i} = fadd double %mv{i}, 1.0",
              f"  %bv{i} = fmul double %mv{i}, 2.0",
              f"  %pv{i} = fadd double %av{i}, %bv{i}",
              f"  br label %{nxt}"]
        acc = f"%pv{i}"
L += ["done:", f"  ret double {acc}", "}"]
print("\n".join(L))
