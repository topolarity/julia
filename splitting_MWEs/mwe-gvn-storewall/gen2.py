#!/usr/bin/env python3
# GVN store-wall MWE v2: REDUNDANT load forwarding across a branchy store wall.
# entry stores base[0]. Each unit i stores a DISTINCT slot i (NoAlias with base[0])
# then RE-LOADS base[0] -> GVN forwards it to the entry store, but must prove NoAlias
# against the wall of stores base[1..i] in between -> walk length ~ i => O(N^2).
# The forward ELIMINATES the load, dirtying the MemDep cache (as reversediff does),
# so subsequent queries re-walk. Diamonds force NON-LOCAL memdep.  BS = units/block.
import sys
N  = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
BS = int(sys.argv[2]) if len(sys.argv) > 2 else 1
nseg = (N + BS - 1) // BS
L = ["define double @f(ptr noalias %base) {", "entry:",
     "  store double 1.0, ptr %base, align 8", "  br label %s0"]
unit = 0
for s in range(nseg):
    L.append(f"s{s}:")
    acc = "0.0" if s == 0 else f"%accm{s-1}"
    for _ in range(BS):
        if unit >= N: break
        i = unit; unit += 1
        L += [f"  %sp{i} = getelementptr inbounds double, ptr %base, i64 {i+1}",
              f"  store double {acc}, ptr %sp{i}, align 8",       # store distinct slot i+1
              f"  %lv{i} = load double, ptr %base, align 8",      # reload slot 0 -> forward past the wall
              f"  %mv{i} = fadd double %lv{i}, {acc}"]
        acc = f"%mv{i}"
    L += [f"  %c{s} = fcmp ogt double {acc}, 0.0",
          f"  br i1 %c{s}, label %a{s}, label %b{s}",
          f"a{s}:", f"  %av{s} = fadd double {acc}, 1.0", f"  br label %m{s}",
          f"b{s}:", f"  %bv{s} = fmul double {acc}, 2.0", f"  br label %m{s}",
          f"m{s}:", f"  %accm{s} = phi double [ %av{s}, %a{s} ], [ %bv{s}, %b{s} ]",
          f"  br label %{'s'+str(s+1) if s+1 < nseg else 'done'}"]
L += ["done:", f"  ret double %accm{nseg-1}", "}"]
print("\n".join(L))
