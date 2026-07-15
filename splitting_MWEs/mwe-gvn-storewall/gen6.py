#!/usr/bin/env python3
# gen6: pointer-phi version. The load CURSOR is phi'd through each diamond, so the
# load's pointer arrives via a phi and MemDep must PHI-translate it (PHITransAddr) to
# find the dependency -- the reversediff mechanism (tracked values flow through branches
# as pointers -> new identities to track). Cursor resolves to base[0] on both arms so
# reloads stay redundant (forward to entry store) but require translation to prove it.
#   gen6.py N BS
import sys
N  = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
BS = int(sys.argv[2]) if len(sys.argv) > 2 else 1
nseg = (N + BS - 1) // BS
L = ["define double @f(ptr noalias %base) {", "entry:",
     "  store double 1.0, ptr %base, align 8",
     "  %cur0 = getelementptr inbounds double, ptr %base, i64 0", "  br label %s0"]
cur = "%cur0"; acc = "0.0"; unit = 0
for s in range(nseg):
    L.append(f"s{s}:")
    for _ in range(BS):
        if unit >= N: break
        i = unit; unit += 1
        L += [f"  %sp{i} = getelementptr inbounds double, ptr %base, i64 {i+1}",
              f"  store double {acc}, ptr %sp{i}, align 8",
              f"  %lv{i} = load double, ptr {cur}, align 8",      # load through phi'd cursor
              f"  %mv{i} = fadd double %lv{i}, {acc}"]
        acc = f"%mv{i}"
    # diamond: re-derive the cursor on each arm -> phi of POINTERS
    L += [f"  %c{s} = fcmp ogt double {acc}, 0.0",
          f"  br i1 %c{s}, label %a{s}, label %b{s}",
          f"a{s}:", f"  %ca{s} = getelementptr inbounds double, ptr %base, i64 0",
          f"  %av{s} = fadd double {acc}, 1.0", f"  br label %m{s}",
          f"b{s}:", f"  %cb{s} = getelementptr inbounds double, ptr %base, i64 0",
          f"  %bv{s} = fmul double {acc}, 2.0", f"  br label %m{s}",
          f"m{s}:",
          f"  %cur{s+1} = phi ptr [ %ca{s}, %a{s} ], [ %cb{s}, %b{s} ]",
          f"  %accm{s} = phi double [ %av{s}, %a{s} ], [ %bv{s}, %b{s} ]",
          f"  br label %{'s'+str(s+1) if s+1 < nseg else 'done'}"]
    cur = f"%cur{s+1}"; acc = f"%accm{s}"
L += ["done:", f"  ret double {acc}", "}"]
print("\n".join(L))
