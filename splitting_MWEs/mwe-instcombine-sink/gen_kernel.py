import os
# MWE: 8-lane polynomial-chain evaluation, INTERLEAVED (as written for ILP),
# with a straight seam before the combining call, and a short continuation
# after the call that reuses the same coefficients.
N = int(os.environ.get("MN", "1600"))
lines = ["""define internal fastcc void @stage2(double %v0, double %v1, double %v2, double %v3, double %v4, double %v5, double %v6, double %v7, ptr %out) noinline {
top:
  store double %v0, ptr %out
  %p1 = getelementptr inbounds double, ptr %out, i64 1
  store double %v1, ptr %p1
  ret void
}""", "", "define double @kernel(double %x) {", "entry:",
  "  %agg = alloca [8 x double], align 8"]
ch = {}
for c in range(8):
    lines.append(f"  %h{c} = fadd double %x, {float(c)/8}")
    ch[c] = f"%h{c}"
for i in range(N):              # interleaved, as any ILP-aware source is
    for c in range(8):
        k = (8 * i + c) % 7
        lines.append(f"  %c{c}s{i}.m = fmul contract double {ch[c]}, 0x3FF000001AD7F29B")
        lines.append(f"  %c{c}s{i} = fadd contract double %c{c}s{i}.m, {float(k)}")
        ch[c] = f"%c{c}s{i}"
lines += ["  br label %stage2call", "", "stage2call:"]   # the seam
args = ", ".join(f"double {ch[c]}" for c in range(8))
lines.append(f"  call fastcc void @stage2({args}, ptr %agg)")
rl = []
for c in range(8):
    lines.append(f"  %rp{c} = getelementptr inbounds double, ptr %agg, i64 {c}")
    lines.append(f"  %rv{c} = load double, ptr %rp{c}")
    cur = f"%rv{c}"
    for j in range(4):          # continuation reuses the coefficients
        lines.append(f"  %t{c}j{j}.m = fmul contract double {cur}, 0x3FF000001AD7F29B")
        lines.append(f"  %t{c}j{j} = fadd contract double %t{c}j{j}.m, {float((c+j) % 7)}")
        cur = f"%t{c}j{j}"
    rl.append(cur)
acc = rl[0]
for i, v in enumerate(rl[1:], 1):
    lines.append(f"  %s{i} = fadd double {acc}, {v}")
    acc = f"%s{i}"
lines += [f"  ret double {acc}", "}"]
open(f"{os.environ['SCRATCH']}/mwe_final.ll", "w").write("\n".join(lines) + "\n")
