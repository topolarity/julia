# Mixed-generation workload: rolling retention forces promotion (minor
# survivors), old-generation growth (drives majors via the pacing goal), and
# old death (majors must reclaim what minors promoted).  Validates the
# minor<->major interactions: promotion arming, mark persistence across
# InitialMark clears, remset old->young edges, and nursery-vs-lazy-sweep
# handoff.  Prints a correctness checksum and per-kind pause counts.
ms(x) = round(x/1e6, digits=2)
function churn(n, window)
    keep = Vector{Matrix{Int}}(undef, window)
    for i = 1:window
        keep[i] = [1 i; i 1]
    end
    x = 0.0
    for i = 1:n
        j = mod1(i, window)
        # read the survivor before replacing it (old->young edge on `keep`)
        x += keep[j][1, 2]
        keep[j] = [1 i; i 1]
        # transient garbage alongside
        x += sum([i 2; 3 i])
    end
    (x, keep)
end
churn(1000, 100); GC.gc(true)
kn(q) = Int(ccall(:mmtk_stw_kind_n, UInt64, (Csize_t,), q))
ccall(:mmtk_reset_kind_stats, Cvoid, ())
N = parse(Int, ARGS[1]); W = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 200_000
(x, keep) = churn(N, W)
# expected: sum over i of keep-read + transient sum
# keep[j][1,2] at iteration i = value stored at the previous write of slot j
# (i-W for i>W, else the warm init j).  transient sum = 2i + 5.
exp_trans = sum(2.0*i + 5 for i = 1:N)
exp_keep = sum(Float64(i <= W ? mod1(i, W) : i - W) for i = 1:N)
ok = x == exp_trans + exp_keep
# survivors still intact?
live_ok = all(keep[mod1(i, W)][2, 1] == i for i = max(1, N-W+1):N)
println(ok, "|", live_ok, "|full=", kn(1), " init=", kn(2), " final=", kn(3),
        " nursery=", kn(4), "|heap=", round(Int(ccall(:mmtk_used_bytes, UInt64, ()))/2^20, digits=1), "MB")
