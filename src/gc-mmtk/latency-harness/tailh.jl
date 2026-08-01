ms(x) = round(x/1e6, digits=2)
function foo(n, stalls)
    x = 0.0; tmax = 0.0
    for i = 1:n
        t0 = time(); a = [1 i; i 1]; d = time()-t0; x += sum(a)
        if d > 0.0003
            push!(stalls, (i, d))
        end
        tmax = max(tmax, d)
    end
    (x, tmax)
end
foo(30_000_000, Tuple{Int,Float64}[])   # warm past the ramp
ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ()); ccall(:mmtk_reset_kind_stats, Cvoid, ())
N = parse(Int, ARGS[1])
stalls = Tuple{Int,Float64}[]
(_, tmax) = foo(N, stalls)
kn(q) = Int(ccall(:mmtk_stw_kind_n, UInt64, (Csize_t,), q))
kt(q) = Int(ccall(:mmtk_stw_kind_ns, UInt64, (Csize_t,), q))
km(q) = Int(ccall(:mmtk_stw_kind_max_ns, UInt64, (Csize_t,), q))
pk(q) = kn(q)==0 ? "-" : string(ms(kt(q)/kn(q)), "/", ms(km(q)))
println("tmax=", round(tmax*1000,digits=1), "ms pauses=", kn(1)+kn(2)+kn(3),
        " Init=", pk(2), " Final=", pk(3), " Full=", pk(1),
        " block_max=", ms(Int(ccall(:mmtk_block_max_ns, UInt64, ()))),
        " stopw_max=", ms(Int(ccall(:mmtk_stop_wait_max_ns, UInt64, ()))),
        " triage_max=", ms(Int(ccall(:mmtk_triage_max_ns, UInt64, ()))),
        " nstalls=", length(stalls))
sort!(stalls; by = s -> -s[2])
top = stalls[1:min(12, end)]
sort!(top; by = s -> s[1])
for (i, d) in top
    println("  iter=", i, "  ", round(d*1000, digits=2), "ms")
end
# histogram of all stalls
using Printf
edges = [0.0003, 0.0005, 0.001, 0.002, 0.004, 0.008, 1.0]
for k in 1:length(edges)-1
    c = count(s -> edges[k] <= s[2] < edges[k+1], stalls)
    c > 0 && @printf("  [%4.1f-%4.1fms): %d\n", edges[k]*1000, edges[k+1]*1000, c)
end
