# Attribute >2ms mutator stalls: page faults vs context switches, via
# per-iteration getrusage(RUSAGE_THREAD) deltas.
const RUSAGE_THREAD = Cint(1)
mutable struct Rusage
    utime_s::Clong; utime_us::Clong; stime_s::Clong; stime_us::Clong
    maxrss::Clong; ixrss::Clong; idrss::Clong; isrss::Clong
    minflt::Clong; majflt::Clong; nswap::Clong
    inblock::Clong; oublock::Clong; msgsnd::Clong; msgrcv::Clong
    nsignals::Clong; nvcsw::Clong; nivcsw::Clong
    Rusage() = new(0,0,0,0, 0,0,0,0, 0,0,0, 0,0,0,0, 0,0,0)
end
getrusage!(r) = ccall(:getrusage, Cint, (Cint, Ref{Rusage}), RUSAGE_THREAD, r)

function foo(n, events)
    x = 0.0; tmax = 0.0
    ra = Rusage(); rb = Rusage()
    for i = 1:n
        getrusage!(ra)
        t0 = time(); a = [1 i; i 1]; d = time()-t0; x += sum(a)
        if d > 0.002
            getrusage!(rb)
            push!(events, (i, d, rb.minflt-ra.minflt, rb.majflt-ra.majflt,
                           rb.nvcsw-ra.nvcsw, rb.nivcsw-ra.nivcsw,
                           (rb.utime_s-ra.utime_s)*1_000_000 + rb.utime_us-ra.utime_us,
                           (rb.stime_s-ra.stime_s)*1_000_000 + rb.stime_us-ra.stime_us))
        end
        tmax = max(tmax, d)
    end
    (x, tmax)
end
foo(10_000_000, NTuple{8,Real}[])   # warm past the ramp (rusage version is ~2x slower)
ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ()); ccall(:mmtk_reset_kind_stats, Cvoid, ())
N = parse(Int, ARGS[1])
events = NTuple{8,Real}[]
(_, tmax) = foo(N, events)
km(q) = Int(ccall(:mmtk_stw_kind_max_ns, UInt64, (Csize_t,), q))
println("tmax=", round(tmax*1000,digits=1), "ms InitMax=", round(km(2)/1e6,digits=2),
        " FinalMax=", round(km(3)/1e6,digits=2),
        " block_max=", round(Int(ccall(:mmtk_block_max_ns, UInt64, ()))/1e6,digits=2),
        " nevents=", length(events))
println("  iter | ms | minflt majflt | nvcsw nivcsw | utime_us stime_us")
for e in events
    println("  ", e[1], " | ", round(e[2]*1000,digits=2), " | ", e[3], " ", e[4],
            " | ", e[5], " ", e[6], " | ", e[7], " ", e[8])
end
