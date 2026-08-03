# Per-pass steady-state measurement: pass 1 warms the address space; later
# passes isolate steady-state allocation+GC cost from first-touch effects.
# Reports the mutator's THREAD CPU time vs wall (off-CPU = blocked) and the
# three mutator-side GC costs: safepoint stalls (stw), allocation-paid triage,
# and trigger blocking in block_for_gc (`block`, the space-full path).
function loop(n)
    for i = 1:n
        [1 i; i 1]
    end
end
loop(1000); GC.gc()
const HAS_DIAG = try; ccall(:mmtk_triage_ns_total, UInt64, ()); true; catch; false; end
const CLOCK_THREAD_CPUTIME_ID = Cint(3)
function cpu_ns()
    ts = Ref{NTuple{2,Int64}}((0, 0))
    ccall(:clock_gettime, Cint, (Cint, Ref{NTuple{2,Int64}}), CLOCK_THREAD_CPUTIME_ID, ts)
    ts[][1] * 1_000_000_000 + ts[][2]
end
N = parse(Int, ARGS[1])
for pass = 1:4
    if HAS_DIAG
        ccall(:jl_gc_reset_mutator_stall, Cvoid, ())
        ccall(:mmtk_diag_reset, Cvoid, ())
        ccall(:mmtk_reset_gc_stats, Cvoid, ())
    end
    n0 = Base.gc_num().pause
    cpu0 = cpu_ns()
    t = @elapsed loop(N)
    dcpu = (cpu_ns() - cpu0) / 1e9
    p = Base.gc_num().pause - n0
    extra = if HAS_DIAG
        ms = ccall(:jl_gc_mutator_stall_total_ns, UInt64, ()) / 1e6
        tr = ccall(:mmtk_triage_ns_total, UInt64, ()) / 1e6
        bt = ccall(:mmtk_block_total_ns, UInt64, ()) / 1e6
        bc = Int(ccall(:mmtk_block_count, UInt64, ()))
        string("  stw=", round(ms, digits=1), "ms triage=", round(tr, digits=1),
               "ms block=", round(bt, digits=1), "ms(n=", bc, ")")
    else
        ""
    end
    tgt = HAS_DIAG ? string(" target=", round(ccall(:mmtk_total_bytes, UInt64, ()) / 2^20, digits=1), "MB") : ""
    println("pass $pass: wall=", round(t, digits=3), "s thread_cpu=",
            round(dcpu, digits=3), "s off_cpu=", round(t - dcpu, digits=3),
            "s pauses=", p, extra, tgt)
end
