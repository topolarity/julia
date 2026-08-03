# Mutator time budget for the pure-allocation loop: attributes wall time to
# STW stalls, allocation-paid triage, and trigger blocking via the runtime
# counters (MMTk build); runs plain on stock for baselines.
#   ARGS: N [gcoff]   e.g. julia mutator-budget.jl 30000000 gcoff
function loop(n)
    for i = 1:n
        [1 i; i 1]
    end
end
loop(1000); GC.gc()
const IS_MMTK = try; ccall(:mmtk_total_bytes, UInt64, ()); true; catch; false; end
const HAS_DIAG = IS_MMTK && (try; ccall(:mmtk_triage_ns_total, UInt64, ()); true; catch; false; end)
N = parse(Int, ARGS[1])
gcoff = length(ARGS) >= 2 && ARGS[2] == "gcoff"
if HAS_DIAG
    ccall(:jl_gc_reset_mutator_stall, Cvoid, ())
    ccall(:mmtk_diag_reset, Cvoid, ())
    ccall(:mmtk_reset_gc_stats, Cvoid, ())
end
n0 = Base.gc_num().pause
gcoff && GC.enable(false)
t = @elapsed loop(N)
gcoff && GC.enable(true)
pauses = Base.gc_num().pause - n0
if HAS_DIAG
    mstall = ccall(:jl_gc_mutator_stall_total_ns, UInt64, ()) / 1e9
    nstall = Int(ccall(:jl_gc_mutator_stall_count, UInt64, ()))
    triage = ccall(:mmtk_triage_ns_total, UInt64, ()) / 1e9
    println("wall=", round(t, digits=3), "s pauses=", pauses,
            " stw_stall=", round(mstall, digits=4), "s(n=", nstall, ")",
            " triage=", round(triage, digits=4), "s",
            " residual_vs_wall=", round(t - mstall - triage, digits=3), "s")
else
    println("wall=", round(t, digits=3), "s pauses=", pauses)
end
