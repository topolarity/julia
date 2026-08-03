# MWE: the stock-heuristics trigger churns full concurrent cycles for
# allocation-heavy, low-survival loops.  The initial heap target is
# DEFAULT_COLLECT_INTERVAL (= 5600*1024*sizeof(Int) = 43.75MB, stock GC's
# initial collect interval, see mmtk_julia/src/gc_trigger.jl:13,53), and
# since ~nothing survives this loop the survival-driven growth never raises
# it -- so ~1.27GB of garbage runs ~90 full concurrent cycles.  Stock GC
# makes the same "don't grow" decision but pays ~36 cheap nursery sweeps;
# ConcurrentImmix has no nursery, so each cycle is a full concurrent mark
# plus two pauses.  The float-budget trigger fires every
# min(128MB, (target-live)/3) ~= 15MB of float at a 44MB target.
#
# Run (MMTk build):
#   julia --startup-file=no trigger-churn.jl                     # default: churns
#   MMTK_MIN_HSIZE_G=8 MMTK_MAX_HSIZE_G=8 julia ... trigger-churn.jl  # sized: fine
# Also runs on a stock build for comparison (heap target line is skipped).

const IS_MMTK = try
    println("heap_target = ", ccall(:mmtk_total_bytes, UInt64, ()) / 2^20, " MB")
    true
catch
    println("heap_target = (stock build)")
    false
end
# Cycle counting: a ConcurrentImmix cycle spans TWO pauses (InitialMark +
# FinalMark), so `gc_num.pause` overcounts it 2x vs stock/generational
# plans (one pause per collection).  Count cycles as Init + Full when the
# per-kind counters are live (concurrent plans); otherwise cycles = pauses.
kindn(q) = Int(ccall(:mmtk_stw_kind_n, UInt64, (Csize_t,), q))
# Full + InitialMark; 0 when the per-kind counters don't exist (upstream
# binding) or are never set (non-concurrent plans).
cycles0() = IS_MMTK ? (try kindn(1) + kindn(2) catch; 0 end) : 0
full0() = IS_MMTK ? (try kindn(1) catch; 0 end) : 0
minor0() = IS_MMTK ? (try kindn(4) catch; 0 end) : 0
c0 = cycles0(); f0 = full0(); m0 = minor0()
n0 = Base.gc_num().pause
t = @elapsed for i = 1:10_000_000
    [1 i; i 1]
end
pauses = Base.gc_num().pause - n0
c = cycles0() - c0
fulls = full0() - f0
minors = minor0() - m0
cycles = c > 0 ? c : pauses
println("wall = ", round(t, digits=2), "s   cycles = ", cycles,
        "   full = ", fulls, "   concurrent = ", cycles - fulls,
        "   minor = ", minors, "   (pauses = ", pauses, ")")
