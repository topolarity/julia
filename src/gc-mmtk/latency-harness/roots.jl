ms(x) = round(x/1e6, digits=2)
# Stack/root scaling harness: park NTASKS tasks, each blocked at DEPTH
# recursion with a GC-rooted local per frame, then drive Init pauses with the
# allocation loop.  Run with MMTK_ROOT_ANATOMY=1 to get per-pause [roots]
# lines (stack=..us tasks=.. slots=..).
#   env ROOTS_TASKS=1000 ROOTS_DEPTH=100 julia roots.jl 50000000
const DEPTH = parse(Int, get(ENV, "ROOTS_DEPTH", "100"))
const NTASKS = parse(Int, get(ENV, "ROOTS_TASKS", "100"))
const ch = Channel{Int}(Inf)

@noinline function deep(d, ch)
    # inferencebarrier defeats SROA so each frame really holds a heap Ref in
    # its shadow stack; reading x[] after take!() returns also makes teardown
    # a liveness check on deferred/snapshot stack scanning.
    x = Base.inferencebarrier(Ref(d))::Base.RefValue{Int}
    if d == 0
        take!(ch)                   # park with the whole stack live
        return x[]
    end
    return deep(d-1, ch) + x[]
end

tasks = [errormonitor(@async deep(DEPTH, ch)) for _ in 1:NTASKS]
yield()                             # let every task run down to take!()

function foo(n)
    x = 0.0; tmax = 0.0
    for i = 1:n
        t0 = time(); a = [1 i; i 1]; tmax = max(tmax, time()-t0); x += sum(a)
    end
    (x, tmax)
end
foo(1000); GC.gc(true)
ccall(:jl_gc_reset_mutator_stall, Cvoid, ()); ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ()); ccall(:mmtk_reset_kind_stats, Cvoid, ())
N = parse(Int, ARGS[1]); (_, tmax) = foo(N)
kn(q) = Int(ccall(:mmtk_stw_kind_n, UInt64, (Csize_t,), q))
kt(q) = Int(ccall(:mmtk_stw_kind_ns, UInt64, (Csize_t,), q))
km(q) = Int(ccall(:mmtk_stw_kind_max_ns, UInt64, (Csize_t,), q))
pk(q) = kn(q)==0 ? "-" : string(ms(kt(q)/kn(q)), "/", ms(km(q)))
mn = Int(ccall(:jl_gc_mutator_stall_count, UInt64, ())); mm = Int(ccall(:jl_gc_mutator_stall_max_ns, UInt64, ())); mt = Int(ccall(:jl_gc_mutator_stall_total_ns, UInt64, ()))
println("tasks=", NTASKS, " depth=", DEPTH, " tmax=", round(tmax*1000,digits=1), "ms",
        " Init(mean/max)=", pk(2), " Final=", pk(3), " Full=", pk(1),
        " mstall(mean/max)=", mn==0 ? 0.0 : ms(mt/mn), "/", ms(mm))
for t in tasks; put!(ch, 0); end
foreach(wait, tasks)
