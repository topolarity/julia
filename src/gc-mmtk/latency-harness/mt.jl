ms(x) = round(x/1e6, digits=2)
function worker(n)
    x = 0.0; tmax = 0.0
    for i = 1:n
        t0 = time(); a = [1 i; i 1]; tmax = max(tmax, time()-t0); x += sum(a)
    end
    (x, tmax)
end
foreach(wait, [Threads.@spawn worker(1000) for _ in 1:Threads.nthreads()])
GC.gc(true)
ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ())
N = parse(Int, ARGS[1])
rs = map(fetch, [Threads.@spawn worker(N) for _ in 1:Threads.nthreads()])
tm = sort([r[2] for r in rs]; rev=true)
expected = 2.0*N + N*(N+1.0)
ok = all(r->r[1] == expected, rs)
n = max(Int(ccall(:mmtk_gc_count_total, Csize_t, ())),1)
println(join((Threads.nthreads(), ok, n,
  ms(Int(ccall(:mmtk_stw_total_ns, UInt64, ()))/n),
  ms(Int(ccall(:mmtk_stw_max_ns, UInt64, ()))),
  round(tm[1]*1000,digits=1), round(tm[cld(length(tm),2)]*1000,digits=1)), "|"))
