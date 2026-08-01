ms(x) = round(x/1e6, digits=2)
function foo(n)
    x = 0.0; tmax = 0.0
    for i = 1:n
        t0 = time(); a = [1 i; i 1]; tmax = max(tmax, time()-t0); x += sum(a)
    end
    x, tmax
end
N = parse(Int, ARGS[1])
foo(1000); GC.gc(true)
ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ())
(x, tmax) = foo(N)
n = max(Int(ccall(:mmtk_gc_count_total, Csize_t, ())),1)
expected = 2.0*N + 2.0*(N*(N+1)/2)      # each matrix sums to 2 + 2i
println(join((x, x == expected, round(tmax*1000,digits=1), n,
  ms(Int(ccall(:mmtk_stw_total_ns, UInt64, ()))/n),
  ms(Int(ccall(:mmtk_diag_sweep_ns, UInt64, ()))/n)), "|"))
