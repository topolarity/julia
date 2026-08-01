ms(x) = round(x/1e6, digits=2)
function foo(n)
    x = 0.0; tmax = 0.0
    for i = 1:n
        t0 = time(); a = [1 i; i 1]; tmax = max(tmax, time()-t0); x += sum(a)
    end
    (x, tmax)
end
foo(1000); GC.gc(true)
ccall(:mmtk_set_pause_pkt_report_ns, Cvoid, (UInt64,), 400_000); ccall(:mmtk_reset_gc_stats, Cvoid, ()); ccall(:mmtk_diag_reset, Cvoid, ()); ccall(:mmtk_reset_kind_stats, Cvoid, ())
N = parse(Int, ARGS[1]); (_, tmax) = foo(N)
kn(q) = Int(ccall(:mmtk_stw_kind_n, UInt64, (Csize_t,), q))
kt(q) = Int(ccall(:mmtk_stw_kind_ns, UInt64, (Csize_t,), q))
km(q) = Int(ccall(:mmtk_stw_kind_max_ns, UInt64, (Csize_t,), q))
ka(q) = Int(ccall(:mmtk_stw_kind_max_at, UInt64, (Csize_t,), q))
pk(q) = kn(q)==0 ? "-" : string(ms(kt(q)/kn(q)), "/", ms(km(q)), "@", ka(q))
println("tmax=", round(tmax*1000,digits=1), "ms n=", kn(1)+kn(2)+kn(3),
        " Init(mean/max@ord)=", pk(2), " Final=", pk(3), " Full=", pk(1),
        " block_max=", ms(Int(ccall(:mmtk_block_max_ns, UInt64, ()))),
        " stopw_max=", ms(Int(ccall(:mmtk_stop_wait_max_ns, UInt64, ()))),
        " triage_max=", ms(Int(ccall(:mmtk_triage_max_ns, UInt64, ()))),
        " triage_tot=", ms(Int(ccall(:mmtk_triage_ns_total, UInt64, ()))),
        " unlog_max=", ms(Int(ccall(:mmtk_unlog_max_ns, UInt64, ()))))
