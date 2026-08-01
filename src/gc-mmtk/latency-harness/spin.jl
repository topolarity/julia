# Pure spin loop: detect wall-clock gaps with zero allocation and zero GC.
# If multi-ms gaps appear here, the tail stalls are external (SMI/IRQ/sched),
# not the collector.
function spin(seconds)
    t_end = time_ns() + round(UInt64, seconds * 1e9)
    prev = time_ns()
    worst = 0.0
    ngaps = 0
    x = 1.0
    while true
        # ~1us of pure FP work between clock reads
        for _ in 1:300
            x = muladd(x, 1.0000001, 1.0e-12)
        end
        now = time_ns()
        d = (now - prev) / 1e9
        if d > 0.002
            ngaps += 1
            println("gap ", round(d*1000, digits=2), "ms at t+",
                    round((Int64(now) - Int64(t_end) + Int64(round(seconds*1e9)))/1e9, digits=1), "s")
        end
        worst = max(worst, d)
        prev = now
        now > t_end && break
    end
    (worst, ngaps, x)
end
spin(2)  # warm up / compile
(worst, ngaps, _) = spin(parse(Float64, ARGS[1]))
println("worst=", round(worst*1000, digits=2), "ms ngaps=", ngaps)
