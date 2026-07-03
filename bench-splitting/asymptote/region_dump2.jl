include(joinpath(@__DIR__, "straight_gen_inc.jl"))
Core.eval(Main, straight_expr(65536))
Base.invokelatest(bench_f, 1.5)
println(stderr, "CodeInstance fields: ", fieldnames(Core.CodeInstance))
m = only(methods(bench_f))
mi = only(Base.specializations(m))
ci = mi.cache
ptr = try
    reinterpret(Ptr{UInt8}, getfield(ci, :specptr))
catch
    println(stderr, "specptr failed; props: ", propertynames(ci))
    rethrow()
end
println(stderr, "parent at ", ptr)
glue = Vector{UInt8}(undef, 8192)
unsafe_copyto!(pointer(glue), ptr, 8192)
addrs = UInt64[]
for i in 1:8180
    if glue[i] == 0x48 && glue[i+1] == 0xb8
        v = UInt64(0)
        for k in 0:7
            v |= UInt64(glue[i+2+k]) << (8k)
        end
        # plausible userspace pointer, 16-aligned
        if v > 0x10000 && v < 0x0000800000000000 && v % 16 == 0
            push!(addrs, v)
        end
    end
end
println(stderr, "candidate region addrs: ", length(addrs))
isempty(addrs) && exit(1)
for (i, a) in enumerate(sort(unique(addrs)))
    n = 480 * 1024
    bytes = Vector{UInt8}(undef, n)
    unsafe_copyto!(pointer(bytes), Ptr{UInt8}(a), n)
    write(joinpath(@__DIR__, "region_" * string(i) * ".bin"), bytes)
    println(stderr, "dumped cand ", i, " from 0x", string(a, base=16))
end
