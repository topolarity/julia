# Compiles many small functions, each in its own LinkGraph, in one process and
# reports the number of memory mappings as it goes. A memory manager that
# gives every graph its own differently protected pages adds a few mappings
# per graph and eventually hits the kernel's limit (`vm.max_map_count`, 65530
# by default on Linux), after which mmap/mprotect fail with ENOMEM
# (llvm/llvm-project#63236).
# Usage: julia map_count.jl [N]
include(joinpath(@__DIR__, "common.jl"))
const N = isempty(ARGS) ? 40_000 : parse(Int, ARGS[1])
report("map_count_0")
for i in 1:N
    f = @eval $(Symbol(:m_, i))(x::Float64) = x * $(i + 0.5) + 1.0
    got = Base.invokelatest(f, 2.0)
    got == 2.0 * (i + 0.5) + 1.0 || error("m_$i(2.0) == $got")
    i % 1000 == 0 && (report("map_count_$i"); flush(stdout))
end
