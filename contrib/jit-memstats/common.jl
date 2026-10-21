# Prints the JIT memory counters from the temporary instrumentation in
# src/cgmemmgr.cpp, along with the resident set size of the process.
using Libdl
# The counters live in libjulia-codegen, which is not in the global namespace
# on every platform (e.g. macOS), so look them up there explicitly.
const LIBCODEGEN = only(filter(contains("libjulia-codegen"), Libdl.dllist()))
function report(label)
    GC.gc(true); GC.gc(false)
    rss = Ref{Csize_t}(0)
    ccall(:uv_resident_set_memory, Cint, (Ptr{Csize_t},), rss)
    stats = zeros(UInt64, 8)
    ccall((:jl_jit_memstats, LIBCODEGEN), Cvoid, (Ptr{UInt64},), stats)
    allocator = unsafe_string(ccall((:jl_jit_memstats_allocator, LIBCODEGEN), Cstring, ()))
    println("RESULT label=$label mm=$(get(ENV, "JULIA_JIT_MM", "default")) ",
            "allocator=$allocator rss=$(rss[]) graphs=$(stats[1]) content=$(stats[2]) ",
            "mapped=$(stats[3]) wrbuf=$(stats[4]) pp4k=$(stats[5]) pp16k=$(stats[6]) ",
            "pp64k=$(stats[7]) arenas=$(stats[8]) jit_total_bytes=$(Base.jit_total_bytes())")
end
