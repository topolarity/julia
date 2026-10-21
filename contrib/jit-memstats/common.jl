# Prints the JIT memory counters from the temporary instrumentation in
# src/cgmemmgr.cpp, along with the resident set size of the process. On a build
# without that instrumentation (e.g. master or JuliaLang/julia#60915), prints
# only what can be measured from outside: RSS and the number of mappings.
using Libdl
# The counters live in libjulia-codegen, which is not in the global namespace
# on every platform (e.g. macOS), so look them up there explicitly.
const LIBCODEGEN = only(filter(contains("libjulia-codegen"), Libdl.dllist()))
const HAS_MEMSTATS = Libdl.dlsym(Libdl.dlopen(LIBCODEGEN), :jl_jit_memstats; throw_error=false) !== nothing

# Number of memory mappings in the process, counted the same way as the
# instrumentation does: lines of /proc/self/maps on Linux, entries of the
# task's VM map on macOS.
function count_mappings()
    if Sys.islinux()
        return countlines("/proc/self/maps")
    elseif Sys.isapple()
        task = unsafe_load(cglobal(:mach_task_self_, UInt32))
        addr = Ref{UInt64}(0); sz = Ref{UInt64}(0)
        info = zeros(Int32, 16); cnt = Ref{UInt32}(0); obj = Ref{UInt32}(0)
        n = 0
        while true
            cnt[] = 9 # VM_REGION_BASIC_INFO_COUNT_64
            kr = ccall(:mach_vm_region, Cint,
                       (UInt32, Ref{UInt64}, Ref{UInt64}, Cint, Ptr{Int32}, Ref{UInt32}, Ref{UInt32}),
                       task, addr, sz, 9 #= VM_REGION_BASIC_INFO_64 =#, info, cnt, obj)
            kr == 0 || break
            n += 1
            addr[] += sz[]
        end
        return n
    end
    return 0
end

function report(label)
    GC.gc(true); GC.gc(false)
    rss = Ref{Csize_t}(0)
    ccall(:uv_resident_set_memory, Cint, (Ptr{Csize_t},), rss)
    if !HAS_MEMSTATS
        println("RESULT label=$label allocator=uninstrumented rss=$(rss[]) ",
                "mappings=$(count_mappings()) jit_total_bytes=$(Base.jit_total_bytes())")
        return
    end
    stats = zeros(UInt64, 9)
    ccall((:jl_jit_memstats, LIBCODEGEN), Cvoid, (Ptr{UInt64},), stats)
    allocator = unsafe_string(ccall((:jl_jit_memstats_allocator, LIBCODEGEN), Cstring, ()))
    println("RESULT label=$label mm=$(get(ENV, "JULIA_JIT_MM", "default")) ",
            "allocator=$allocator rss=$(rss[]) graphs=$(stats[1]) content=$(stats[2]) ",
            "mapped=$(stats[3]) wrbuf=$(stats[4]) pp4k=$(stats[5]) pp16k=$(stats[6]) ",
            "pp64k=$(stats[7]) arenas=$(stats[8]) mappings=$(stats[9]) jit_total_bytes=$(Base.jit_total_bytes())")
end
