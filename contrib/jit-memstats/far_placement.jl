include(joinpath(@__DIR__, "common.jl"))
# Interleaves JIT compilation with large address-space reservations, so that
# blocks mapped later land far (> 4 GiB) from blocks mapped earlier. A memory
# manager that can lay one LinkGraph out across such blocks fails to link
# (PC-relative fixups out of range); this checks that every function compiled
# under these conditions links and computes the right result.
const PROT_NONE = Cint(0)
const MAP_FLAGS = Sys.isapple() ? Cint(0x0002 | 0x1000 | 0x0040) :  # PRIVATE|ANON|NORESERVE
                  Sys.islinux() ? Cint(0x02 | 0x20 | 0x4000) :
                  error("far_placement.jl: unsupported OS")
const GAP = UInt(8) << 30
const HOLE = UInt(1) << 20  # smallest JIT block (256 pages of 4 KiB)
function reserve(len)
    p = ccall(:mmap, Ptr{Cvoid}, (Ptr{Cvoid}, Csize_t, Cint, Cint, Cint, Int64),
              C_NULL, len, PROT_NONE, MAP_FLAGS, -1, 0)
    p == Ptr{Cvoid}(typemax(UInt)) && error("mmap of reservation failed")
    return UInt(p)
end
# Reserve a gap, then fill every free hole that could hold a JIT block until
# the kernel hands out the address right next to the gap (above it when
# allocating bottom-up as on macOS, below it when top-down as on Linux), so
# the next block is mapped on the far side of the gap.
function reserve_gap()
    g = reserve(GAP)
    for _ in 1:100_000
        p = reserve(HOLE)
        (p == g + GAP || p + HOLE == g) && return
    end
    error("could not fill the holes around the reservation")
end

const R = Ref{Any}()
const N = 1500
for i in 1:N
    i % 10 == 1 && reserve_gap()
    # Float literals, a load of a JIT global, and calls into libjulia/libm, so
    # that each graph has code, GOT entries and stubs.
    f = @eval $(Symbol(:far_, i))(x::Float64) =
        (isassigned(R) ? 0.0 : sin(x) * $(i + 0.123456789) + x^3.25) + length(string($i))
    want = sin(0.7) * (i + 0.123456789) + 0.7^3.25 + length(string(i))
    got = Base.invokelatest(f, 0.7)
    got == want || error("far_$i(0.7) == $got, expected $want")
end
report("far_placement")
