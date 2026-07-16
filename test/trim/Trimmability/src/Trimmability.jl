# Test that various constructs support trimming
module Trimmability

using Sockets

world::String = "world!"
const str = OncePerProcess{String}() do
    return "Hello, " * world
end

abstract type Shape end
struct Square <: Shape
    side::Float64
end
struct Circle <: Shape
    radius::Float64
end
area(s::Square) = s.side^2
area(c::Circle) = pi*c.radius^2

sum_areas(v::Vector{Shape}) = sum(area, v)

mutable struct Foo; x::Int; end
const storage = Foo[]
function add_one(x::Cint)::Cint
    push!(storage, Foo(x))
    return x + 1
end

function _test_cat()
    # hcat
    _cat1a = hcat(randn(3), rand(3), randn(3))
    _cat1b = [randn(3) rand(3) randn(3)]
    _cat1c = hcat(randn(3,3), rand(3,3), randn(3,3))
    _cat1d = [randn(3,3) rand(3,3) randn(3,3)]
    _cat1e = hcat(randn(3,3,3), rand(3,3,3), randn(3,3,3))
    _cat1f = [randn(3,3,3) rand(3,3,3) randn(3,3,3)]

    # v_cat
    _cat2a = vcat(randn(3), rand(3), randn(3))
    _cat2b = [randn(3); rand(3); randn(3)]
    _cat2c = vcat(randn(3,3), rand(3,3), randn(3,3))
    _cat2d = [randn(3,3); rand(3,3); randn(3,3)]
    _cat2e = vcat(randn(3,3,3), rand(3,3,3), randn(3,3,3))
    _cat2f = [randn(3,3,3); rand(3,3,3); randn(3,3,3)]

    # hvcat
    _cat3a = hvcat((2,2), rand(3,2), randn(3,4), rand(1,2), randn(1,4))
    _cat3b = [rand(3,2) randn(3,4); rand(1,2) randn(1,4)]
    _cat3c = hvcat((2, 2), rand(5,2,3), rand(5,4,3), rand(1,2,3), rand(1,4,3))
    _cat3d = [rand(5,2,3) rand(5,4,3); rand(1,2,3) rand(1,4,3)]

    # cat
    _cat4a = cat(randn(3), randn(3); dims = 1)
    _cat4b = cat(randn(3,3,3), randn(3,3,3); dims = 2)
    _cat4c = cat(randn(3), randn(3,3); dims = 2)
    _cat4d = cat(randn(3), randn(3), rand(3), rand(3), randn(3), randn(3); dims = (1,))
    _cat4e = cat(randn(3,3), randn(3,3), rand(3,3), rand(3,3), randn(3,3), randn(3,3); dims = (1,2))
    _cat4f = cat(randn(3,3,3), randn(3,3); dims=(1,3))

    # hvncat
    _cat5a = hvncat(2, randn(3), randn(3), randn(3))
    _cat5b = [randn(3) ;; randn(3) ;; randn(3)]
    _cat5c = hvncat(2, randn(3,3), randn(3,3), randn(3,3))
    _cat5d = [randn(3,3) ;; randn(3,3) ;; randn(3,3)]
    _cat5e = hvncat((1, 2, 2), false, randn(2,3), randn(2,3), randn(2,3), randn(2,3))
    _cat5f = [randn(2,3) ;; randn(2,3) ;;; randn(2,3) ;; randn(2,3)]

    # stack
    _cat6a = stack([randn(3), randn(3), randn(3)])
    _cat6b = stack([randn(3), randn(3), randn(3)]; dims=1)
    _cat6c = stack([randn(2,3), randn(2,3)]; dims=3)
    _cat6d = stack(x -> x .^ 2, [randn(3), randn(3)])

    # repeat
    _cat7a = repeat(randn(3), 2)
    _cat7b = repeat(randn(2,3), 2, 3)
    _cat7c = repeat(randn(2,3); inner=(2,1), outer=(1,3))
    _cat7d = repeat(randn(3,3,3), 1, 2, 1)

    # aggregate to prevent deletion
    _cat1 = _cat1a[1] + _cat1b[1] + _cat1c[1] + _cat1d[1] + _cat1e[1] + _cat1f[1]
    _cat2 = _cat2a[1] + _cat2b[1] + _cat2c[1] + _cat2d[1] + _cat2e[1] + _cat2f[1]
    _cat3 = _cat3a[1] + _cat3b[1] + _cat3c[1] + _cat3d[1]
    _cat4 = _cat4a[1] + _cat4b[1] + _cat4c[1] + _cat4d[1] + _cat4e[1] + _cat4f[1]
    _cat5 = _cat5a[1] + _cat5b[1] + _cat5c[1] + _cat5d[1] + _cat5e[1] + _cat5f[1]
    _cat6 = _cat6a[1] + _cat6b[1] + _cat6c[1] + _cat6d[1]
    _cat7 = _cat7a[1] + _cat7b[1] + _cat7c[1] + _cat7d[1]

    return _cat1 + _cat2 + _cat3 + _cat4 + _cat5 + _cat6 + _cat7
end


# A finalizer registered from reachable code. Its target is reached only via the
# finalizer/invokelatest edge (not a static invoke), so the kept set must include it or
# it MethodErrors at GC time -- a regression test for that soundness hole.
mutable struct FinResource; id::Int; end
function fin_cleanup(r::FinResource)
    println(Core.stdout, "finalized resource ", r.id)
    return nothing
end
@noinline function register_fin()
    r = FinResource(99)
    finalizer(fin_cleanup, r)
    return nothing
end

# A TypedCallable constructed in reachable code: the optimizer resolves its dispatch
# trampoline, codegen emits the trampoline's adapter into the image, and
# `collectinvokes!` ships the dispatched target -- so calling it needs no runtime JIT.
tc_add(x::Int)::Int = x + 1
@noinline make_tc() = Core.TypedCallable{Tuple{Int},Int}(tc_add)
call_tc(t::Core.TypedCallable{Tuple{Int},Int}, x::Int) = t(x)

# A TypedCallable constructed by top-level *execution* at build time: it reaches the
# image as a serialized value with no compiled construction site, so its adapter comes
# from the live-cache sweep in `generate_cfunc_thunks` (and its target from the trim
# entry's seeding pass).
tc_mul(x::Int)::Int = x * 2
const TC_CONST = Core.TypedCallable{Tuple{Int},Int}(tc_mul)

# An OpaqueClosure stored into an Array and called after extraction. An OC's body is
# fixed: the optimizer resolves the body CodeInstance into the construction
# (`handle_new_opaque_closure_call!`), `collectinvokes!` keeps that CI like an `:invoke`
# edge, and codegen emits the OC's `JL_ADAPTER_OPAQUE_CLOSURE` adapter inline at the
# construction site (`emit_inline_abi_adapter`), so the no-JIT image resolves nothing at
# runtime. Routing the OC through an Array forces a real heap construction -- the
# PartialOpaque transform cannot inline the call away or elide the construction -- so this
# genuinely exercises the construction codegen and the call through the compiled specsig
# adapter. Captures `c` (a non-empty env).
@noinline function array_oc_roundtrip(c::Int, x::Int)
    ocs = Core.OpaqueClosure{Tuple{Int},Int}[]
    push!(ocs, Base.Experimental.@opaque (y::Int) -> y + c)
    return ocs[1](x)
end

# A capture-free OpaqueClosure with a `Float64` return type (a different adapter `rt`
# and an empty env tuple), returned from one `@noinline` function and called from another --
# so it escapes as a real OC value and dispatches through the adapter rather than inlining.
@noinline make_scaler() = Base.Experimental.@opaque (y::Int) -> y * 2.0
@noinline apply_oc_f(oc, x::Int) = oc(x)::Float64

function @main(args::Vector{String})::Cint
    println(Core.stdout, str())
    println(Core.stdout, PROGRAM_FILE)
    foreach(x->println(Core.stdout, x), args)

    # TypedCallable dispatched through its image-serialized adapter
    println(Core.stdout, call_tc(make_tc(), 41))
    println(Core.stdout, call_tc(TC_CONST, 21))

    # An OpaqueClosure routed through an Array (see array_oc_roundtrip): a real OC object
    # is constructed (not inlined away), its body CI kept by collectinvokes!, and its
    # adapter emitted inline at the construction site. 23 + 100 -> 123.
    println(Core.stdout, array_oc_roundtrip(100, 23))
    # A capture-free OpaqueClosure with a Float64 rt, returned and called across a
    # @noinline boundary (see make_scaler / apply_oc_f). 21 * 2.0 -> 42.0.
    println(Core.stdout, apply_oc_f(make_scaler(), 21))

    # Register a finalizer and force collection so it runs before exit.
    register_fin()
    GC.gc(true); GC.gc(true)

    # test map/mapreduce; should work but relies on inlining and other optimizations
    # test that you can dispatch to some number of concrete cases
    println(Core.stdout, sum_areas(Shape[Circle(1), Square(2)]))

    arr = rand(10)
    sorted_arr = sort(arr)
    tot = sum(sorted_arr)
    tot = prod(sorted_arr)
    a = any(x -> x > 0, sorted_arr)
    b = all(x -> x >= 0, sorted_arr)
    c = map(x -> x^2, sorted_arr)
    d = mapreduce(x -> x^2, +, sorted_arr)
    # e = reduce(xor, rand(Int, 10))

    println(Core.stdout, _test_cat())
    println(Core.stdout, "Version: ", v"1.1")
    println(Core.stdout, "# preferences: ", length(Base.get_preferences()))

    for i = 1:10
        # https://github.com/JuliaLang/julia/issues/60846
        add_one(Cint(i))
        GC.gc()
    end

    try
        sock = connect("localhost", 4900)
        if isopen(sock)
            write(sock, "Hello")
            flush(sock)
            close(sock)
        end
    catch
    end

    Base.donotdelete(reshape([1,2,3],:,1,1))

    return 0
end

end
