# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
    TypedCallable{A,R}(f)

Wrap the callable `f` as a concretely-typed callable. When called with arguments
matching the argument tuple type `A`, it dispatches `f` in the *latest* world and
returns a value of type `R`.

Unlike an [`OpaqueClosure`](@ref Base.Experimental.@opaque), which captures the world
age of its creation, a `TypedCallable` always invokes in the current world
(re-resolving its target when methods are redefined), analogous to `@cfunction`.

!!! warning
    This interface is experimental and subject to change or removal without notice.
"""
function (::Type{Core.TypedCallable{A,R}})(@nospecialize(f)) where {A,R}
    A <: Tuple || throw(ArgumentError("TypedCallable argument type must be a Tuple type"))
    # Route through the `Core._typed_callable` builtin (rather than a direct ccall) so
    # the optimizer can see the construction site: infer its `TypedCallable{A,R}` type
    # and, for `--trim`, discover the latest-world dispatch target via `collectinvokes!`.
    return Core._typed_callable(f, A, R)::Core.TypedCallable{A,R}
end
