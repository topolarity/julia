using Test, JuliaLowering

test_mod = Module()

# Test that two array element types are equal and that they are also equal
# elementwise
function ≅(a, b)
    eltype(a) == eltype(b) && a == b
end

# vect
# From PkgEval: SOLPS2imas v2.2.5, via IMASdd src/io.jl:949 (kwarg in indexed assignment)
@test JuliaLowering.include_string(test_mod, """
[1,2,3]
""") ≅ [1,2,3]

# hcat
@test JuliaLowering.include_string(test_mod, """
[1 2 3]
""") ≅ [1 2 3]

# typed_hcat
@test JuliaLowering.include_string(test_mod, """
Int[1.0 2.0 3.0]
""") ≅ [1 2 3]

# splat with vect/hcat/typed_hcat
@test JuliaLowering.include_string(test_mod, """
let xs = [1,2,3]
    [0, xs...]
end
""") ≅ [0,1,2,3]
@test JuliaLowering.include_string(test_mod, """
let xs = [1,2,3]
    [0 xs...]
end
""") ≅ [0 1 2 3]
@test JuliaLowering.include_string(test_mod, """
let xs = [1,2,3]
    Int[0 xs...]
end
""") ≅ Int[0 1 2 3]

# vcat
@test JuliaLowering.include_string(test_mod, """
[1;2;3]
""") ≅ [1; 2; 3]

@test JuliaLowering.include_string(test_mod, """
let
    xs = (1,2)
    [xs...; xs...]
end
""") ≅ [1,2,1,2]

# hvcat
@test JuliaLowering.include_string(test_mod, """
[1 2 3; 4 5 6]
""") ≅ [1 2 3;
        4 5 6]

# hvcat_rows
@test JuliaLowering.include_string(test_mod, """
let
    xs = (1,2)
    [xs... 3; 4 xs...]
end
""") ≅ [1 2 3;
        4 1 2]

# typed_vcat
@test JuliaLowering.include_string(test_mod, """
Int[1.0; 2.0; 3.0]
""") ≅ [1; 2; 3]

# typed_hvcat
@test JuliaLowering.include_string(test_mod, """
Int[1.0 2.0 3.0; 4.0 5.0 6.0]
""") ≅ [1 2 3;
        4 5 6]

# typed_hvcat_rows
@test JuliaLowering.include_string(test_mod, """
let
    xs = (1.0,2.0)
    Int[xs... 3; 4 xs...]
end
""") ≅ [1 2 3;
        4 1 2]

# ncat with a single dimension
@test JuliaLowering.include_string(test_mod, """
[1 ;;; 2 ;;; 3]
""") ≅ [1 ;;; 2 ;;; 3]

@test JuliaLowering.include_string(test_mod, """
Int[1.0 ;;; 2.0 ;;; 3.0]
""") ≅ [1 ;;; 2 ;;; 3]

# Lowering of ref to setindex
@test JuliaLowering.include_string(test_mod, """
let
    as = [0,0,0,0]
    as[begin] = 1
    as[2] = 2
    as[end] = 4
    as
end
""") == [1, 2, 0, 4]

@test JuliaLowering.include_string(test_mod, """
let
    as = zeros(Int, 2,3)
    as[begin, end] = 1
    as[end, begin] = 2
    js = (2,)
    as[js..., end] = 3
    as
end
""") == [0 0 1;
         2 0 3]

# getindex
@test JuliaLowering.include_string(test_mod, """
let
    x = [1 2;
         3 4]
    (x[end,begin], x[begin,end])
end
""") == (3, 2)

# getindex with splats
@test JuliaLowering.include_string(test_mod, """
let
    x = [1 2;
         3 4
         ;;;
         5 6;
         7 8]
    inds = (2,1)
    ind1 = (1,)
    (x[inds..., begin], x[inds..., end], x[1, inds...],
     x[ind1..., ind1..., end])
end
""") == (3, 7, 2, 5)

# begin/end not replaced in some cases
JuliaLowering.include_string(test_mod, "f(args...;kws...) = 2")
@test JuliaLowering.include_string(test_mod, """
    [7,8,9][f(;var"end"=123, var"begin"=456)]
""") === 8
@test JuliaLowering.include_string(test_mod, """
    [7,8,9][f(quote var"end" end)]
""") === 8
@test JuliaLowering.include_string(test_mod, """
let var"end" = [1,2,3], y = [7,8,9]
    y[var"end"[var"end"]]
end
""") === 9

# Keyword arguments in indexing position, e.g. `a[i, kw=v]`, desugar to a
# regular keyword call of getindex/setindex! (matching flisp lowering). Only
# the comma form is legal syntax; `a[i; kw=v]` is a parse error under both
# lowerers and is not tested here.
JuliaLowering.include_string(test_mod, """
struct KwIndexable
end
Base.getindex(::KwIndexable, i; compress=0) = (i, compress)
Base.getindex(::KwIndexable, i, j; compress=0) = (i, j, compress)
Base.setindex!(::KwIndexable, v, i; compress=0) = (i, v, compress)
Base.lastindex(::KwIndexable) = 99
Base.lastindex(::KwIndexable, d::Int) = 99

struct KwIndexableNum
end
Base.getindex(::KwIndexableNum, i; compress=0) = i + compress
Base.setindex!(::KwIndexableNum, v, i; compress=0) = (i, v, compress)
""")

# read
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable()
    a[1, compress=2]
end
""") == (1, 2)

# write
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable()
    a[1, compress=2] = 10
end
""") == 10

# update-op through kw indexing
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexableNum()
    a[1, compress=2] += 1
end
""") == 4

# `end` inside brackets alongside a keyword argument (counts as an index slot
# for dimensionality, same as flisp: `lastindex(a, 1)` is called)
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable()
    a[end, compress=2]
end
""") == (99, 2)

# multiple keyword arguments
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable()
    a[1, 2, compress=3]
end
""") == (1, 2, 3)

# keyword argument after a splatted positional argument
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable(), xs = (1, 2)
    a[xs..., compress=3]
end
""") == (1, 2, 3)

# a computed (non-atom) index alongside a keyword argument
@test JuliaLowering.include_string(test_mod, """
let a = KwIndexable(), xs = (2,)
    a[xs..., compress=1+2]
end
""") == (2, 3)

# the semicolon form remains rejected under JuliaLowering, same as flisp
# (it is not valid `ref` syntax at all, regardless of this fix)
@test_throws JuliaLowering.LoweringError JuliaLowering.include_string(test_mod, """
let a = KwIndexable()
    a[1; compress=2]
end
""")
