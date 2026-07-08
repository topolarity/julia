########################################
# Simple call
f(x, y)
#---------------------
1   TestMod.f
2   TestMod.x
3   TestMod.y
4   (call %₁ %₂ %₃)
5   (return %₄)

########################################
# Keyword calls
f(x; a=1, b=2)
#---------------------
1   TestMod.f
2   (call core.tuple :a :b)
3   (call core.apply_type core.NamedTuple %₂)
4   (call core.tuple 1 2)
5   (call %₃ %₄)
6   TestMod.x
7   (call core.kwcall %₅ %₁ %₆)
8   (return %₇)

########################################
# Keyword call with only splats for kws
f(; ks1..., ks2...)
#---------------------
1   TestMod.f
2   (call core.NamedTuple)
3   TestMod.ks1
4   (call top.merge %₂ %₃)
5   TestMod.ks2
6   (call top.merge %₄ %₅)
7   (call top.isempty %₆)
8   (gotoifnot %₇ label₁₁)
9   (call %₁)
10  (return %₉)
11  (call core.kwcall %₆ %₁)
12  (return %₁₁)

########################################
# Error: Call with repeated keywords
f(x; a=1, a=2)
#---------------------
LoweringError:
f(x; a=1, a=2)
#         ╙ ── Repeated keyword argument name

########################################
# literal_pow lowering
x^42
#---------------------
1   TestMod.^
2   TestMod.x
3   (call core.apply_type top.Val 42)
4   (call %₃)
5   (call top.literal_pow %₁ %₂ %₄)
6   (return %₅)

########################################
# almost but not quite literal_pow lowering :)
x^42.0
#---------------------
1   TestMod.^
2   TestMod.x
3   (call %₁ %₂ 42.0)
4   (return %₃)

########################################
# Error: Call with no function name
@ast_ [K"call"]
#---------------------
LoweringError:
#= line 1 =# - malformed `call`
Expression:
  (call)
Containing expressions:
  (call)

########################################
# Simple broadcast
x .* y .+ f.(z)
#---------------------
1   TestMod.+
2   TestMod.*
3   TestMod.x
4   TestMod.y
5   (call top.broadcasted %₂ %₃ %₄)
6   TestMod.f
7   TestMod.z
8   (call top.broadcasted %₆ %₇)
9   (call top.broadcasted %₁ %₅ %₈)
10  (call top.materialize %₉)
11  (return %₁₀)

########################################
# Broadcast with unary function calls
.+x
#---------------------
1   TestMod.+
2   TestMod.x
3   (call top.broadcasted %₁ %₂)
4   (call top.materialize %₃)
5   (return %₄)

########################################
# Broadcast with short circuit operators
x .&& y .|| z
#---------------------
1   TestMod.x
2   TestMod.y
3   (call top.broadcasted top.andand %₁ %₂)
4   TestMod.z
5   (call top.broadcasted top.oror %₃ %₄)
6   (call top.materialize %₅)
7   (return %₆)

########################################
# Scalar comparison chain
x < y < z
#---------------------
1   TestMod.<
2   TestMod.x
3   TestMod.y
4   (call %₁ %₂ %₃)
5   (gotoifnot %₄ label₁₁)
6   TestMod.<
7   TestMod.y
8   TestMod.z
9   (call %₆ %₇ %₈)
10  (return %₉)
11  (return false)

########################################
# Broadcasted comparison chain
x .< y .< z
#---------------------
1   TestMod.<
2   TestMod.x
3   TestMod.y
4   (call top.broadcasted %₁ %₂ %₃)
5   TestMod.<
6   TestMod.y
7   TestMod.z
8   (call top.broadcasted %₅ %₆ %₇)
9   (call top.broadcasted top.& %₄ %₈)
10  (call top.materialize %₉)
11  (return %₁₀)

########################################
# Mixed scalar / broadcasted comparison chain
a < b < c .< d .< e
#---------------------
1   TestMod.<
2   TestMod.a
3   TestMod.b
4   (call %₁ %₂ %₃)
5   (gotoifnot %₄ label₁₁)
6   TestMod.<
7   TestMod.b
8   TestMod.c
9   (= slot₁/if_val (call %₆ %₇ %₈))
10  (goto label₁₂)
11  (= slot₁/if_val false)
12  slot₁/if_val
13  TestMod.<
14  TestMod.c
15  TestMod.d
16  (call top.broadcasted %₁₃ %₁₄ %₁₅)
17  (call top.broadcasted top.& %₁₂ %₁₆)
18  TestMod.<
19  TestMod.d
20  TestMod.e
21  (call top.broadcasted %₁₈ %₁₉ %₂₀)
22  (call top.broadcasted top.& %₁₇ %₂₁)
23  (call top.materialize %₂₂)
24  (return %₂₃)

########################################
# Mixed scalar / broadcasted comparison chain
a .< b .< c < d < e
#---------------------
1   TestMod.<
2   TestMod.a
3   TestMod.b
4   (call top.broadcasted %₁ %₂ %₃)
5   TestMod.<
6   TestMod.b
7   TestMod.c
8   (call top.broadcasted %₅ %₆ %₇)
9   (call top.broadcasted top.& %₄ %₈)
10  TestMod.<
11  TestMod.c
12  TestMod.d
13  (call %₁₀ %₁₁ %₁₂)
14  (gotoifnot %₁₃ label₂₀)
15  TestMod.<
16  TestMod.d
17  TestMod.e
18  (= slot₁/if_val (call %₁₅ %₁₆ %₁₇))
19  (goto label₂₁)
20  (= slot₁/if_val false)
21  slot₁/if_val
22  (call top.broadcasted top.& %₉ %₂₁)
23  (call top.materialize %₂₂)
24  (return %₂₃)

########################################
# Comparison chain fused with other broadcasting
x .+ (a .< b .< c)
#---------------------
1   TestMod.+
2   TestMod.x
3   TestMod.<
4   TestMod.a
5   TestMod.b
6   (call top.broadcasted %₃ %₄ %₅)
7   TestMod.<
8   TestMod.b
9   TestMod.c
10  (call top.broadcasted %₇ %₈ %₉)
11  (call top.broadcasted top.& %₆ %₁₀)
12  (call top.broadcasted %₁ %₂ %₁₁)
13  (call top.materialize %₁₂)
14  (return %₁₃)

########################################
# Broadcast with literal_pow
x.^3
#---------------------
1   TestMod.^
2   TestMod.x
3   (call core.apply_type top.Val 3)
4   (call %₃)
5   (call top.broadcasted top.literal_pow %₁ %₂ %₄)
6   (call top.materialize %₅)
7   (return %₆)

########################################
# Broadcast with keywords
f.(x, y, z = 1; w = 2)
#---------------------
1   top.broadcasted_kwsyntax
2   (call core.tuple :z :w)
3   (call core.apply_type core.NamedTuple %₂)
4   (call core.tuple 1 2)
5   (call %₃ %₄)
6   TestMod.f
7   TestMod.x
8   TestMod.y
9   (call core.kwcall %₅ %₁ %₆ %₇ %₈)
10  (call top.materialize %₉)
11  (return %₁₀)

########################################
# Broadcast with unary dot syntax
(.+)(x,y)
#---------------------
1   TestMod.+
2   TestMod.x
3   TestMod.y
4   (call top.broadcasted %₁ %₂ %₃)
5   (call top.materialize %₄)
6   (return %₅)

########################################
# Trivial in-place broadcast update
x .= y
#---------------------
1   TestMod.x
2   TestMod.y
3   (call top.broadcasted top.identity %₂)
4   (call top.materialize! %₁ %₃)
5   (return %₄)

########################################
# Fused in-place broadcast update
x .= y .+ z
#---------------------
1   TestMod.x
2   TestMod.+
3   TestMod.y
4   TestMod.z
5   (call top.broadcasted %₂ %₃ %₄)
6   (call top.materialize! %₁ %₅)
7   (return %₆)

########################################
# In-place broadcast update with property assignment on left hand side
x.prop .= y
#---------------------
1   TestMod.x
2   (call top.dotgetproperty %₁ :prop)
3   TestMod.y
4   (call top.broadcasted top.identity %₃)
5   (call top.materialize! %₂ %₄)
6   (return %₅)

########################################
# In-place broadcast update with ref on left hand side
x[i,end] .= y
#---------------------
1   TestMod.x
2   TestMod.i
3   (call top.lastindex %₁ 2)
4   (call top.dotview %₁ %₂ %₃)
5   TestMod.y
6   (call top.broadcasted top.identity %₅)
7   (call top.materialize! %₄ %₆)
8   (return %₇)

########################################
# <: as a function call
x <: y
#---------------------
1   TestMod.<:
2   TestMod.x
3   TestMod.y
4   (call %₁ %₂ %₃)
5   (return %₄)

########################################
# >: as a function call
x >: y
#---------------------
1   TestMod.>:
2   TestMod.x
3   TestMod.y
4   (call %₁ %₂ %₃)
5   (return %₄)

########################################
# --> as a function call
x --> y
#---------------------
1   TestMod.-->
2   TestMod.x
3   TestMod.y
4   (call %₁ %₂ %₃)
5   (return %₄)

########################################
# Prefix <: with a splatted argument (JuliaLowering.jl#18)
<:(xs...)
#---------------------
1   TestMod.<:
2   TestMod.xs
3   (call core._apply_iterate top.iterate %₁ %₂)
4   (return %₃)

########################################
# Prefix >: with a splatted argument
>:(xs...)
#---------------------
1   TestMod.>:
2   TestMod.xs
3   (call core._apply_iterate top.iterate %₁ %₂)
4   (return %₃)

########################################
# Prefix <: with a mix of plain and splatted arguments
<:(a, xs...)
#---------------------
1   TestMod.<:
2   TestMod.a
3   (call core.tuple %₂)
4   TestMod.xs
5   (call core._apply_iterate top.iterate %₁ %₃ %₄)
6   (return %₅)

########################################
# Prefix <: with 3 plain arguments
<:(a, b, c)
#---------------------
1   TestMod.<:
2   TestMod.a
3   TestMod.b
4   TestMod.c
5   (call %₁ %₂ %₃ %₄)
6   (return %₅)

########################################
# basic ccall
ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   (call top.unsafe_convert %₁ %₂)
4   (foreigncall :strlen (static_eval TestMod.Csize_t) (static_eval (call core.svec TestMod.Cstring)) 0 :ccall %₃ %₂)
5   (return %₄)

########################################
# ccall with library name as a global var
ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   (call top.unsafe_convert %₁ %₂)
4   (foreigncall (foreignsymbol (tuple-p (inert strlen) TestMod.libc)) (static_eval TestMod.Csize_t) (static_eval (call core.svec TestMod.Cstring)) 0 :ccall %₃ %₂)
5   (return %₄)

########################################
# ccall with a calling convention
ccall(:foo, stdcall, Csize_t, ())
#---------------------
1   (foreigncall :foo (static_eval TestMod.Csize_t) (static_eval (call core.svec)) 0 :stdcall)
2   (return %₁)

########################################
# ccall with Any args become core.Any and don't need conversion or GC roots
ccall(:foo, stdcall, Csize_t, (Any,), x)
#---------------------
1   core.Any
2   TestMod.x
3   (foreigncall :foo (static_eval TestMod.Csize_t) (static_eval (call core.svec core.Any)) 0 :stdcall %₂)
4   (return %₃)

########################################
# ccall with variable as function name (must eval to a pointer)
ccall(ptr, Csize_t, (Cstring,), "asdfg")
#---------------------
1   TestMod.Cstring
2   (call top.cconvert %₁ "asdfg")
3   TestMod.ptr
4   (call top.unsafe_convert %₁ %₂)
5   (foreigncall %₃ (static_eval TestMod.Csize_t) (static_eval (call core.svec TestMod.Cstring)) 0 :ccall %₄ %₂)
6   (return %₅)

########################################
# ccall with varargs
ccall(:printf, Cint, (Cstring, Cstring...), "%s = %s\n", "2 + 2", "5")
#---------------------
1   TestMod.Cstring
2   TestMod.Cstring
3   TestMod.Cstring
4   (call top.cconvert %₁ "%s = %s\n")
5   (call top.cconvert %₂ "2 + 2")
6   (call top.cconvert %₃ "5")
7   (call top.unsafe_convert %₁ %₄)
8   (call top.unsafe_convert %₂ %₅)
9   (call top.unsafe_convert %₃ %₆)
10  (foreigncall :printf (static_eval TestMod.Cint) (static_eval (call core.svec TestMod.Cstring TestMod.Cstring TestMod.Cstring)) 1 :ccall %₇ %₈ %₉ %₄ %₅ %₆)
11  (return %₁₀)

########################################
# Error: ccall with too few arguments
ccall(:foo, Csize_t)
#---------------------
LoweringError:
ccall(:foo, Csize_t)
└──────────────────┘ ── too few arguments to ccall

########################################
# Error: ccall with calling conv and too few arguments
ccall(:foo, thiscall, Csize_t)
#---------------------
LoweringError:
ccall(:foo, thiscall, Csize_t)
└────────────────────────────┘ ── too few arguments to ccall with calling convention specified

########################################
# Error: ccall without tuple for argument types
ccall(:foo, Csize_t, Cstring)
#---------------------
LoweringError:
ccall(:foo, Csize_t, Cstring)
#                    └─────┘ ── ccall argument types must be a tuple; try `(T,)`

########################################
# Error: ccall without tuple for argument types
ccall(:foo, (Csize_t,), "arg")
#---------------------
LoweringError:
ccall(:foo, (Csize_t,), "arg")
#           └────────┘ ── ccall argument types must be a tuple; try `(T,)` and check if you specified a correct return type

########################################
# Error: ccall with library name which is a local variable
let libc = "libc"
    ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let libc = "libc"
    ccall((:strlen, libc), Csize_t, (Cstring,), "asdfg")
#                   └──┘ ── function name and library expression cannot reference local variable
end

########################################
# Error: ccall with return type which is a local variable
let Csize_t = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let Csize_t = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#                  └─────┘ ── ccall return type cannot reference local variable
end

########################################
# Error: ccall with argument type which is a local variable
let Cstring = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
end
#---------------------
LoweringError:
let Cstring = 1
    ccall(:strlen, Csize_t, (Cstring,), "asdfg")
#                            └─────┘ ── ccall argument type cannot reference local variable
end

########################################
# ccall argument type may reference a local captured from an enclosing scope.
# The captured local is spliced into the method at definition time via
# `captured_local` / `replace_captured_locals!` (matching flisp, which builds
# such method bodies as spliced templates). This is the BandedMatrices
# `@eval`-loop LAPACK-wrapper idiom.
begin
    local Relty = Cchar
    function ccall_captures_local()
        ccall(:strlen, Csize_t, (Ptr{Relty},), "abc")
    end
end
#---------------------
1   TestMod.Cchar
2   (= slot₁/Relty %₁)
3   (method TestMod.ccall_captures_local)
4   latestworld
5   TestMod.ccall_captures_local
6   (call core.TypeEqOf %₅)
7   (call core.svec %₆)
8   (call core.svec)
9   SourceLocation::3:14
10  (call core.svec %₇ %₈ %₉)
11  --- code_info
    slots: [slot₁/#self#(!read)]
    1   TestMod.Ptr
    2   (captured_local 1)
    3   (call core.apply_type %₁ %₂)
    4   (call top.cconvert %₃ "abc")
    5   (call top.unsafe_convert %₃ %₄)
    6   (foreigncall :strlen (static_eval TestMod.Csize_t) (static_eval (call core.svec (call core.apply_type TestMod.Ptr (captured_local 1)))) 0 :ccall %₅ %₄)
    7   (return %₆)
12  (call core.svec slot₁/Relty)
13  (call JuliaLowering.replace_captured_locals! %₁₁ %₁₂)
14  --- method TestMod.ccall_captures_local %₁₀ %₁₃
15  latestworld
16  TestMod.ccall_captures_local
17  (return %₁₆)

########################################
# ccall argument/return types inside a closure may reference an enclosing
# method's static parameter. Unlike a captured local, its value is unknown at
# (top-level) method definition time, so it can't be spliced; instead it gets
# the `capt-sp` treatment (see `convert_closure_sig_sparams`): a leading type
# parameter of the closure type, re-bound by dispatch as a trailing static
# parameter of the closure method, referenced as `static_parameter` in the
# static_eval positions - which codegen's static evaluator handles natively.
function ccall_sparam_closure(v::Vector{T}) where {T}
    f = () -> ccall(:memset, Ptr{T}, (Ptr{T}, Cint, Csize_t), v, 0, 0)
    f()
end
#---------------------
1   (method TestMod.ccall_sparam_closure)
2   latestworld
3   (call core.svec :T :v)
4   (call core.svec false false)
5   (call core.svec :T)
6   (call JuliaLowering.eval_closure_type TestMod :#ccall_sparam_closure##->###0 %₃ %₄ %₅)
7   latestworld
8   (call core.TypeVar :T)
9   TestMod.#ccall_sparam_closure##->###0
10  (call core.apply_type %₉ %₈)
11  (call core.svec %₁₀)
12  (call core.svec %₈)
13  SourceLocation::2:9
14  (call core.svec %₁₁ %₁₂ %₁₃)
15  --- method core.nothing %₁₄
    slots: [slot₁/#self#(!read)]
    1   TestMod.Ptr
    2   (call core.getfield slot₁/#self# :T)
    3   (call core.apply_type %₁ %₂)
    4   TestMod.Cint
    5   TestMod.Csize_t
    6   (call core.getfield slot₁/#self# :v)
    7   (call top.cconvert %₃ %₆)
    8   (call top.cconvert %₄ 0)
    9   (call top.cconvert %₅ 0)
    10  (call top.unsafe_convert %₃ %₇)
    11  (call top.unsafe_convert %₄ %₈)
    12  (call top.unsafe_convert %₅ %₉)
    13  (foreigncall :memset (static_eval (call core.apply_type TestMod.Ptr static_parameter₁)) (static_eval (call core.svec (call core.apply_type TestMod.Ptr static_parameter₁) TestMod.Cint TestMod.Csize_t)) 0 :ccall %₁₀ %₁₁ %₁₂ %₇ %₈ %₉)
    14  (return %₁₃)
16  latestworld
17  (= slot₁/T (call core.TypeVar :T))
18  TestMod.ccall_sparam_closure
19  (call core.TypeEqOf %₁₈)
20  TestMod.Vector
21  slot₁/T
22  (call core.apply_type %₂₀ %₂₁)
23  (call core.svec %₁₉ %₂₂)
24  slot₁/T
25  (call core.svec %₂₄)
26  SourceLocation::1:10
27  (call core.svec %₂₃ %₂₅ %₂₆)
28  --- method TestMod.ccall_sparam_closure %₂₇
    slots: [slot₁/#self#(!read) slot₂/v slot₃/#->#(single_assign) slot₄/f(single_assign,called)]
    1   TestMod.#ccall_sparam_closure##->###0
    2   static_parameter₁
    3   static_parameter₁
    4   (call core._typeof_captured_variable %₃)
    5   (call core._typeof_captured_variable slot₂/v)
    6   (call core.apply_type %₁ %₂ %₄ %₅)
    7   static_parameter₁
    8   (new %₆ %₇ slot₂/v)
    9   (= slot₃/#-># %₈)
    10  slot₃/#->#
    11  (= slot₄/f %₁₀)
    12  slot₄/f
    13  (call %₁₂)
    14  (return %₁₃)
29  latestworld
30  TestMod.ccall_sparam_closure
31  (return %₃₀)

########################################
# Error: ccall with too few arguments
ccall(:strlen, Csize_t, (Cstring,))
#---------------------
LoweringError:
ccall(:strlen, Csize_t, (Cstring,))
└─────────────────────────────────┘ ── Too few arguments in ccall compared to argument types

########################################
# Error: ccall with too many arguments
ccall(:strlen, Csize_t, (Cstring,), "asdfg", "blah")
#---------------------
LoweringError:
ccall(:strlen, Csize_t, (Cstring,), "asdfg", "blah")
└──────────────────────────────────────────────────┘ ── More arguments than types in ccall

########################################
# Error: ccall varargs with too few args
ccall(:foo, Csize_t, (Cstring...,), "asdfg")
#---------------------
LoweringError:
ccall(:foo, Csize_t, (Cstring...,), "asdfg")
#                     └────────┘ ── C ABI prohibits vararg without one required argument

########################################
# Error: ccall with multiple varargs
ccall(:foo, Csize_t, (Cstring..., Cstring...), "asdfg", "blah")
#---------------------
LoweringError:
ccall(:foo, Csize_t, (Cstring..., Cstring...), "asdfg", "blah")
#                     └────────┘ ── only the trailing ccall argument type should have `...`

########################################
# cglobal special support for (sym, lib) tuple
# unlike flisp we outline the tuple and allow constant propagation to put it
# back before codegen generates code for `cglobal`
cglobal((:sym, lib), Int)
#---------------------
1   TestMod.Int
2   (call core.apply_type top.Ptr %₁)
3   (foreignglobal (foreignsymbol (tuple-p (inert sym) TestMod.lib)))
4   (call top.bitcast %₂ %₃)
5   (return %₄)

########################################
# cglobal - non-tuple expressions in first arg are lowered as normal
cglobal(f(), Int)
#---------------------
1   TestMod.Int
2   (call core.apply_type top.Ptr %₁)
3   TestMod.f
4   (call %₃)
5   (foreignglobal %₄)
6   (call top.bitcast %₂ %₅)
7   (return %₆)

########################################
# Error: cglobal too many arguments
cglobal(:sym, Int, blah)
#---------------------
LoweringError:
cglobal(:sym, Int, blah)
└──────────────────────┘ ── cglobal must have one or two arguments

########################################
# Error: assigning to `cglobal`
cglobal = 10
#---------------------
LoweringError:
cglobal = 10
└─────┘ ── invalid syntax in left-hand side of assignment

########################################
# Error: assigning to `ccall`
ccall = 10
#---------------------
LoweringError:
ccall = 10
└───┘ ── invalid syntax in left-hand side of assignment

########################################
# Error: assigning to `var"ccall"`
var"ccall" = 10
#---------------------
LoweringError:
var"ccall" = 10
#   └───┘ ── invalid syntax in left-hand side of assignment

########################################
# Error: Invalid function name ccall
function ccall()
end
#---------------------
LoweringError:
function ccall()
#        └───┘ ── ccall is a reserved identifier
end

########################################
# Error: Invalid function name ccall
function A.ccall()
end
#---------------------
LoweringError:
function A.ccall()
#          └───┘ ── ccall is a reserved identifier
end

########################################
# Error: Invalid function name ccall
function ccall{<:T}()
end
#---------------------
LoweringError:
function ccall{<:T}()
#        └───┘ ── ccall is a reserved identifier
end

########################################
# Nested splat: simple case
tuple((xs...)...)
#---------------------
1   TestMod.tuple
2   (call core.tuple top.iterate %₁)
3   TestMod.xs
4   (call core._apply_iterate top.iterate core._apply_iterate %₂ %₃)
5   (return %₄)

########################################
# Nested splat: with mixed arguments
tuple(a, (xs...)..., b)
#---------------------
1   TestMod.tuple
2   TestMod.a
3   (call core.tuple %₂)
4   (call core.tuple top.iterate %₁ %₃)
5   TestMod.xs
6   TestMod.b
7   (call core.tuple %₆)
8   (call core.tuple %₇)
9   (call core._apply_iterate top.iterate core._apply_iterate %₄ %₅ %₈)
10  (return %₉)

########################################
# Nested splat: multiple nested splats
tuple((xs...)..., (ys...)...)
#---------------------
1   TestMod.tuple
2   (call core.tuple top.iterate %₁)
3   TestMod.xs
4   TestMod.ys
5   (call core._apply_iterate top.iterate core._apply_iterate %₂ %₃ %₄)
6   (return %₅)

########################################
# Nested splat: triple nesting
tuple(((xs...)...)...)
#---------------------
1   TestMod.tuple
2   (call core.tuple top.iterate %₁)
3   (call core.tuple top.iterate core._apply_iterate %₂)
4   TestMod.xs
5   (call core._apply_iterate top.iterate core._apply_iterate %₃ %₄)
6   (return %₅)

########################################
# Error: Standalone splat expression
(xs...)
#---------------------
LoweringError:
(xs...)
#└───┘ ── unexpected `...`
splatting can only be done into a `call`, `tuple`, `curly`, or array-like expression
