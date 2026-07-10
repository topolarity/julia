# Branching

test_mod = Module()

#-------------------------------------------------------------------------------
@testset "Tail position" begin

@test JuliaLowering.include_string(test_mod, """
let a = true
    if a
        1
    end
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    if a
        1
    end
end
""") === nothing

@test JuliaLowering.include_string(test_mod, """
let a = true
    if a
        1
    else
        2
    end
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    if a
        1
    else
        2
    end
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = true
    if a
        1
    elseif b
        2
    else
        3
    end
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = false
    if a
        1
    elseif b
        2
    else
        3
    end
end
""") === 3

end

#-------------------------------------------------------------------------------
@testset "Value required but not tail position" begin

@test JuliaLowering.include_string(test_mod, """
let a = true
    x = if a
        1
    end
    x
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    x = if a
        1
    end
    x
end
""") === nothing

@test JuliaLowering.include_string(test_mod, """
let a = true
    x = if a
        1
    else
        2
    end
    x
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    x = if a
        1
    else
        2
    end
    x
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = true
    x = if a
        1
    elseif b
        2
    else
        3
    end
    x
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = false
    x = if a
        1
    elseif b
        2
    else
        3
    end
    x
end
""") === 3

end

#-------------------------------------------------------------------------------
@testset "Side effects (not value or tail position)" begin

@test JuliaLowering.include_string(test_mod, """
let a = true
    x = nothing
    if a
        x = 1
    end
    x
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    x = nothing
    if a
        x = 1
    end
    x
end
""") === nothing

@test JuliaLowering.include_string(test_mod, """
let a = true
    x = nothing
    if a
        x = 1
    else
        x = 2
    end
    x
end
""") === 1

@test JuliaLowering.include_string(test_mod, """
let a = false
    x = nothing
    if a
        x = 1
    else
        x = 2
    end
    x
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = true
    x = nothing
    if a
        x = 1
    elseif b
        x = 2
    else
        x = 3
    end
    x
end
""") === 2

@test JuliaLowering.include_string(test_mod, """
let a = false, b = false
    x = nothing
    if a
        x = 1
    elseif b
        x = 2
    else
        x = 3
    end
    x
end
""") === 3

end
#-------------------------------------------------------------------------------
# Block condition
@test JuliaLowering.include_string(test_mod, """
let a = true
    if begin; x = 2; a; end
        x
    end
end
""") === 2

#-------------------------------------------------------------------------------
@testset "`&&` and `||` chains" begin

# 0-1 arguments
@test jl_eval(test_mod, Expr(:&&)) == true
@test jl_eval(test_mod, Expr(:&&, true)) == true
@test jl_eval(test_mod, Expr(:&&, false)) == false
@test jl_eval(test_mod, Expr(:||)) == false
@test jl_eval(test_mod, Expr(:||, true)) == true
@test jl_eval(test_mod, Expr(:||, false)) == false

@test JuliaLowering.include_string(test_mod, """
true && "hi"
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
true && true && "hi"
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
false && "hi"
""") == false

@test JuliaLowering.include_string(test_mod, """
true && false && "hi"
""") == false

@test JuliaLowering.include_string(test_mod, """
begin
    z = true && "hi"
    z
end
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
begin
    z = false && "hi"
    z
end
""") == false


@test JuliaLowering.include_string(test_mod, """
true || "hi"
""") == true

@test JuliaLowering.include_string(test_mod, """
true || true || "hi"
""") == true

@test JuliaLowering.include_string(test_mod, """
false || "hi"
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
false || true || "hi"
""") == true

@test JuliaLowering.include_string(test_mod, """
false || false || "hi"
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
begin
    z = false || "hi"
    z
end
""") == "hi"

@test JuliaLowering.include_string(test_mod, """
begin
    z = true || "hi"
    z
end
""") == true

# 0-1 arguments in condition position (`expand_condition`, used by `if`/`while`)
# have their own desugaring path separate from the value-position case above.
# From PkgEval: JSON v1.6.1, via StructUtils src/StructUtils.jl:1188 (@generated makestruct emits 1-arg Expr(:&&))
@test jl_eval(test_mod, Expr(:if, Expr(:&&), 1, 2)) == 1
@test jl_eval(test_mod, Expr(:if, Expr(:&&, true), 1, 2)) == 1
@test jl_eval(test_mod, Expr(:if, Expr(:&&, false), 1, 2)) == 2
@test jl_eval(test_mod, Expr(:if, Expr(:||), 1, 2)) == 2
@test jl_eval(test_mod, Expr(:if, Expr(:||, true), 1, 2)) == 1
@test jl_eval(test_mod, Expr(:if, Expr(:||, false), 1, 2)) == 2

# Same, but with the condition inside a block (the `isblock` branch of
# `expand_condition`)
@test jl_eval(test_mod, Expr(:if, Expr(:block, Expr(:&&, true)), 1, 2)) == 1
@test jl_eval(test_mod, Expr(:if, Expr(:block, Expr(:||, false)), 1, 2)) == 2
@test jl_eval(test_mod, Expr(:if, Expr(:block, Expr(:&&)), 1, 2)) == 1

# Degenerate arities nested inside another `&&`/`||` (flattened away by
# `expand_cond_children`)
@test jl_eval(test_mod, Expr(:if, Expr(:&&, Expr(:&&)), 1, 2)) == 1
@test jl_eval(test_mod, Expr(:if, Expr(:&&, Expr(:&&, false), true), 1, 2)) == 2

# `while` conditions share `expand_condition` with `if`
@test jl_eval(test_mod, Expr(:while, Expr(:||), 1)) === nothing
@test jl_eval(test_mod, Expr(:while, Expr(:&&), Expr(:break))) === nothing

end

#-------------------------------------------------------------------------------
@testset "diverging (`return`) condition terms" begin
    # From PkgEval: PSSFSS v1.13.1, src/structuredtri.jl:632 (a && b && return true as if/elseif test); also PEtab

# A `&&`/`||` chain used directly as an `if`/`elseif` test may contain a
# `return` as a (flattened) operand, eg PSSFSS's `a && b && return true` used as
# a bare `elseif` test with an empty body. The `return` term compiles to a
# divergence (no reachable value); `compile_conditional` must skip the gate for
# it rather than crash. All expected values below are the flisp lowering's.

# Trailing `return` in a `&&` test with an empty `elseif` body (the MWE)
fa = JuliaLowering.include_string(test_mod, """
function (x, y)
    if y == 1
        return 10
    elseif y == 2 && x == 2 && return 20
    elseif y == 3
        return 30
    end
    return 99
end
""")
@test fa(2, 1) === 10   # first branch
@test fa(2, 2) === 20   # `&&` chain reaches the `return`
@test fa(3, 2) === 99   # `x == 2` false -> chain false -> fall through
@test fa(2, 3) === 30   # later branch still reachable
@test fa(0, 0) === 99

# Trailing `return` in a `||` test
fd = JuliaLowering.include_string(test_mod, """
function (x, y)
    if y == 1
        return 10
    elseif x == 2 || return 20
    elseif y == 3
        return 30
    end
    return 99
end
""")
@test fd(2, 1) === 10
@test fd(0, 2) === 20   # `x == 2` false -> `return 20`
@test fd(2, 2) === 99   # `x == 2` true -> empty body -> fall through
@test fd(0, 3) === 20   # reached before the `y == 3` branch

# `return` in a non-final position of the flattened chain (via parens): the
# terms after it are unreachable and must be dropped.
fh = JuliaLowering.include_string(test_mod, """
function (a, b)
    if (a && return 20) && b
        return 111
    end
    return 99
end
""")
@test fh(true, false) === 20    # `a` true -> `return 20`; `b` never evaluated
@test fh(false, true) === 99    # `a` false -> chain false -> skip body

# `||` with a non-final diverging term
fj = JuliaLowering.include_string(test_mod, """
function (a, b)
    if (a || return 20) || b
        return 111
    end
    return 99
end
""")
@test fj(true, false) === 111   # `a` true -> short circuit -> body
@test fj(false, true) === 20    # `a` false -> `return 20`; `b` unreachable

# The body of an `if` whose test always diverges when true is unreachable.
fb = JuliaLowering.include_string(test_mod, """
function (x, y)
    if y == 2 && x == 2 && return 20
        return 111
    end
    return 99
end
""")
@test fb(2, 2) === 20
@test fb(3, 2) === 99
@test fb(2, 3) === 99

# Diverging test of a ternary (`?:` lowers to `if`)
ff = JuliaLowering.include_string(test_mod, """
function (a, y, z)
    (a && return 20) ? y : z
end
""")
@test ff(true, 1, 2) === 20     # diverges before the ternary result
@test ff(false, 1, 2) === 2     # chain false -> select `z`

# `return` as a `&&` term in *value* position (already handled via the
# `if`-desugaring path) must keep working.
fg = JuliaLowering.include_string(test_mod, """
function (a)
    x = a && return 1
    x
end
""")
@test fg(true) === 1
@test fg(false) === false

end

@testset "symbolic goto/label" begin

JuliaLowering.include_string(test_mod, """
let
    a = []
    i = 1
    @label foo
    push!(a, i)
    i = i + 1
    if i <= 2
        @goto foo
    end
    a
end
""") == [1,2]

end
