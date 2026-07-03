chain(i) = Symbol(:v, i)
function straight_expr(S)
    stmts = Expr[]
    for i in 1:8
        push!(stmts, :($(chain(i)) = x + $(float(i))))
    end
    for k in 0:S-1
        i = k % 8 + 1
        push!(stmts, :($(chain(i)) = muladd($(chain(i)), 1.0000001, $(float(k % 7)))))
    end
    push!(stmts, :(return $(Expr(:call, :+, (chain(i) for i in 1:8)...))))
    :(function bench_f(x::Float64)
        $(Expr(:block, stmts...))
    end)
end
