"""
    rationalconst(expr)

Return the value of a rational constant or a rational function of rational constants
if that can be expressed as `Rational`. Otherwise return `nothing`.
"""
rationalconst(x::Integer) = big(x)
rationalconst(x::AbstractFloat) = isinteger(x) ? Integer(x) : nothing
rationalconst(::Any) = nothing

function rationalconst(expr::Expr)
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        fun = fun == :(/) ? :(//) : fun
        if fun == :(^)
            p = rationalconst(args[2])
            isnothing(p) && return p
            e = rationalconst(args[3])
            isnothing(e) && return e
            en = numerator(e)
            ed = denominator(e)
            ed == 1 && return p^en
            sn = Integer(trunc(numerator(p)^(1 / ed)))
            sd = Integer(trunc(denominator(p)^(1 / ed)))
            q = sn // sd
            return q^ed == p ? q^en : nothing
        elseif fun == :inv
            p = rationalconst(args[2])
            isnothing(p) && return p
            return inv(p)
        elseif fun == :sqrt
            p = rationalconst(args[2])
            isnothing(p) && return p
            sn = isqrt(abs(numerator(p)))
            sd = isqrt(denominator(p))
            q = sn // sd
            return q^2 == p ? q : nothing
        elseif fun == :cbrt
            p = rationalconst(args[2])
            isnothing(p) && return p
            sn = Integer(trunc(cbrt(numerator(p))))
            sd = Integer(trunc(cbrt(denominator(p))))
            q = sn // sd
            return q^3 == p ? q : nothing
        end
        if fun ∉ (:(+), :(-), :(*), :(//))
            return nothing
        end
        n = length(args)
        eargs = similar(args)
        eargs[1] = fun
        for j = 2:n
            earg = rationalconst(args[j])
            isnothing(earg) && return nothing
            eargs[j] = earg
        end
        eval(Expr(head, eargs...))
    else
        nothing
    end
end

"""
    isalgebraic(expr)

Return true iff the expression describes an `AlgebraicNumber`.
"""

const ALLOWED_SYMBOLS = (:im, :φ)

isalgebraic(::AlgebraicNumber) = true
isalgebraic(::Union{Rational,Integer}) = true
isalgebraic(x::AbstractFloat) = isinteger(x)
isalgebraic(s::Symbol) = s ∈ ALLOWED_SYMBOLS
isalgebraic(::Any) = false

function isalgebraic(expr::Expr)
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        fun = fun == :(/) ? :(//) : fun
        if fun == :(^)
            isalgebraic(args[2]) || return false
            q = rationalconst(args[3])
            return !isnothing(q)
        elseif fun ∉ (:(+), :(-), :(*), :(//), :inv, :sqrtx, :cbrt)
            return false
        end
        n = length(args)
        for j = 2:n
            isalgebraic(args[j]) || return false
        end
        return true
    else
        return false
    end
end

replacesqrt!(s::Symbol) = s === :sqrt ? :sqrtx : s
replacesqrt!(a::Any) = a
function replacesqrt!(expr::Expr)
    if expr.head == :call
        args = expr.args
        for i in axes(args, 1)
            args[i] = replacesqrt!(args[i])
        end
    end
    expr
end

sqrtx(x::Number) = sqrt(complex(x))

function AlgebraicNumber(expr::Expr, pre::Union{Nothing,Number} = nothing)
    replacesqrt!(expr)
    approx = pre === nothing ? eval(expr) : float(pre)
    A = AlgebraicNumber(to_algebraic_or_rational(expr))
    r = A.roots
    p = A.minpol
    a, id = closeroot(p, big(fvalue(approx)), r)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end

function to_algebraic_or_rational(expr::Expr)
    x = rationalconst(expr)
    !isnothing(x) && return x
    isalgebraic(expr) || throw(ArgumentError("expression is not an algebraic number"))
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        if fun == :(^)
            a = to_algebraic_or_rational(args[2])
            q = rationalconst(args[3])
            denominator(q) != 1 && (a = AlgebraicNumber(a))
            return a^q
        elseif fun ∈ (:(+), :(-), :(*), :(//), :(/), :inv, :sqrtx, :cbrt)
            n = length(args)
            eargs = Vector{Any}(undef, n - 1)
            for j = 2:n
                eargs[j-1] = to_algebraic_or_rational(args[j])
            end
            return evaluate(Val(fun), eargs)
        end
        throw(ArgumentError("unknown function $fun"))
    else
        throw(ArgumentError("no call, but $head"))
    end
end
to_algebraic_or_rational(a::Number) = a
function to_algebraic_or_rational(s::Symbol)
    s in ALLOWED_SYMBOLS ? AlgebraicNumber(s) : throw(ArgumentError("unexpected symbol $s"))
end

evaluate(::Val{:(+)}, args) = +(args...)
evaluate(::Val{:(-)}, args) = -(args...)
evaluate(::Val{:(*)}, args) = *(args...)
evaluate(::Val{:(/)}, args) = /(args...)
evaluate(::Val{:(//)}, args) = /(args...)
evaluate(::Val{:(inv)}, args) = inv(args...)
evaluate(::Val{:(sqrtx)}, args) = sqrt(AlgebraicNumber(args[1]))
evaluate(::Val{:(cbrt)}, args) = AlgebraicNumber(args[1])^(1 // 3)


"""
    traversereplacing(what, replacement, context)

Traverse AST what performing list of replacements. Context is a dict to be passed through
"""
traversereplacing(a::Any, repls::AbstractDict, context::AbstractDict) = a
function traversereplacing(s::Symbol, repls::AbstractDict, context::AbstractDict)
    matchandbindfirst(s, repls, context)
end
function traversereplacing(expr::Expr, repls::AbstractDict, context::AbstractDict)
    expr = matchandbindfirst(expr, repls, context)
    _traversereplacing(Val(expr.head), expr.args, repls, context)
    expr
end

_traversereplacing(::Val, args, repls, context) = nothing # throw unsupported?
function _traversereplacing(::Val{:call}, args::Vector, repls, context::AbstractDict)
    for i in axes(args, 1)
        args[i] = traversereplacing(args[i], repls, context)
    end
end

function matchandbindfirst(any, repl::AbstractDict, context::AbstractDict)
    for (k, v) in repl
        res = matchandbind(any, k, v, repl, context)
        res !== nothing && return res
    end
    return nothing
end

function matchandbind(a::Any, pattern, value, repl, context)
    a
end
function matchandbind(s::Symbol, pattern, value, repl, context)
    s == pattern ? replacementfor(value, context) : nothing
end
function replacementfor(value, context)
    value
end
function replacementfor(rexpr::Expr, context)
    replacement(Val(rexpr.head), rexpr, context)
end

replacement(::Val, rexpr, context) = rexpr
function replacement(::Val{>:}, rexpr, context)
    length(rexpr.args) == 1 || throw_repl_error(rexpr)
    x = first(rexpr.args)
    get(context, x, missing)
end

@noinline throw_repl_error(x) = throw(ArgumentError("Syntax error in replacement $x"))
