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
        elseif fun ∉ (:(+), :(-), :(*), :(//), :inv, :Complex)
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

function preprocess!(expr::Any)
     traversereplacing(expr, [:(sqrt(x::Any)) => :(Complex(>:x)^(1//2)), :(cbrt(x::Any)) => :(Complex(>:x)^(1//3))], Dict())
end

sqrtx(x::Number) = sqrt(complex(x))

function AlgebraicNumber(expr::Expr, pre::Union{Nothing,Number} = nothing)
    expr = preprocess!(expr)
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
        elseif fun ∈ (:(+), :(-), :(*), :(//), :(/), :inv, :Complex)
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
evaluate(::Val{:(Complex)}, args) = AlgebraicNumber(args[1])

const CALL = Val{:call}
const GET = Val{:(::)}
const PUT = Val{:(>:)}

const ANY = Val{:Any}
const NUMBER = Val{:Number}
const SYMBOL = Val{:Symbol}
const EXPR = Val{:Expr}

const Rules = AbstractVector{<:Pair}
const TERMINAL = Union{Symbol,String,Int,UInt,AbstractFloat}

"""
    traversereplacing(what, replacement, context)

Traverse AST what performing list of replacements. Context is a dict to be passed through
"""
traversereplacing(a::TERMINAL, repls::Rules, context) = a
function traversereplacing(s::Symbol, repls::Rules, context)
    matchandbindfirst(s, repls, context)
end
function traversereplacing(expr::Expr, repls::Rules, context)
    mexpr = matchandbindfirst(expr, repls, context)
    mexpr !== expr && return traversereplacing(mexpr, repls, context)
    for i in axes(expr.args, 1)
        expr.args[i] = traversereplacing(expr.args[i], repls, context)
    end
    expr
end

"""
    matchandbindfirst(term, repl, context)

Try all patterns in repl for match with term.
The first matching is used to create a replacement AST for any using the contents of term and
the value part associated with the pattern.
If no match is found, term is returned
"""
function matchandbindfirst(term, repl::Rules, context)
    for (k, v) in repl
        res = matchandbind(term, k, context)
        res && return replacement(v, context)
    end
    return term
end

"""
    matchandbind

Traverse the pattern AST and try to construct replacement for any.
If no match is found, return `false` and discard all changes in context made during
this process.
Certain special terms in patterns `:(x::Any)` accept all types of input and are stored
available for use during generation process, where the term`:( >:x)` stands for the
placeholder.
"""
matchandbind(a::Any, pattern::Any, context) = false
function matchandbind(s::Symbol, pattern::Symbol, context)
    s === pattern
end
function matchandbind(ast::Any, pattern::Expr, context)
    _matchandbind(Val(pattern.head), ast, pattern, context)
end

_matchandbind(::Val, ast, pattern::Expr, context) = false

function _matchandbind(::GET, ast, pattern::Expr, context)
    pargs = pattern.args
    x = pargs[1]
    t = length(pargs) >= 2 ? pargs[2] : :Any
    if acceptable(Val(t), ast)
        bind!(context, x, ast)
        return true
    else
        return false
    end
end
function _matchandbind(::CALL, expr::Expr, pattern::Expr, context)
    pargs = pattern.args
    eargs = expr.args
    if Val{expr.head} <: CALL && length(pargs) == length(eargs)
        for (ea, pa) in zip(eargs, pargs)
            v = matchandbind(ea, pa, context)
            v || return v
        end
        return true
    end
    return false
end

acceptable(::ANY, ::Any) = true
acceptable(::NUMBER, y::Any) = y isa Number
acceptable(::SYMBOL, y::Any) = y isa Symbol
acceptable(::EXPR, y::Any) = y isa Expr

bind!(context::AbstractDict, x, any) = (context[x] = any)

function replacement(value, context)
    value
end
function replacement(rexpr::Expr, context)
    _replacement(Val(rexpr.head), rexpr, context)
end

_replacement(::Val, rexpr, context) = rexpr
function _replacement(::PUT, rexpr, context)
    length(rexpr.args) == 1 || throw_repl_error(rexpr)
    x = first(rexpr.args)
    get(context, x, missing)
end
function _replacement(::CALL, rexpr, context)
    rargs = rexpr.args
    nargs = Vector(undef, length(rargs))
    for i in axes(rargs, 1)
        nargs[i] = replacement(rargs[i], context)
    end
    Expr(rexpr.head, nargs...)
end

@noinline throw_repl_error(x) = throw(ArgumentError("Syntax error in replacement $x"))
