"""
Power Series (aka Taylor Series) are a generalization of polynomials.
Calculation is restricted to a maximal "precision"(number of terms to be considered).
All further terms are subsumed in a "remainder term".
"""
const InfPrecision = typemax(Int)
struct PowerSeries{Y,R,X} <: Ring{PowerSeriesRingClass{X,R}}
    poly::UnivariatePolynomial{R,X}
    prec::Int
    PowerSeries{Y,R,X}(p, prec) where {Y,R,X} = new{Y,R,X}(p, prec)
    function PowerSeries{Y}(p::P, prec::Integer) where {R,X,P<:UnivariatePolynomial{R,X},Y}
        new{Y,R,X}(p, prec)
    end
end

function PowerSeries{Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    PowerSeries{Y,R,X}(p)
end
function (::Type{S})(p::P) where {Y,R,X,S<:PowerSeries{Y,R,X},P<:UnivariatePolynomial{R,X}}
    p, rt = splitpoly!(copy(p), precision(S), InfPrecision)
    S(p, rt)
end
function PowerSeries{Y,R,X}(s::PowerSeries{Z,R,X}) where {R,X,Y,Z}
    PowerSeries{Y}(s.poly, s.prec)
end

# enable `R[[:x],n]` as a convenience constructor for power series
function getindex(R::Type{<:Ring}, X::AbstractVector{Symbol}, n::Integer)
    length(X) == 1 && n >= 0 || throw(ArgumentError("invalid power series constructor"))
    PowerSeries{n,R,X[1]}
end

# accessing coefficients
getindex(s::PowerSeries, n) = getindex(s.poly, n)

O(p::P) where P<:UnivariatePolynomial = PowerSeries{-1}(zero(P), deg(p))
O(s::S) where S<:PowerSeries = S(zero(basetype(s)), deg(s))

Base.copy(tp::S) where S<:PowerSeries = S(copy(tp.poly), tp.prec)

ord(s::PowerSeries) = ord(s.poly)
deg(s::PowerSeries) = deg(s.poly)
precision(::Type{<:PowerSeries{Y,R,X}}) where {Y,R,X} = Y
basetype(::Type{P}) where {Y,R,X,P<:PowerSeries{Y,R,X}} = UnivariatePolynomial{R,X}

"""
    precision(::Type{<:PowerSeries})
    precision(s::PowerSeries)

Return the maximal relative precision of a power series type.
Return the actual relative precision of a power series object.

The absolute precision of an element is `ord(s) + precision(s)`
"""
precision(p::PowerSeries) = p.prec

"""
    absprecision(s::PowerSeries)

Return absolute precision of a power series element.

Essentially: `ord(s) + precision(s)`
"""
function absprecision(p::PowerSeries)
    pr = precision(p)
    pr == InfPrecision ? InfPrecision : ord(p) + pr
end

convert(::Type{S}, p::S) where S<:PowerSeries = p
convert(::Type{S}, p::P) where {P<:UnivariatePolynomial,S<:PowerSeries} = S(p)
zero(::Type{S}) where {S<:PowerSeries} = S(zero(basetype(S)))
iszero(s::PowerSeries) = iszero(s.poly)
one(::Type{S}) where {S<:PowerSeries} = S(one(basetype(S)))
isunit(s::PowerSeries) = !iszero(s)
==(s::S, t::S) where S<:PowerSeries = s.poly == t.poly

monom(::Type{P}, a...) where P<:PowerSeries = P(monom(basetype(P), a...))

function evaluate(p::S, q::UnivariatePolynomial) where S<:PowerSeries
    s, rt = splitpoly!(p.poly(q), precision(S), precision(p))
    S(s, rt)
end
function evaluate(p::UnivariatePolynomial, tq::S) where S<:PowerSeries
    s, rt = splitpoly!(p(tq.poly), precision(S), precision(tq))
    S(s, rt)
end
evaluate(p::PowerSeries, tq::S) where S = evaluate(p.poly, tq)

(p::PowerSeries)(a, b...) = evaluate(p, a, b...)

+(p::PowerSeries) = p
-(p::S) where S<:PowerSeries = S(-p.poly, p.prec)

function +(p::S, q::S) where {S<:PowerSeries}
    s = +(p.poly, q.poly)
    rt = pdiff(min(absprecision(p), absprecision(q)), ord(s))
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end
function -(p::S, q::S) where {S<:PowerSeries}
    s = -(p.poly, q.poly)
    rt = min(absprecision(p), absprecision(q)) - ord(s)
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end
function *(tp::S, tq::S) where {S<:PowerSeries}
    p, q = tp.poly, tq.poly
    pp, pq = precision(tp), precision(tq)
    izp, izq = iszero(p), iszero(q)
    if izp || izq
        rt = if izp && izq
            psum(pp, pq)
        elseif izp
            pp + ord(q)
        else
            pq + ord(p)
        end
        return S(zero(basetype(S)), rt)
    end
    ps = precision(S)
    pr = psum(precision(S), 10)
    s = multiply(p, q, pr)
    rt = min(length(p.coeff) + length(q.coeff) - 2, pr)
    rt = rt < ps ? InfPrecision : rt
    rt = min(pp, pq, rt)
    s, rt = splitpoly!(s, ps, rt)
    S(s, rt)
end
function /(tp::S, tq::S) where {S<:PowerSeries}
    P = basetype(S)
    p, q = tp.poly, tq.poly
    if iszero(p) && isunit(tq)
        return S(p, precision(tp) + ord(tp) - ord(tq))
    end
    x = monom(typeof(p))
    n = precision(S) + deg(q) + 2
    s = reverse(div(reverse(p) * x^n, reverse(q)))
    s = P(s.coeff, ord(p) - ord(q))
    rt = min(precision(tp), precision(tq))
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end

"""
    compose_inv(f::PowerSeries{R}) -> g::PowerSeries

Compute composition inverse `g` of `f`.

Condition: `f(0) == 0` and `f(x) / x` is invertible and ring has `characteristic(R) == 0`.
Use the ["Lagrange inversion formula"](https://en.wikipedia.org/wiki/Formal_power_series#The_Lagrange_inversion_formula).
"""
function compose_inv(tp::S) where {R,X,Y,S<:PowerSeries{Y,R,X}}
    P = basetype(S)
    n = precision(S) - 1
    p = tp.poly
    x = monom(P)
    tf = inv(S(tp.poly / x)).poly
    tgk = tf
    g = tf[0]
    for k = 1:n
        tgk = multiply(tgk, tf, n + 1)
        g += (tgk[k] / R(k + 1)) * monom(P, k)
    end
    S(g * x) + O(monom(P, n + 2))
end

function derive(tp::S) where S<:PowerSeries
    p = derive(tp.poly)
    prec = precision(tp)
    prec = prec == InfPrecision ? prec : max(prec - 1, 0)
    S(p, prec)
end

adjoint(p::PowerSeries) = derive(p)

# utility functions

function splitpoly!(p::UnivariatePolynomial{R}, mprec::Integer, prec::Integer) where R
    n = length(p.coeff)
    if mprec <= 0
        if n > 0
            throw(ArgumentError("cannot convert to PowerSeries without known precision"))
        else
            return p, prec
        end
    end
    if prec > mprec && n > mprec
        k = mprec
        n = min(n, prec)
        while k < n && iszero(p.coeff[k+1])
            k += 1
        end
        rt = k
    else
        rt = prec
    end
    n = min(mprec, prec, n)
    while n >= 1 && iszero(p.coeff[n])
        n -= 1
    end
    if n <= 0
        rt += ord(p)
        p = zero(p)
    else
        resize!(p.coeff, n)
    end
    p, rt
end

function psum(pp::Int, pq::Int)
    ps = pp + pq
    ifelse(ps < 0, InfPrecision, ps)
end

function pdiff(pp::Int, pq::Int)
    ifelse(pp == InfPrecision, pp, pp - pq)
end

function promote_rule(
    ::Type{PowerSeries{Y,R,X}},
    ::Type{PowerSeries{Z,R,X}},
) where {R,X,Y,Z}
    M = max(Y, Z)
    PowerSeries{M,R,X}
end

function Base.show(io::IO, s::PowerSeries{Y,R,X}) where {Y,R,X}
    haso = precision(s) != InfPrecision
    if !iszero(s.poly) || !haso
        _show(io, s.poly, Val(false))
        if haso
            print(io, " + ")
        end
    end
    if haso
        n = precision(s) + ord(s)
        print(io, n == 1 ? "O(x)" : "O($X^$n)")
    end
end
