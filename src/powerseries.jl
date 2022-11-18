"""
Power Series (aka Taylor Series) are a generalization of polynomials.
Calculation is restricted to a maximal "precision"(number of terms to be considered).
All further terms are subsumed in a "remainder term".
"""

const InfPrecision = typemax(Int)
struct PowerSeries{R,X,Y} <: Ring{PowerSeriesRingClass{X,R}}
    poly::UnivariatePolynomial{R,X}
    prec::Int
    PowerSeries{R,X,Y}(p, rem) where {R,X,Y} = new{R,X,Y}(p, rem)
    function PowerSeries{Y}(p::P, prec::Integer) where {R,X,P<:UnivariatePolynomial{R,X},Y}
        new{R,X,Y}(p, prec)
    end
end

Base.copy(tp::S) where S<:PowerSeries = S(tp.poly, tp.prec)

ord(p::PowerSeries) = ord(p.poly)
precision(::Type{<:PowerSeries{R,X,Y}}) where {R,X,Y} = Y
basetype(::Type{P}) where {R,X,P<:PowerSeries{R,X}} = UnivariatePolynomial{R,X}

"""
    precision(::Type{<:PowerSeries})
    precision(s::PowerSeries)

Return the maximal relative precision of a power series type.
Return the actual relative precision of a power series object.

The absolute precision of an element is `ord(s) + precision(s)`
"""
precision(p::PowerSeries) = p.prec
convert(::Type{S}, p::S) where S<:PowerSeries = p
convert(::Type{S}, p::P) where {P<:UnivariatePolynomial,S<:PowerSeries} = S(p)
zero(::Type{S}) where {S<:PowerSeries} = S(zero(basetype(S)))
iszero(s::PowerSeries) = iszero(s.poly)
one(::Type{S}) where {S<:PowerSeries} = S(one(basetype(S)))
isunit(tp::PowerSeries) = isunit(tp.poly[0])

function PowerSeries{Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    PowerSeries{R,X,Y}(p)
end
function PowerSeries{R,X,Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    p, rt = splitpoly!(PowerSeries{R,X,Y}, copy(p))
    PowerSeries{Y}(p, rt)
end

function evaluate(p::S, q::UnivariatePolynomial) where S<:PowerSeries
    s, rt = splitpoly!(S, p.poly(q))
    S(s, rt)
end
function evaluate(p::UnivariatePolynomial, tq::S) where S<:PowerSeries
    s, rt = splitpoly!(S, p(tq.poly))
    S(s, rt)
end
evaluate(p::PowerSeries, tq::S) where S = evaluate(p.poly, tq)

(p::PowerSeries)(a, b...) = evaluate(p, a, b...)

function +(p::P, q::P) where {R,P<:PowerSeries{R}}
    s = +(p.poly, q.poly)
    s, rt = splitpoly!(P, s)
    P(s, rt)
end
function -(p::P, q::P) where {R,P<:PowerSeries{R}}
    s = -(p.poly, q.poly)
    s, rt = splitpoly!(P, s)
    P(s, rt)
end
function *(tp::P, tq::P) where {R,P<:PowerSeries{R}}
    p, q = tp.poly, tq.poly
    s = *(p, q)
    s, rt = splitpoly!(P, s)
    rt = min(rt, precision(tp), precision(tq))
    P(s, rt)
end
function /(tp::S, tq::S) where {R,S<:PowerSeries{R}}
    P = basetype(S)
    p, q = tp.poly, tq.poly
    x = monom(typeof(p))
    n = precision(S) + deg(q)
    s = reverse(div(reverse(p) * x^n, reverse(q)))
    s = P(s.coeff, ord(p) - ord(q))
    s, rt = splitpoly!(S, s)
    rt = min(rt, precision(tp), precision(tq))
    S(s, rt)
end

"""
    compose_inv(f::PowerSeries{R}) -> g::PowerSeries

Compute composition inverse `g` of `f`.

Condition: `f(0) == 0` and `f(x) / x` is invertible and ring has `characteristic(R) == 0`.
Use the ["Lagrange inversion formula"](https://en.wikipedia.org/wiki/Formal_power_series#The_Lagrange_inversion_formula).
"""
function compose_inv(tp::S) where {R,X,Y,S<:PowerSeries{R,X,Y}}
    P = basetype(S)
    n = precision(S)
    T = S
    p = tp.poly
    x = monom(P)
    tf = T(tp.poly / x)
    tq = one(T)
    tgk = tq / tf
    g = P(inv(p[1]))
    for k = 2:n
        tgk /= tf
        g += tgk.poly[k-1] * monom(P, k - 1) / R(k)
    end
    T(g * x)
end

function derive(tp::S) where S<:PowerSeries
    p = derive(tp.poly)
    prec = precision(tp)
    prec = prec == InfPrecision ? prec : max(prec - 1, 0)
    S(p, prec)
end

# utility functions

function splitpoly!(::Type{S}, p::UnivariatePolynomial{R}) where {R,S<:PowerSeries{R}}
    prec = precision(S)
    n = length(p.coeff) - 1
    if n <= prec
        rt = InfPrecision
    else
        n = prec + 1
        while iszero(p.coeff[n])
            n -= 1
        end
        resize!(p.coeff, n)
        rt = prec
    end
    p, rt
end
