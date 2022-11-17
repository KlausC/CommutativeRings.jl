"""
Power Series (aka Taylor Series) are a generalization of polynomials.
Calculation is restricted to a maximal "precision"(number of terms to be considered).
All further terms are subsumed in a "remainder term".
"""

const InfPrecision = typemax(Int)
struct RemTerm{R}
    prec::Int
    mult::R
    hash::UInt
    function RemTerm(prec::Integer, mult::R, hash::Integer) where R
        if iszero(mult)
            prec = InfPrecision
            hash = 0x0
        end
        new{R}(prec, mult, hash)
    end
end
struct PowerSeries{R,X,Y} <: Ring{PowerSeriesRingClass{X,R}}
    poly::UnivariatePolynomial{R,X}
    rem::RemTerm{R}
    PowerSeries{R,X,Y}(p, rem) where {R,X,Y} = new{R,X,Y}(p, rem)
    function PowerSeries{Y}(p::P, rem::RemTerm) where {R,X,P<:UnivariatePolynomial{R,X},Y}
        new{R,X,Y}(p, rem)
    end
end

Base.zero(::Type{<:RemTerm{R}}) where R = RemTerm(InfPrecision, zero(R), 0x0)
Base.iszero(rt::RemTerm) = iszero(rt.mult)
Base.copy(tp::S) where S<:PowerSeries = S(tp.poly, tp.rem)

ord(p::PowerSeries) = ord(p.poly)
precision(::Type{<:PowerSeries{R,X,Y}}) where {R,X,Y} = Y
basetype(::Type{P}) where {R,X,P<:PowerSeries{R,X}} = UnivariatePolynomial{R,X}

precision(p::PowerSeries) = p.rem.prec
convert(::Type{S}, p::S) where S<:PowerSeries = p
convert(::Type{S}, p::P) where {P<:UnivariatePolynomial,S<:PowerSeries} = S(p)
zero(::Type{S}) where {S<:PowerSeries} = S(zero(basetype(S)))
iszero(s::PowerSeries) = iszero(s.poly)
one(::Type{S}) where {S<:PowerSeries} = S(one(basetype(S)))
isunit(tp::PowerSeries) = isunit(tp.poly[0])

function splitpoly(::Type{<:PowerSeries{R,X,Y}}, p::UnivariatePolynomial{R,X}) where {R,X,Y}
    prec = Y
    n = length(p.coeff) - 1
    if n <= prec
        rt = zero(RemTerm{R})
    else
        p = copy(p)
        resize!(p.coeff, prec+1)
        rt = RemTerm(prec, one(R), hash(p))
    end
    p, rt
end

function combine(a::RT, b::RT, A::R, B::R) where {R,RT<:RemTerm{R}}
    if iszero(a)
        b
    elseif iszero(b)
        a
    elseif a.prec == b.prec && a.hash == b.hash
            RemTerm(a.prec, a.mult * A + b.mult * B, a.hash)
    else
        RemTerm(min(a.prec, b.prec), one(R), a.hash + b.hash)
    end
end

function PowerSeries{Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    PowerSeries{R,X,Y}(p)
end
function PowerSeries{R,X,Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    p, rt = splitpoly(PowerSeries{R,X,Y}, p)
    PowerSeries{Y}(p, rt)
end

Base.precision(::Type{<:PowerSeries{R,X,Y}}) where {R,X,Y} = Y

function evaluate(p::S, q::UnivariatePolynomial) where S<:PowerSeries
    s, rt = splitpoly(S, p.poly(q))
    S(s + 0, rt)
end
function evaluate(p::UnivariatePolynomial, tq::S) where S<:PowerSeries
    s, rt = splitpoly(S, p(tq.poly))
    S(s + 0, rt)
end
evaluate(p::PowerSeries, tq::S) where S = evaluate(p.poly, tq)

(p::PowerSeries)(a, b...) = evaluate(p, a, b...)

function +(p::P, q::P) where {R,P<:PowerSeries{R}}
    s = +(p.poly, q.poly)
    s, rt = splitpoly(P, s)
    rt = combine(p.rem, q.rem, one(R), one(R))
    P(s, rt)
end
function -(p::P, q::P) where {R,P<:PowerSeries{R}}
    s = -(p.poly, q.poly)
    s, rt = splitpoly(P, s)
    rt = combine(p.rem, q.rem, one(R), -one(R))
    P(s, rt)
end
function *(tp::P, tq::P) where {R,P<:PowerSeries{R}}
    p, q = tp.poly, tq.poly
    s = *(p, q)
    s, rt = splitpoly(P, s)
    rt = combine(rt, combine(tp.rem, tq.rem, p[ord(p)], q[ord(q)]), one(R), one(R))
    P(s + 0, rt)
end
function /(tp::P, tq::P) where {R,P<:PowerSeries{R}}
    p, q = tp.poly, tq.poly
    x = monom(typeof(p))
    n = precision(P) + deg(q)
    s = reverse(div(reverse(p) * x^n, reverse(q)))
    s = s / x^ord(s)
    s, rt = splitpoly(P, s)
    rt = combine(rt, combine(tp.rem, tq.rem, p[ord(p)], q[ord(q)]), one(R), one(R))
    P(s, rt)
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
    for k in 2:n
        tgk /= tf
        g += tgk.poly[k-1] * monom(P, k-1) / R(k)
    end
    T(g * x)
end

function derive(tp::S) where S<:PowerSeries
    p = derive(tp.poly)
    rt = tp.rem
    prec = rt.prec == InfPrecision ? rt.prec : rt.prec - 1
    rta = RemTerm(prec, rt.mult, hash(p))
    S(p, rta)
end
