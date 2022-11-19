"""
Power Series (aka Taylor Series) are a generalization of polynomials.
Calculation is restricted to a maximal "precision"(number of terms to be considered).
All further terms are subsumed in a "remainder term".
"""
const InfPrecision = typemax(Int)
struct PowerSeries{R,X,Y} <: Ring{PowerSeriesRingClass{X,R}}
    poly::UnivariatePolynomial{R,X}
    prec::Int
    PowerSeries{R,X,Y}(p, prec) where {R,X,Y} = new{R,X,Y}(p, prec)
    function PowerSeries{Y}(p::P, prec::Integer) where {R,X,P<:UnivariatePolynomial{R,X},Y}
        new{R,X,Y}(p, prec)
    end
end

function PowerSeries{R,X,Y}(s::PowerSeries{R,X,Z}) where {R,X,Y,Z}
    PowerSeries{Y}(s.poly, s.prec)
end

function O(p::P) where P<:UnivariatePolynomial
    n = deg(p)
    PowerSeries{InfPrecision}(zero(P), n)
end

Base.copy(tp::S) where S<:PowerSeries = S(copy(tp.poly), tp.prec)

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

function PowerSeries{Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    PowerSeries{R,X,Y}(p)
end
function (::Type{S})(p::P) where {R,X,S<:PowerSeries{R,X},P<:UnivariatePolynomial{R,X}}
    p, rt = splitpoly!(copy(p), precision(S), InfPrecision)
    S(p, rt)
end

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

function +(p::S, q::S) where {R,S<:PowerSeries{R}}
    s = +(p.poly, q.poly)
    rt = min(absprecision(p), absprecision(q)) - ord(s)
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end
function -(p::S, q::S) where {R,S<:PowerSeries{R}}
    s = -(p.poly, q.poly)
    rt = min(absprecision(p), absprecision(q)) - ord(s)
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end
function *(tp::S, tq::S) where {R,S<:PowerSeries{R}}
    p, q = tp.poly, tq.poly
    s = *(p, q)
    rt = min(precision(tp), precision(tq))
    s, rt = splitpoly!(s, precision(S), rt)
    S(s, rt)
end
function /(tp::S, tq::S) where {R,S<:PowerSeries{R}}
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
function compose_inv(tp::S) where {R,X,Y,S<:PowerSeries{R,X,Y}}
    P = basetype(S)
    n = precision(S) - 1
    p = tp.poly
    x = monom(P)
    tf = S(tp.poly / x)
    tgk = inv(tf)
    g = P(inv(p[1]))
    for k = 1:n
        tgk /= tf
        g += tgk.poly[k] * monom(P, k) / R(k + 1)
    end
    S(g * x) + O(x^(n+2))
end

function derive(tp::S) where S<:PowerSeries
    p = derive(tp.poly)
    prec = precision(tp)
    prec = prec == InfPrecision ? prec : max(prec - 1, 0)
    S(p, prec)
end

# utility functions

function splitpoly!(p::UnivariatePolynomial{R}, mprec::Integer, prec::Integer) where R
    n = length(p.coeff)
    if prec > mprec && n > mprec
        k = mprec
        n = min(n, prec)
        while k < n && iszero(p.coeff[k+1])
            k += 1
        end
        rt = k < n ? k : prec
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

function promote_rule(
    ::Type{PowerSeries{R,X,Y}},
    ::Type{PowerSeries{R,X,Z}},
) where {R,X,Y,Z}
    PowerSeries{R,X,min(Y, Z)}
end

function Base.show(io::IO, s::PowerSeries{R,X}) where {R,X}
    haso = precision(s) != InfPrecision
    if !iszero(s.poly) || !haso
        Base.show(io, s.poly, Val(false))
        if haso
            print(io, " + ")
        end
    end
    if haso
        n = precision(s) + ord(s)
        print(io, n == 1 ? "O(x)" : "O($X^$n)")
    end
end
