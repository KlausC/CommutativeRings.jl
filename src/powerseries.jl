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

ord(p::PowerSeries) = ord(p.poly)
precision(::Type{<:PowerSeries{R,X,Y}}) where {R,X,Y} = Y
precision(p::PowerSeries) = p.rem.prec

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
    p, rt = splitpoly(PowerSeries{R,X,Y}, p)
    PowerSeries{Y}(p, rt)
end

Base.precision(::Type{<:PowerSeries{R,X,Y}}) where {R,X,Y} = Y

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
    s, rt = splitpoly(P, s)
    rt = combine(rt, combine(tp.rem, tq.rem, p[ord(p)], q[ord(q)]), one(R), one(R))
    P(s, rt)
end
