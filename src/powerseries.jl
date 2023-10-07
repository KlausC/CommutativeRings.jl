
const InfPrecision = typemax(Int)

function PowerSeries{Y}(p::P) where {R,X,P<:UnivariatePolynomial{R,X},Y}
    PowerSeries{Y,R,X}(p)
end
function (::Type{S})(p::P) where {Y,R,X,S<:PowerSeries{Y,R,X},P<:UnivariatePolynomial{R,X}}
    p, rt = ps_from_poly!(copy(p), precision(S), InfPrecision)
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
function ==(s::S, t::S) where S<:PowerSeries
    precision(s) == precision(t) == InfPrecision && s.poly == t.poly
end
isapprox(s::PowerSeries, t::PowerSeries) = s.poly == t.poly
function isapprox(s::P, r::R) where {P<:PowerSeries,R<:Union{RingInt,Rational}}
    B = basetype(P)
    promote_type(B, R) == B && B(r) == s.poly
end
isapprox(r::R, s::P) where {P<:PowerSeries,R<:Union{RingInt,Rational}} = isapprox(s, r)

monom(::Type{P}, a...) where P<:PowerSeries = P(monom(basetype(P), a...))
CC(s::PowerSeries) = CC(s.poly)

function evaluate(p::S, q::UnivariatePolynomial) where S<:PowerSeries
    s, rt = ps_from_poly!(p.poly(q), precision(S), precision(p))
    S(s, rt)
end
function evaluate(p::UnivariatePolynomial, tq::S) where S<:PowerSeries
    s, rt = ps_from_poly!(p(tq.poly), precision(S), precision(tq))
    S(s, rt)
end
function evaluate(p::PowerSeries, tq::S) where S
    r = evaluate(p.poly, tq)
    if r isa PowerSeries && precision(r) == InfPrecision
        r = typeof(r)(r.poly, min(precision(p), precision(tq)))
    end
    r
end

(p::PowerSeries)(a, b...) = evaluate(p, a, b...)

+(p::PowerSeries) = p
-(p::S) where S<:PowerSeries = S(-p.poly, p.prec)

function +(p::S, q::S) where {S<:PowerSeries}
    s = +(p.poly, q.poly)
    rt = pdiff(min(absprecision(p), absprecision(q)), ord(s))
    s, rt = ps_from_poly!(s, precision(S), rt)
    S(s, rt)
end
function -(p::S, q::S) where {S<:PowerSeries}
    s = -(p.poly, q.poly)
    rt = pdiff(min(absprecision(p), absprecision(q)), ord(s))
    s, rt = ps_from_poly!(s, precision(S), rt)
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
            psum(pp, ord(q))
        else
            psum(pq, ord(p))
        end
        return S(zero(basetype(S)), rt)
    end
    ps = precision(S)
    pr = psum(precision(S), 10)
    s = multiply(p, q, pr)
    rt = min(length(p.coeff) + length(q.coeff) - 2, pr)
    rt = rt < ps ? InfPrecision : rt
    rt = min(pp, pq, rt)
    s, rt = ps_from_poly!(s, ps, rt)
    S(s, rt)
end
function /(tp::S, tq::S) where {S<:PowerSeries}
    P = basetype(S)
    R = basetype(P)
    p, q = tp.poly, tq.poly
    if iszero(p) && isunit(tq)
        return S(p, pdiff(precision(tp), -ord(tp) + ord(tq)))
    end
    b = p.coeff
    a = q.coeff
    na = length(a)
    nb = length(b)
    a0 = inv(q[ord(q)])
    m = precision(S)
    c = Vector{R}(undef, m)
    for n = 0:m-1
        s = n < nb ? b[n+1] : zero(R)
        for k ∈ 1:min(n, na - 1)
            s -= a[k+1] * c[n-k+1]
        end
        c[n+1] = s * a0
    end
    pr = min(precision(tp), precision(tq))
    if !iszero(view(c, max(1, m - na + 1):m))
        pr = min(pr, m)
    end
    rt = ord(p) - ord(q)
    return S(P(c, rt), pr)
end

"""
    sqrt(s::PowerSeries)

For power series `s` with constant term `1` calculate the
powerseries `p` with `p^2 == s` and constant term `1`.
"""
function Base.sqrt(s::S) where {Y,R,X,S<:PowerSeries{Y,R,X}}
    iszero(s) && return s
    P = basetype(S)
    if isodd(ord(s)) || !isone(s[ord(s)])
        throw(ArgumentError("sqrt of power series requires first even term of `1`"))
    end
    sqe = one(R)
    c = s.poly.coeff
    n = length(c)
    m = precision(S)
    a = Vector{R}(undef, m)
    a[1] = sqe
    kmax = 0
    for k = 1:m-1
        t = k < n ? c[k+1] : zero(R)
        if iseven(k)
            t -= a[k÷2+1]^2
        end
        t /= 2
        for i = 1:(k-1)÷2
            t -= a[i+1] * a[k-i+1]
        end
        if !iszero(t)
            kmax = k
        end
        a[k+1] = t
    end
    ps = precision(s)
    pr = kmax <= m ÷ 2 ? ps : min(m, ps)
    S(P(a, ord(s) ÷ 2), pr)
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
pade(p::PowerSeries, a...) = pade(p.poly, a...)

# utility functions

function ps_from_poly!(p::UnivariatePolynomial{R}, mprec::Integer, prec::Integer) where R
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
