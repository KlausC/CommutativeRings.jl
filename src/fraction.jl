
# class constructors
Frac(::Type{R}) where R<:Ring = Frac{R}
Frac(::Type{R}) where R<:Integer = QQ{R}

# construction
category_trait(Z::Type{<:Frac}) = category_trait_fraction(category_trait(basetype(Z)))
basetype(::Type{<:Frac{T}}) where T = T
depth(::Type{<:Frac{T}}) where T = depth(T) + 1
copy(a::Frac) = typeof(a)(a.num,a.den, NOCHECK)

numerator(a::FractionRing) = a.num
denominator(a::FractionRing) = a.den
deg(a::Frac{<:Polynomial}) = (deg(a.num), deg(a.den))

issimpler(a::T, b::T) where T<:Frac = issimpler(a.num, b.num)

Frac{T}(a::Frac{T}) where T = a
Frac{T}(a::Frac{S}) where {T,S} = Frac{T}(T(a.num), T(a.den), NOCHECK)

Frac{T}(a::Integer) where T = Frac{T}(T(a), one(T), NOCHECK)
Frac{T}(a::Base.Rational) where T = Frac{T}(T(a.num), T(a.den), NOCHECK)
Frac{T}(a::Ring) where T = Frac{T}(T(a), one(T), NOCHECK)
Frac(a::T) where T<:Ring  = Frac{T}(a)
Frac(a::T) where T<:Integer = Frac{ZZ{T}}(a)
Frac(a::Rational{T}) where T<:Integer = Frac{ZZ{T}}(a)
Frac{T}(a::Integer,b::Integer) where T = Frac(T(a), T(b))
function Frac(a::T, b::T) where T<:Polynomial
    cab = content(a) // content(b)
    a = primpart(a)
    b = primpart(b)
    g = pgcd(a, b)
    a /= g
    b /= g
    a *= numerator(cab)
    b *= denominator(cab)
    g = pgcd(a, b)
    a /= g
    b /= g
    s = lcunit(b)
    b /= s
    a /= s
    Frac{T}(a, b, NOCHECK)
end
function Frac(a::T, b::T) where T<:ZZ
    g = pgcd(a, b)
    a /= g
    b /= g
    s = lcunit(b)
    b /= s
    a /= s
    Frac{T}(a, b, NOCHECK)
end
//(a::T, b::T) where T<:QQ = a / b
//(a::T, b::T) where T<:Ring = Frac(a, b)
//(a::T, b::T) where T<:FractionRing = (a.num * b.den) // (b.num * a.den)
Frac{T}(a, b) where T = Frac(T(a), T(b))

_promote_rule(::Type{Frac{T}}, ::Type{Frac{S}}) where {S,T} = Frac{promote_type(S,T)}
_promote_rule(::Type{Frac{T}}, ::Type{S}) where {S<:Ring,T} = Frac{promote_type(S,T)}
promote_rule(::Type{Frac{T}}, ::Type{S}) where {S<:Integer,T} = Frac{promote_type(S,T)}
promote_rule(::Type{Frac{T}}, ::Type{Rational{S}}) where {S<:Integer,T} = Frac{promote_type(S,T)}

lcunit(a::Frac) = inv(lcunit(a.den))

# induced homomorphism
function (h::Hom{F,R,S})(a::Frac{<:R}) where {F,R,S}
    Frac(h.f(a.num), h.f(a.den))
end

import Base: isless
isless(p::T, q::T) where T<:Frac = isless(p.num * q.den, q.num * p.den)

# operations for Frac

function +(x::T, y::T) where T<:Frac
    a, b, c, d = x.num, x.den, y.num, y.den
    h = pgcd(b, d)
    b /= h
    d /= h
    n = a * d + b * c
    g = pgcd(n, h)
    T(n / g, h / g * b * d)
end

function *(x::T, y::T) where T<:Frac
    a, b, c, d = x.num, x.den, y.num, y.den
    g = pgcd(a, d)
    a /= g
    d /= g
    g = pgcd(b, c)
    b /= g
    c /= g
    T(a * c, b * d, NOCHECK)
end
function inv(x::T) where T<:Frac
    T(x.den, x.num, NOCHECK)
end

==(a::T, b::T) where T<:Frac = iszero(a - b)
/(a::T, b::T) where T<:Frac = a * inv(b)
-(a::T, b::T) where T<:Frac = +(a, -b)
-(a::Frac{T}) where T = Frac{T}(-a.num, a.den, NOCHECK)
divrem(a::T, b::T) where T<:Frac = (a / b, zero(T))
div(a::T, b::T) where T<:Frac = a / b
rem(a::T, b::T) where T<:Frac = zero(T)

isunit(a::Frac) = !iszero(a.num)
isone(a::Frac) = a.num == a.den
iszero(a::Frac) = iszero(a.num)
zero(::Type{Frac{T}}) where T = Frac(zero(T), one(T))
one(::Type{Frac{T}}) where T = Frac(one(T), one(T))
hash(a::Frac, h::UInt) = hash(a.den, hash(a.num, h))

evaluate(p::Frac, a) = evaluate(p.num, a) // evaluate(p.den, a)
(p::Frac)(a, b...) = evaluate(p, a, b...)

derive(p::Frac) = (derive(p.num) * p.den - p.num * derive(p.den)) // p.den // p.den
function derive(p::Ring, n::Integer)
    n < 0 && throw(ArgumentError("degree of derivative must not be negative"))
    n == 0 ? p : derive(derive(p, n-1))
end

Base.getindex(s::Series{T}, i::Integer) where T = T(s.f(i))
deg(::Series) = typemax(Int)
basetype(::Type{<:Series{T}}) where T = T
varname(::Type{<:Series}) = :x

"""
    pade(m, n, p)

Calculate Padé approximation of order `n / m` for polynomial or series `p`.

If `deg(p)` is greater than `m + n`, the higher terms of `p` are ignored.

The Padé approximant is a rational function `R(x) = P(x) / Q(x)` with polynomials
with `deg(P) ≤ m`, `deg(Q) ≤ n` and `Q(0) = 1`.

It is defined by the coincidence of the derivatives of `p` and `R` of degrees less than or equal `m + n` at `0`.
"""
function pade(s::S, m::Integer, n::Integer) where S<:Union{UnivariatePolynomial,Series}
    (m >= 0 && n >= 0) || throw(ArgumentError("numerator and denumerator degrees must not be negative ($m, $n)"))
    P = UnivariatePolynomial{basetype(S),varname(S)}
    p = P([s[i] for i in 0:m+n])
    d = m + n + 1
    r0 = monom(P, d)
    r1 = p
    s1 = t0 = 0
    s0 = t1 = 1
    k = 2
    while deg(r1) > m && k <= d
        q, r2 = divrem(r0, r1)
        s2 = s0 - q * s1
        t2 = t0 - q * t1
        s0 = s1
        s1 = s2
        t0 = t1
        t1 = t2
        r0 = r1
        r1 = r2
        k += 1
    end
    pade = r1 // t1
    pade_normal!(pade)
end

"""
    pade_normal!(p::Frac)

Normalize rational function by multiplying denominator and numerator polynom
in order to change least significant term of denominator to one.
"""
function pade_normal!(p::Frac{<:UnivariatePolynomial})
    den = p.den
    num = p.num
    k = findfirst(isunit, den.coeff)
    if k !== nothing
        u = den.coeff[k]
        num.coeff ./= u
        den.coeff ./= u
    end
    p
end

function evaluate(p::Union{Frac{<:UnivariatePolynomial},UnivariatePolynomial}, x::AbstractFloat)
    float(Rational(evaluate(p, rationalize(x))))
end

function show(io::IO, a::Frac)
    if isone(a.den)
        show(io, a.num)
    else
        print(io, '(', a.num, ") \u2044(", a.den, ')')
    end
end
    
