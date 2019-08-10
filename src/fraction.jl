
# construction
basetype(::Type{<:Frac{T}}) where T = T
copy(a::Frac) = typeof(a)(a.num,a.den, NOCHECK)
sign(a::Frac) = sign(a.num)

Frac{T}(a::Frac{T}) where T = a
Frac{T}(a::Frac{S}) where {T,S} = Frac{T}(a.num, a.den, NOCHECK)

Frac{T}(a::Integer) where T = Frac{T}(T(a), one(T), NOCHECK)
Frac{T}(a::Ring) where T = Frac{T}(T(a), one(T), NOCHECK)
Frac(a::T) where T<:Ring  = Frac{T}(a, one(T), NOCHECK)
Frac(a::T) where T<:Integer = Frac{ZZ{T}}(ZZ(a), one(ZZ{T}), NOCHECK)
//(a::T, b::T) where T<:Ring = Frac(a, b)
function Frac(a::T, b::T) where T
    g = pgcd(a, b)
    b /= g
    s = sign(b)
    b /= s
    a /= g * s
    Frac{T}(a, b, NOCHECK)
end

promote_rule(::Type{Frac{T}}, ::Type{Frac{S}}) where {S,T} = Frac{promote_type(S,T)}
promote_rule(::Type{Frac{T}}, ::Type{S}) where {S<:Ring,T} = Frac{promote_type(S,T)}
promote_rule(::Type{Frac{T}}, ::Type{S}) where {S<:Integer,T} = Frac{promote_type(S,T)}
promote_rule(::Type{Frac{T}}, ::Type{Rational{S}}) where {S,T} = Frac{promote_type(S,T)}

convert(F::Type{Frac{T}}, a::Type{Frac{S}}) where {S,T} = F(T(a.num), T(a.den), NOCHECK)
convert(F::Type{Frac{T}}, a::Ring) where T = F(T(a), one(T), NOCHECK)
convert(F::Type{Frac{T}}, a::Integer) where T = F(T(a), one(T), NOCHECK)
convert(F::Type{Frac{T}}, a::Rational) where T = F(T(a.num), T(a.den), NOCHECK)

# operations for Frac

function +(x::T, y::T) where T<:Frac
    a, b, c, d = x.num, x.den, y.num, y.den
    h = pgcd(b, d)
    b /= h
    d /= h
    n = a * d + b * c
    g = pgcd(n, h)
    T(n / g, h / g * b * d, NOCHECK)
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

function show(io::IO, a::Frac)
    if isone(a.den)
        show(io, a.num)
    else
        print(io, '(', a.num, ")/(", a.den, ')')
    end
end
    
