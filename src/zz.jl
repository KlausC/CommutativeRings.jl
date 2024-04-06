
# class constructors
ZZ(::Type{T}) where T<:Integer = ZZ{T}

# construction
category_trait(::Type{<:ZZ}) = EuclidianDomainTrait
basetype(::Type{<:ZZ{T}}) where T = T

Base.IteratorSize(::Type{<:ZZ}) = Base.IsInfinite()
lcunit(a::Z) where Z<:ZZ = a < 0 ? -one(a) : one(a)
issimpler(a::T, b::T) where T<:ZZ = abs(a.val) < abs(b.val)
iscoprime(a::T, b::T) where T<:ZZ = gcd(a.val, b.val) == 1
value(a::ZZ) = a.val

copy(a::ZZ) = typeof(a)(a.val)
ZZ(a::T) where T<:Integer = ZZ{T}(a)
ZZ{T}(a::ZZ) where T = ZZ{T}(T(a.val))
ZZ(a::ZZ{T}) where T = copy(a)

function ZZ{T}(a::Union{QQ{T},Frac{ZZ{T}}}) where T
    a.den != 1 && throw(InexactError(:ZZ, ZZ{T}, a))
    ZZ(a.num)
end
ZZ(a::Union{QQ{T},Frac{ZZ{T}}}) where T = ZZ{T}(a)
ZZ{S}(a::Union{QQ{T},Frac{ZZ{T}}}) where {S,T} = ZZ(promote_type(S, T)(a))

# promotion and conversion
promote_rule(::Type{ZZ{T}}, ::Type{ZZ{S}}) where {S,T} = ZZ{promote_type(S, T)}
promote_rule(::Type{ZZ{T}}, ::Type{QQ{S}}) where {S,T} = QQ{promote_type(S, T)}
promote_rule(::Type{ZZ{T}}, ::Type{S}) where {S<:Integer,T} = ZZ{promote_type(S, T)}
promote_rule(::Type{ZZ{T}}, ::Type{Rational{S}}) where {S<:Integer,T} =
    QQ{promote_type(S, T)}

# induced homomorphism
function (h::Hom{F,R,S})(p::Z) where {F,R,S,Z<:ZZ{<:R}}
    Z(h.f(p.val))
end

for op in (:+, :-, :/, :(==), :div, :rem, :divrem, :gcd, :gcdx, :pgcd, :pgcdx)
    @eval begin
        ($op)(a::ZZ{T}, b::Integer) where T = ($op)(promote(a, b)...)
        ($op)(a::Integer, b::ZZ{T}) where T = ($op)(promote(a, b)...)
    end
end

Base.isless(p::T, q::T) where T<:ZZ = isless(p.val, q.val)

# operations for ZZ
+(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_add(a.val, b.val))
-(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_sub(a.val, b.val))
-(a::ZZ{T}) where T = ZZ{T}(checked_neg(a.val))
*(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_mul(a.val, b.val))
*(a::ZZ{T}, b::Integer) where T = ZZ(T(checked_mul(a.val, T(b))))
*(a::Integer, b::ZZ{T}) where T = ZZ(T(checked_mul(T(a), b.val)))
^(a::ZZ{BigInt}, b::Integer) = ZZ(a.val^b)
divrem(a::T, b::T) where T<:ZZ = T.(divrem(a.val, b.val))
div(a::T, b::T) where T<:ZZ = T(a.val ÷ b.val)
rem(a::T, b::T) where T<:ZZ = T(a.val % b.val)

isunit(a::ZZ) = abs(a.val) == 1
isone(a::ZZ) = isone(a.val)
iszero(a::ZZ) = iszero(a.val)
zero(::Type{ZZ{T}}) where T = ZZ(zero(T))
one(::Type{ZZ{T}}) where T = ZZ(one(T))
==(a::ZZ{T}, b::ZZ{T}) where T = a.val == b.val
hash(a::ZZ, h::UInt) = hash(a.val, h)

gcd(a::T, b::T) where T<:ZZ = T(gcd(a.val, b.val))
lcm(a::T, b::T) where T<:ZZ = T(lcm(a.val, b.val))

factor(a::Z) where Z<:ZZ = [Z(first(x)) => last(x) for x in Primes.factor(value(a))]
isirreducible(a::ZZ) = isirreducible(a.val)

Base.show(io::IO, z::ZZ) = print(io, z.val)

function (::Type{T})(a::ZZ) where T<:Integer
    T(value(a))
end

wide_type(::Type{<:ZZ}) = ZZ{BigInt}
