
# construction
copy(a::ZZ) = typeof(a)(a.val)
ZZ{T}(a::ZZ{T}) where T = a
ZZ{T}(a::ZZ) where T = ZZ{T}(a.val)

# operations for ZZ
+(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_add(a.val, b.val))
-(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_sub(a.val, b.val))
-(a::ZZ{T}) where T = ZZ{T}(checked_neg(a.val))
*(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_mul(a.val, b.val))
*(a::ZZ{T}, b::Integer) where T = ZZ(T(checked_mul(a.val, T(b))))
*(a::Integer, b::ZZ{T}) where T = ZZ(T(checked_mul(T(a), b.val)))
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

gcd(a::T, b::T) where T<: ZZ = T(gcd(a.val, b.val))
lcm(a::T, b::T) where T<:ZZ = T(lcm(a.val, b.val))
    
