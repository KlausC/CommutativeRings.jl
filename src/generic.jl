
# generic operations
owner(::Type{<:Ring{T}}) where T = T
\(a::T, b::T) where T<:Ring = inv(a) * b
^(a::Ring, n::Integer) = Base.power_by_squaring(a, n)
zero(x::Ring) = zero(typeof(x))
one(x::Ring) = one(typeof(x))

# operations for ZZ
+(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_add(a.val, b.val))
-(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_sub(a.val, b.val))
-(a::ZZ{T}) where T = ZZ{T}(checked_neg(a.val))
*(a::ZZ{T}, b::ZZ{T}) where T = ZZ(checked_mul(a.val, b.val))
*(a::ZZ{T}, b::Integer) where T = ZZ(T(checked_mul(a.val, T(b))))
*(a::Integer, b::ZZ{T}) where T = ZZ(T(checked_mul(T(a), b.val)))
function /(a::ZZ{T}, b::ZZ{T}) where T
    d, r = divrem(a.val, b.val)
    iszero(r) || throw(DivideError())
    ZZ{T}(d)
end
\(a::ZZ{T}, b::ZZ{T}) where T = b / a

isunit(a::ZZ) = abs(a.val) == 1
isone(a::ZZ) = isone(a.val)
iszero(a::ZZ) = iszero(a.val)
zero(::Type{ZZ{T}}) where T = ZZ(zero(T))
one(::Type{ZZ{T}}) where T = ZZ(one(T))
==(a::ZZ{T}, b::ZZ{T}) where T = a.val == b.val

inv(a::ZZ{T}) where T = isunit(a) ? a : throw(DivideError())
