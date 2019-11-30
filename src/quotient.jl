
# class constructors
Quotient(X,::Type{R}) where R<:Ring = new_class(R,Quotient{sintern(X)}, X)
Quotient(X::Integer,::Type{T}) where T<:Integer = T / T(X)

# convenience type constructor
# enable `Z / m` for anonymous quotient class constructor
/(::Type{R}, m) where R<:Ring = new_class(Quotient{R,sintern(m)}, pseudo_ideal(R, m))

# Constructors
basetype(::Type{<:Quotient{T}}) where T = T
depth(::Type{<:Quotient{T}}) where T = depth(T) + 1

function Quotient{R,X}(a::R) where {X,R<:Ring}
    m = modulus(Quotient{R,X})
    v = rem(a, m)
    Quotient{R,X}(v, NOCHECK)
end

# convert argument to given R
Quotient{R,X}(v::Quotient{R,X}) where {X,R<:Ring} = Quotient{R,X}(v.val)
Quotient{R,X}(v) where {X,R<:Ring} = Quotient{R,X}(R(v))

# promotion and conversion
_promote_rule(::Type{<:Quotient}, ::Type{<:Quotient}) = Base.Bottom
_promote_rule(::Type{Quotient{R,X}}, ::Type{S}) where {X,R,S<:Ring} = Quotient{promote_type(R,S),X}
promote_rule(::Type{Quotient{R,X}}, ::Type{S}) where {X,R,S<:Integer} = Quotient{R,X}

convert(::Type{Q}, a::Q) where {X,R,Q<:Quotient{R}} = a
convert(::Type{Q}, a::S) where {R,S,Q<:Quotient{R}} = Q(convert(R, a))

Base.isless(p::T, q::T) where T<:Quotient = isless(p.val, q.val)

## Arithmetic

==(a::T, b::T) where T<:Quotient =  a.val == b.val
==(a::Quotient, b::Quotient) =  false
+(a::T, b::T) where T<:Quotient =  T(a.val + b.val)
-(a::T, b::T) where T<:Quotient =  T(a.val - b.val)
*(a::T, b::T) where T<:Quotient =  T(a.val * b.val)
*(a::Integer, b::T) where T<:Quotient =  T(a * b.val)
*(a::T, b::Integer) where T<:Quotient =  T(a.val * b)
-(a::T) where T<:Quotient =  T(-a.val)
inv(a::T) where T<:Quotient = T(invert(a.val, modulus(T)), NOCHECK)

isunit(a::T) where T<:Quotient = isunit(a.val) || isinvertible(modulus(T), a.val)
iszero(x::Quotient) = iszero(x.val)
isone(x::Quotient) = isone(x.val)
zero(::Type{Q}) where {S,Q<:Quotient{S}} = Q(zero(S), NOCHECK)
one(::Type{Q}) where {S,Q<:Quotient{S}} = Q(one(S), NOCHECK)

# induced homomorphism - invalid if Q = R/I and I not in kernel(F)
function (h::Hom{F,R,S})(a::Q) where {F,R,S,Q<:Quotient{<:R}}
    iszero(F(modulus(Q))) || throw(DomainError((F,R), "ideal not in kernel of homomorphism"))
    F(a.val)
end

# note:
# the real work is in the functions `Ideal`, `rem`, `invert`, `isinvertible` which
# have all been delegated to Ideal

## Help functions

# return the ideal associated uniquely with this quotient ring
modulus(t::Type{<:Quotient{R}}) where R = gettypevar(t).modulus

# standard functions
==(a::Quotient{S,X},b::Quotient{T,X}) where {X,S,T} = a.val == b.val
hash(a::Quotient, h::UInt) = hash(a.val, hash(modulus(a), h))

function Base.show(io::IO, a::Quotient)
    v = a.val
    m = modulus(a)
    print(io, v, " mod(", m, ")")
end

