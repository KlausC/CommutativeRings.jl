
## Creation

pseudo_ideal(::Type{R}, m::RingInt) where R = R(m)
pseudo_ideal(::Type{R}, mm::AbstractVector) where R = Ideal(Vector{R}(mm))
pseudo_ideal(::Type{R}, m::Ideal{R}) where R = m

function Ideal(m::R) where R<:Ring
    if iszero(m)
        Ideal{R}(R[])
    elseif isunit(m)
        Ideal{R}([one(R)])
    else
        Ideal{R}([m])
    end
end
Ideal(m::T) where T<:Integer = Ideal(ZZ{T}(m))
Ideal(mm::RingInt...) = Ideal(collect(Base.promote_typeof(mm...), mm))
Ideal(mm::AbstractVector{<:RingInt}) = Ideal(gcd(mm))
Ideal(mm::AbstractVector{R}) where R<:MultivariatePolynomial = Ideal{R}(groebnerbase(mm))

# Arithmetic

import Base: in, issubset, ==, intersect, sum, +, *, ^, iszero, zero, one, rem

function in(a::R, id::Ideal{R}) where R<:MultivariatePolynomial
    a, r, d = pdivrem(a, id.base)
    isone(d) && iszero(r)
end

function issubset(id1::Ideal{R}, id2::Ideal{R}) where R<:Polynomial
    for b1 in id1.base
        in(b1, id2) || return false
    end
    true
end

==(id1::Ideal{R}, id2::Ideal{S}) where {R<:Ring,S<:Ring} = id1.base == id2.base
==(id::Ideal{R}, ::Type{R}) where R<:Ring = isone(id)
==(::Type{R}, id::Ideal{R}) where R<:Ring = isone(id)

function +(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    Ideal(vcat(id1.base, id2.base))
end
+(id::Ideal{R}, a::R) where R = Ideal([id.base; a])
+(a::R, id::Ideal{R}) where R = Ideal([a; id.base])

function *(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    C = [b1 * b2 for b1 in id1.base for b2 in id2.base]
    Ideal(C)
end

*(id::Ideal{R}, a::R) where R = Ideal(id.base .* a)
*(a::R, id::Ideal{R}) where R = Ideal(a .* id.base)

function ^(id::Ideal{R}, p::Integer) where R<:MultivariatePolynomial
    if p == 1
        id
    elseif p == 0
        Ideal([one(R)])
    elseif p == 2
        id * id
    elseif iseven(p)
        (id^(p ÷ 2))^2
    else
        (id^((p - 1) ÷ 2))^2 * id
    end
end

# remainder when dividing by an ideal
rem(a::R, id::Ideal{R}) where R<:Ring = divrem(a, id)[2]

function intersect(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    Ideal(_intersect(id1.base, id2.base))
end

function _intersect(v1::V, v2::V) where {R<:MultivariatePolynomial,V<:AbstractVector{R}}
    t = Symbol("intersect_extension")
    Rt = lextend(R, t)
    t, = generators(Rt)
    id3 = Ideal([Rt.(v1) .* t; Rt.(v2) .* (1 - t)])
    R.([x for x in id3.base if multideg(x)[1] == 0])
end

iszero(id::Ideal) = length(id.base) == 0
isone(id::Ideal) = length(id.base) == 1 && isone(id.base[1])
zero(::Type{I}) where {R,I<:Ideal{R}} = Ideal(R[])
one(::Type{I}) where {R,I<:Ideal{R}} = Ideal(R[1])
one(::R) where R<:Ideal = one(R)
zero(::R) where R<:Ideal = zero(R)
