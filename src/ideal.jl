
## Creation

pseudo_ideal(::Type{R},m::RingInt) where R = R(m)
pseudo_ideal(::Type{R},mm::AbstractVector) where R = Ideal(Vector{R}(mm))
Ideal(m::R) where R<:Ring = Ideal{R}([m])
Ideal(m::T) where T<:Integer = Ideal(ZZ{T}(m))
Ideal(mm::RingInt...) = Ideal(collect(Base.promote_typeof(mm...), mm))
Ideal(mm::AbstractVector{<:Integer}) = Ideal(gcd(mm))
Ideal(mm::AbstractVector{R}) where R<:Polynomial = Ideal{R}(groebnerbase(mm))

# Arithmetic

import Base: in, issubset, ==, intersect, sum, +, *, ^, iszero, zero, one

function in(a::R, id::Ideal{R}) where R<:MultivariatePolynomial
    r, a, d = red(a, id.base)
    isone(d) && iszero(r)
end

function issubset(id1::Ideal{R}, id2::Ideal{R}) where R<:Polynomial
    for b1 in id1.base
        in(b1, id2) || return false
    end
    true
end

==(id1::Ideal{R}, id2::Ideal{R}) where R<:Ring = id1.base == id2.base
==(id::Ideal{R}, ::Type{R}) where R<:Ring = isone(id)
==(id::Ideal, a) = false
==(::Type{R}, id::Ideal{R}) where R<:Ring = isone(id)
==(a, id::Ideal) = false

function +(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    Ideal(vcat(id1.base, id2.base))
end
+(id::Ideal{R}, a::R) where R = Ideal([id.base; a])
+(a::R, id::Ideal{R}) where R = Ideal([id.base; a])

function *(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    C = [ b1 * b2 for b1 in id1.base for b2 in id2.base]  
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
        ib = id.base
        n = length(ib)
        C = [ib[i] * ib[j] for i = 1:n for j = 1:i]
        Ideal(C)
    elseif iseven(p)
        (id^(p÷2))^2
    else
        id^((p-1)÷2) * id^((p+1)÷2)
    end
end

function intersect(id1::Ideal{R}, id2::Ideal{R}) where R<:MultivariatePolynomial
    t = Symbol("intersect_extension")
    Rt = lextend(R, t)
    t, = generators(Rt)
    id3 = Ideal([Rt.(id1.base) .* t; Rt.(id2.base) .* (1 - t)])
    C = [x for x in id3.base if leading_expo(x)[1] == 0]
    Ideal(R.(C))
end

iszero(id::Ideal) = length(id.base) == 0
isone(id::Ideal) = length(id.base) == 1 && isone(id.base[1])
zero(::Type{I}) where {R,I<:Ideal{R}} = Ideal(R[])
one(::Type{I}) where {R,I<:Ideal{R}} = Ideal(R[1])
one(::R) where R<:Ideal = one(R)
zero(::R) where R<:Ideal = zero(R)

