
## Creation

pseudo_ideal(::Type{R},m::RingInt) where R = R(m)
pseudo_ideal(::Type{R},mm::AbstractVector) where R = Ideal(Vector{R}(mm))
Ideal(m::R) where R<:Ring = Ideal{R}([m])
Ideal(m::T) where T<:Integer = Ideal(ZZ{T}(m))
Ideal(mm::RingInt...) = Ideal(collect(Base.promote_typeof(mm...), mm))
Ideal(mm::AbstractVector{<:Integer}) = Ideal(gcd(mm))
Ideal(mm::AbstractVector{R}) where R<:Polynomial = Ideal{R}(groebnerbase(mm))

# Arithmetic

import Base: in, issubset, ==

function in(a::R, id::Ideal{R}) where R <:MultivariatePolynomial
    r, a, d = red(a, id.base)
    isone(d) && iszero(r)
end

function issubset(id1::Ideal{R}, id2::Ideal{R}) where R
    for b1 in id1.base
        in(b1, id2) || return false
    end
    true
end

function ==(id1::Ideal{R}, id2::Ideal{R}) where R
    id1.base == id2.base
end


