module CommutativeRings

export Ring, RingInt, FractionField, QuotientRing, Polynomial
export ZZ, QQ, ZZmod, UnivariatePolynomial, MultivariatePolynomial

export RingClass, ZZClass, FractionFieldClass, QuotientRingClass, ZZmodClass
export PolyRingClass, UniPolyRingClass, MultiPolyRingClass

export owner, isunit

import Base: +, -, *, /, inv, ^, \
import Base: iszero, isone, zero, one, div, rem, ==

using Base.Checked

# RingClass subtypes describe the different categories
abstract type RingClass end
struct ZZClass <: RingClass end
abstract type FractionFieldClass <:RingClass end
abstract type QuotientRingClass <: RingClass end
abstract type ZZmodClass <: QuotientRingClass end
abstract type PolyRingClass <: RingClass end
abstract type UniPolyRingClass <: RingClass end
abstract type MultiPolyRingClass <: RingClass end


# Ring subtypes describe the ring elements
# They era connected to a corresponding RingClass by type parameters
# and method `owner`.
"""
    Ring{<:RingClass}

Abstract superclass of all commutative ring element types.
All subtypes support the arithmetic operators `+, -, *, and ^(power)`.
The operators `inv, /` may be defined on a subset.
"""
abstract type Ring{T<:RingClass} end

"""
    RingInt

Union of system `Integer` types and any `Ring` subtype. 
"""
const RingInt = Union{Ring,Integer}
"""
    FractionField{S<:RingInt,T<:FractionFieldClass}

Rational extension of elements of ring `S`. Example the field of rational numbers.
"""
abstract type FractionField{S<:RingInt,T<:FractionFieldClass} <: Ring{T} end
"""
    QuotientRing{S<:Union{Integer,Ring},T<:QuotientRingClass}

Quotient ring of ring `S` by some ideal. If S = Z, the ring of integer numbers, and p 
a positive number Z/p is calculation modulo p.
"""
abstract type QuotientRing{S<:RingInt,T<:QuotientRingClass} <: Ring{T} end
"""
    Polynomial{S<:Ring,T<:PolyRingClass}
"""
abstract type Polynomial{S<:Ring,T<:PolyRingClass} <: Ring{T} end

"""
    ZZ{S<:Signed}

The ring of integer numbers. There may be restrictions on the set of representable
elemets according to the chosen `S`.
"""
struct ZZ{T<:Signed} <: Ring{ZZClass}
    val::T
end

"""
    QQQ{S<:RingInt}


"""
struct QQ{S<:RingInt} <: FractionField{S,FractionFieldClass}
    num::S
    den::S
end

"""
    ZZmod{m,S<:Integer}

Quotient ring modulo integer `m > 0`, also noted as `ZZ/m`.
If `p` is a prime number, `ZZmod{p}` is the field `ZZ/p`.
"""
struct ZZmod{m,S<:Integer} <: QuotientRing{S,ZZmodClass}
    val::S
end

"""
    UnivariatePolynomial{Var,S<:RingInt}

Polynomials of ring elemets `S` in one variable `Var` (by default `:X`).
The variable name is specified as a `Symbol`.
"""
struct UnivariatePolynomial{Id,S<:Ring,T} <: Polynomial{S,T}
    coeff::Vector{S}
end

"""
    MultivariatePolynomial{Id,N,S<:RingInt}

Polynomials of ring elemets `S` in `N` variables.
The `Id` identifies on object of type `MultiPolyRingClass` which is needed to store
the variable names and properties.
"""
struct MultivariatePolynomial{Id,N,S<:Ring,T<:MultiPolyRingClass} <: Polynomial{S,T}
    coeff::Dict{NTuple{N,Int},S}
end
owner(::Ring{T}) where T = T

include("generic.jl")
#include("fractionfield.jl")
include("quotientring.jl")
#include("univarpolynom.jl")
#include("multivarpolynom.jl")

end # module
