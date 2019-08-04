module CommutativeRings

export Ring, RingInt, FractionField, QuotientRing, Polynomial
export ZZ, QQ, ZZmod, Frac, Quotient, UnivariatePolynomial, MultivariatePolynomial

export Ideal

export new_class, new_ideal, isunit, degree, pgcd, content, primpart, lc, modulus

import Base: +, -, *, /, inv, ^, \, getindex
import Base: iszero, isone, zero, one, div, rem, divrem, ==, hash, gcd, gcdx, lcm
import Base: copy

using Base.Checked

# RingClass subtypes describe the different categories
abstract type RingClass end
struct ZZClass <: RingClass end
abstract type FractionFieldClass <:RingClass end
struct FractionClass <: FractionFieldClass end
struct QQClass <:FractionFieldClass end
abstract type QuotientRingClass <:RingClass end
struct QuotientClass <: QuotientRingClass
    ideal::Any
end
struct ZZmodClass{T<:Integer} <: QuotientRingClass
    modulus::T
end
abstract type PolyRingClass <: RingClass end
abstract type UniPolyRingClass <: PolyRingClass end
abstract type MultiPolyRingClass <: PolyRingClass end

const NCT = Val{:nocheck}
const NOCHECK = Val(:nocheck)

# Ring subtypes describe the ring elements
# They are connected to a corresponding RingClass by type parameters
# and accessible by method `owner`.
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
    ZZ{T}(val::Integer) where T = new{T}(val)
    ZZ(val::T) where T<:Signed = ZZ{T}(val)
end

"""
    ZZmod{m,S<:Integer}

Quotient ring modulo integer `m > 0`, also noted as `ZZ/m`.
If `p` is a prime number, `ZZmod{p}` is the field `ZZ/p`.
"""
struct ZZmod{m,S<:Integer} <: QuotientRing{S,ZZmodClass{S}}
    val::S
    ZZmod{m,T}(a::Integer, ::NCT) where {m,T} = new{m,T}(T(a))
end

"""
    Frac{R}

The ring of fractions of `R`. The elements consist of pairs `num::R,den::R`.
During creation the values may be canceled, such as `gcd(num, den) == one(R)`.
The special case of `R<:Integer` is handled by `QQ{R}`.
"""
struct Frac{R<:Ring} <: FractionField{R,FractionFieldClass}
    num::R
    den::R
end

"""
    Quotient{m,R} 

The quotient ring of `R` modulo `m`, also written as `R / m`.
`m` may be an ideal of `R` or a (list of) element(s) of `R` generating the ideal.
Typically `m` is replaced by a symbolic Id, and the actual `m` is given as argument(s)
to the type constructor like  `new_class(Quotient{:Id,ZZ}, m...)`.
If the `Id`is omitted, an anonymous symbol is used. Also `Zm = Z/m` works.
"""
struct Quotient{Id,R<:Ring} <: QuotientRing{R,QuotientClass}
    val::R
    Quotient{Id,R}(v::R, ::NCT) where {Id,R<:Ring} = new{Id,R}(v)
end

"""
    QQ{S<:RingInt}


"""
struct QQ{S<:RingInt} <: FractionField{S,QQClass}
    num::S
    den::S
end

"""
    UnivariatePolynomial{Var,S<:RingInt}

Polynomials of ring elemets `S` in one variable `Var` (by default `:X`).
The variable name is specified as a `Symbol`.
Besides `UnivariatePolynomial{:X,Ring}` also the constructor `R[:X]` works.
"""
struct UnivariatePolynomial{X,S<:Ring} <: Polynomial{S,UniPolyRingClass}
    coeff::Vector{S}
    UnivariatePolynomial{X,S}(v::Vector{S}, ::NCT) where {X,S<:Ring} = new{X,S}(v)
end

"""
    MultivariatePolynomial{Id,N,S<:RingInt}

Polynomials of ring elemets `S` in `N` variables.
The `Id` identifies on object of type `MultiPolyRingClass` which is needed to store
the variable names and properties.
"""
struct MultivariatePolynomial{Id,N,S<:Ring} <: Polynomial{S,MultiPolyRingClass}
    coeff::Dict{NTuple{N,Int},S}
end


## End of Ring classes

"""
    Ideal{R}

Respresent in Ideal of Ring `R`. Only Ideals with a finite (Groebner) basis.
"""
struct Ideal{R<:Ring}
    base::Vector{R}
    Ideal{R}() where R = new{R}(R[])
end

# implementation

include("typevars.jl")
include("generic.jl")
include("zz.jl")
include("zzmod.jl")
include("quotient.jl")
include("fraction.jl")
include("univarpolynom.jl")
#include("multivarpolynom.jl")
include("ideal.jl")

end # module
