module CommutativeRings

using LinearAlgebra
using Base.Checked
using Primes
using Random

export category_trait, isfield
export Ring, RingInt, FractionRing, QuotientRing, Polynomial
export ZZ, QQ, ZZmod, Frac, Quotient, UnivariatePolynomial, MultivariatePolynomial
export GaloisField, FSeries

export PowerSeries, O, precision, absprecision

export Hom, Ideal

export isunit, deg, ord, content, primpart, content_primpart, isnegative, isproper
export LC, LM, LT, CC, lcunit, multideg, modulus, value
export isdiv, pdivrem, divremv, pgcd, pgcdx
export resultant, discriminant, signed_subresultant_polynomials, sylvester_matrix
export basetype, basetypes, depth, iszerodiv
export monom, ismonom, ismonic, issimpler, iscoprime
export evaluate, derive, pade, pade_normal!
export isirreducible, irreducible, irreducibles
export num_irreducibles, isreducible, reducible, reducibles
export characteristic, dimension, order
export ofindex, index
export generator
export GF, homomorphism
export num_primitives, isprimitive

export VectorSpace, complement, sum, intersect, isequal, issubset
export groebnerbase, SPOL, lextend
export generators, varnames, varname, factors

export characteristic_polynomial, adjugate, companion

export compose_inv

export minimal_polynomial
export rational_normal_form, rnf_matrix, rnf_transformation, rnf_polynomials

import Base: +, -, *, /, inv, ^, \, //, ==, hash, getindex, sign, log, isfinite, adjoint
import Base: iszero, isone, isless, zero, one, div, rem, divrem, mod, gcd, gcdx, lcm
import Base: copy, show, promote_rule, convert, abs, isless, length, iterate, eltype, sum
import Primes: factor, isprime
import Base: Rational, numerator, denominator, precision
import LinearAlgebra: checksquare, det

# Re-exports (of non-Base functions)
export det, isprime, factor

# RingClass subtypes describe the different categories
abstract type RingClass end
struct ZZClass{T<:Integer} <: RingClass end
abstract type FractionRingClass <: RingClass end
struct FractionClass{P} <: FractionRingClass end
struct QQClass{S<:Integer} <: FractionRingClass end
abstract type QuotientRingClass <: RingClass end
struct QuotientClass{Id,M} <: QuotientRingClass
    modulus::M
end
struct ZZmodClass{m,T<:Integer} <: QuotientRingClass
    modulus::T
end
abstract type PolyRingClass <: RingClass end
struct UniPolyRingClass{X,R} <: PolyRingClass end
struct MultiPolyRingClass{X,R,N} <: PolyRingClass
    varnames::Vector{Symbol}
end
struct PowerSeriesRingClass{X,R} <: PolyRingClass end

struct GaloisFieldClass{Id,T,Q} <: QuotientRingClass
    factors::Primes.Factorization # of order of multiplicative group
    exptable::Vector{T}
    logtable::Vector{T}
    zechtable::Vector{T}
end

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
    FractionRing{S<:RingInt,T<:FractionRingClass}

Rational extension of elements of ring `S`. Example the field of rational numbers.
"""
abstract type FractionRing{S<:RingInt,T<:FractionRingClass} <: Ring{T} end

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
struct ZZ{T<:Signed} <: Ring{ZZClass{T}}
    val::T
    ZZ{T}(val::Integer) where T = new{T}(val)
    ZZ(val::T) where T<:Signed = ZZ{T}(val)
end

"""
    ZZmod{m,S<:Integer}

Quotient ring modulo integer `m > 0`, also noted as `ZZ/m`.
If `p` is a prime number, `ZZmod{p}` is the field `ZZ/p`.
"""
struct ZZmod{m,S<:Integer} <: QuotientRing{S,ZZmodClass{m,S}}
    val::S
    ZZmod{m,T}(a::Integer, ::NCT) where {m,T} = new{m,T}(T(a))
end

"""
    Frac{R}

The ring of fractions of `R`. The elements consist of pairs `num::R,den::R`.
During creation the values may be canceled to achieve `gcd(num, den) == one(R)`.
The special case of `R<:Integer` is handled by `QQ{R}`.
"""
struct Frac{P<:Union{Polynomial,ZZ}} <: FractionRing{P,FractionClass{P}}
    num::P
    den::P
    Frac{P}(num::P, den::P, ::NCT) where P = new{P}(num, den)
end

"""
    Quotient{R,I,m}

The quotient ring of `R` modulo `m` of type `I`, also written as `R / m`.
`m` may be an ideal of `R` or a (list of) element(s) of `R` generating the ideal.
Typically `m` is replaced by a symbolic `X`, and the actual `m` is given as argument(s)
to the type constructor like  `new_class(Quotient{ZZ,`X`}, m...)`.
If the ``X``is omitted, an anonymous symbol is used.

The preferred way of construction is via `Zm = Z/m`.
"""
struct Quotient{R<:Ring,I,X,Id} <: QuotientRing{R,QuotientClass{X,I}}
    val::R
    Quotient{R,I,X,Id}(v::R, ::NCT) where {I,X,R<:Ring,Id} = new{R,I,X,Id}(v)
end

"""
    QQ{S<:Integer}


"""
struct QQ{S<:Integer} <: FractionRing{S,QQClass{S}}
    num::S
    den::S
    QQ{T}(num::Integer, den::Integer, ::NCT) where T = new{T}(num, den)
end

"""
    UnivariatePolynomial{S<:RingInt,Id}

Polynomials of ring elemets `S` in one variable `Id` (by default `:x`).
The variable name is specified as a `Symbol`.

A convenience constructor `S[:x]` is the preferred way to construct this class.
"""
struct UnivariatePolynomial{S<:Ring,X} <: Polynomial{S,UniPolyRingClass{X,S}}
    first::Int
    coeff::Vector{S}
    UnivariatePolynomial{S,X}(f::Int, v::Vector{S}, ::NCT) where {X,S} = new{S,X}(f, v)
end

"""
    MultivariatePolynomial{S<:RingInt,N,Id}

Polynomials of ring elemets `S` in `N` variables.
The `Id` identifies on object of type `MultiPolyRingClass` which is needed to store
the variable names and properties.

A convenience constructor `S[:x,:y...]` is the preferred way to construct this class.
"""
struct MultivariatePolynomial{S<:Ring,N,Id,T,B} <: Polynomial{S,MultiPolyRingClass{Id,S,N}}
    ind::Vector{T}
    coeff::Vector{S}
end

struct GaloisField{Id,T,Q} <: QuotientRing{ZZmod{T},GaloisFieldClass{Id,T,Q}}
    val::T
    GaloisField{Id,T,Q}(v, ::NCT) where {Id,T,Q} = new{Id,T,Q}(T(v))
end

# Categorial traits specify algebraic properties of ring types
# (cf. https://en.wikipedia.org/wiki/Integral_domain)
# rings ⊃ commutative rings ⊃ integral domains ⊃ integrally closed domains ⊃ GCD domains ⊃
# unique factorization domains ⊃ principal ideal domains ⊃ Euclidean domains ⊃ fields ⊃ algebraically closed fields
abstract type RingTrait end
abstract type CommutativeRingTrait <: RingTrait end
abstract type IntegralDomainTrait <: CommutativeRingTrait end
abstract type IntegrallyClosedDomainTrait <: IntegralDomainTrait end
abstract type GCDDomainTrait <: IntegrallyClosedDomainTrait end
abstract type UniqueFactorizationDomainTrait <: GCDDomainTrait end
abstract type PrincipalIdealDomainTrait <: UniqueFactorizationDomainTrait end
abstract type EuclidianDomainTrait <: PrincipalIdealDomainTrait end
abstract type FieldTrait <: EuclidianDomainTrait end
abstract type AlgebraicallyClosedFieldTrait <: FieldTrait end

## End of Ring classes

"""
    Ideal{R}

Respresent in Ideal of Ring `R`. Only Ideals with a finite (Groebner) basis.
"""
struct Ideal{R<:Ring}
    base::Vector{R}
    Ideal{R}(a::Vector{R}) where R = new{R}(a)
end

"""
    Hom{function,R,R'}

Represent a ring homomorphism `function:R -> R'`.
"""
struct Hom{F,R<:RingInt,S<:RingInt}
    f::F
    Hom{R,S}(f::F) where {F<:Union{Function,Type},R,S} = new{F,R,S}(f)
end

"""
    VectorSpace{R,V}

Represent a vector space over a Vfield `R`.
"""
struct VectorSpace{R,V}
    base::V
    pivr::Vector{Int} # row permutation vector
    function VectorSpace{R}(b::B, pivr) where {R,B<:AbstractMatrix}
        pivr = *(size(b)...) == 0 ? collect(1:length(pivr)) : pivr
        new{R,B}(b, pivr)
    end
end

"""
    FSeries{T,F}

Represent a Taylor- or Laurent-series by a function over the integers.
"""
struct FSeries{T,F}
    f::F
    FSeries{T}(f::F) where {T,F<:Function} = new{T,F}(f)
    FSeries(f::F) where {F<:Function} = FSeries{typeof(f(0))}(f)
end

# implementation

include("typevars.jl")
include("generic.jl")
include("zz.jl")
include("qq.jl")
include("zzmod.jl")
include("quotient.jl")
include("fraction.jl")
include("univarpolynom.jl")
include("multivarpolynom.jl")
include("ideal.jl")
include("enumerations.jl")
include("factorization.jl")
include("intfactorization.jl")
include("numbertheoretical.jl")
include("galoisfields.jl")
include("linearalgebra.jl")
include("rationalcanonical.jl")
include("powerseries.jl")
include("specialseries.jl")

end # module
