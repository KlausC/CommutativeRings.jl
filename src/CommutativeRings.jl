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

export compose_inv, Li, Ein, lin1p, lin1pe, ver

export minimal_polynomial
export rational_normal_form, rnf_matrix, rnf_transformation, rnf_polynomials
export mfactor, killmemo!, memoize

import Base: +, -, *, /, inv, ^, \, //, ==, hash, isapprox
import Base: getindex, sign, log, isfinite, adjoint
import Base: iszero, isone, isless, zero, one, div, rem, divrem, mod, gcd, gcdx, lcm
import Base: copy, show, promote_rule, convert, abs, isless, length, iterate, eltype, sum
import Primes: factor, isprime
import Base: Rational, numerator, denominator, precision, sqrt
import LinearAlgebra: checksquare, det

# Re-exports (of non-Base functions)
export det, isprime, factor

# implementation

include("ringtypes.jl")
include("typevars.jl")
include("generic.jl")
include("zz.jl")
include("qq.jl")
include("zzmod.jl")
include("quotient.jl")
include("fraction.jl")
include("univarpolynom.jl")
include("multivarpolynom.jl")
include("determinant.jl")
include("resultant.jl")
include("ideal.jl")
include("enumerations.jl")
include("factorization.jl")
include("galoisfields.jl")
include("intfactorization.jl")
include("numbertheoretical.jl")
include("linearalgebra.jl")
include("rationalcanonical.jl")
include("powerseries.jl")
include("specialseries.jl")

using .SpecialPowerSeries
end # module
