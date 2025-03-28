module CommutativeRings

using LinearAlgebra
using Base.Checked
using Primes
using Random
using FLINT_jll

const libflint = FLINT_jll.libflint

function flint_abort()
  error("Problem in the Flint-Subsystem")
end

export category_trait, isfield
export Ring, RingInt, FractionRing, QuotientRing, Polynomial
export ZZ, ZZZ, ZI, QQ, ZZmod, Frac, Quotient, UnivariatePolynomial, MultivariatePolynomial
export GaloisField, GF, FSeries, AlgebraicNumber, NumberField, NF

export SpecialPowerSeries, PowerSeries, O, precision, absprecision
export Conway

export Hom, Ideal

export isunit, deg, ord, content, primpart, content_primpart, isnegative, isproper
export LC, LM, LT, CC, lcunit, multideg, modulus, value
export isdiv, pdivrem, divremv, pgcd, pgcdx
export resultant, discriminant, signed_subresultant_polynomials, sylvester_matrix
export basetype, basetypes, depth, iszerodiv
export base, approx
export monom, ismonom, ismonic, issimpler, iscoprime, issquarefree, sff
export evaluate, derive, pade, pade_normal!
export mapping, domain, codomain
export isirreducible, irreducible, irreducibles
export num_irreducibles, isreducible, reducible, reducibles
export characteristic, dimension, order
export ofindex
export generator, generators
export homomorphism
export num_primitives, isprimitive, ismonomprimitive
export elementary_symmetric, newton_symmetric

export VectorSpace, complement, sum, intersect, isequal, issubset
export groebnerbase, SPOL, lextend
export varnames, varname, factors

export characteristic_polynomial, minimal_polynomial, field_polynomial, adjugate, companion
export field_matrix, field_polynomial, tr, norm
export compose_inv, Li, Ein, lin1p, lin1pe, ver

export rational_normal_form, matrix, transformation, polynomials
export weierstrass_normal_form, smith_normal_form
export mfactor, killmemo!, memoize

import Base: +, -, *, /, inv, ^, \, //, ==, hash, isapprox
import Base: getindex, sign, log, sqrt, isfinite, adjoint
import Base: iszero, isone, isless, zero, one, div, rem, divrem, mod, gcd, gcdx, lcm
import Base: copy, show, promote_rule, convert, abs, isless, length, iterate, eltype, sum
import Base: Rational, numerator, denominator, precision

import Primes: factor, isprime
import LinearAlgebra: checksquare, det, norm, tr

# Re-exports (of non-Base functions)
export det, isprime, factor

# implementation

include("ringtypes.jl")
include("typevars.jl")
include("promoteconvert.jl")
include("generic.jl")
include("zz.jl")
include("zzflint.jl")
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
include("conway.jl")
include("lll.jl")
include("ll.jl")
include("fourier.jl")
include("fastmultiply.jl")
include("algebraic.jl")
include("numberfield.jl")
include("luebeck.jl")

using .SpecialPowerSeries
using .Conway
end # module
