
# Utility classes to facilitate (::Type{<:X}) arguments
# require type to be concrete
struct CType{T}
    function CType(::Type{X}) where X
        if isconcretetype(X)
            new{X}()
        else
            terror(lazy"concrete type needed but got $X")
        end
    end
end

# require type not to be Union{}
struct NType{T}
    function NType(::Type{X}) where X
        if X !== Union{}
            new{X}()
        else
            terror(lazy"nonunion type needed but got $X")
        end
    end
end


# RingClass subtypes describe the different categories
abstract type RingClass end
struct ZZClass{T<:Integer} <: RingClass end
abstract type FractionRingClass <: RingClass end
struct FractionClass{P} <: FractionRingClass end
struct QQClass{S} <: FractionRingClass end
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

struct AlgebraicNumberClass <: FractionRingClass end

struct NumberFieldClass{T,Id} <: QuotientRingClass
    generator::T
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
    RingIntRatSc

Union of system `Integer`, `Rational`, and `UniformScaling` types and any `Ring` subtype.
"""
const RingIntRatSc = Union{Ring,Integer,Rational,UniformScaling}

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

mutable struct ZZZ <: Ring{ZZClass{Integer}}
    d::Int

    function ZZZ(x::ZZZ)
        z = new()
        ccall((:fmpz_init_set, libflint), Nothing, (Ref{ZZZ}, Ref{ZZZ}), z, x)
        finalizer(_fmpz_clear_fn, z)
        return z
    end

    function ZZZ(x::Int)
        z = new()
        ccall((:fmpz_init_set_si, libflint), Nothing, (Ref{ZZZ}, Int), z, x)
        finalizer(_fmpz_clear_fn, z)
        return z
    end

    function ZZZ(x::UInt)
        z = new()
        ccall((:fmpz_init_set_ui, libflint), Nothing, (Ref{ZZZ}, UInt), z, x)
        finalizer(_fmpz_clear_fn, z)
        return z
    end

    function ZZZ(x::BigInt)
        z = new()
        ccall((:fmpz_init, libflint), Nothing, (Ref{ZZZ},), z)
        ccall((:fmpz_set_mpz, libflint), Nothing, (Ref{ZZZ}, Ref{BigInt}), z, x)
        finalizer(_fmpz_clear_fn, z)
        return z
    end

    function ZZZ(x::Float64)
        !isinteger(x) && throw(InexactError(:convert, ZZZ, x))
        z = new()
        ccall((:fmpz_init, libflint), Nothing, (Ref{ZZZ},), z)
        ccall((:fmpz_set_d, libflint), Nothing, (Ref{ZZZ}, Cdouble), z, x)
        finalizer(_fmpz_clear_fn, z)
        return z
    end

end

const ZI = Union{ZZ,ZZZ}

function _fmpz_clear_fn(a::ZZZ)
   ccall((:fmpz_clear, libflint), Nothing, (Ref{ZZZ},), a)
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
struct Frac{P<:Union{Polynomial,ZI}} <: FractionRing{P,FractionClass{P}}
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
If the `X` is omitted, an anonymous symbol is used.

The preferred way of construction is via `Zm = Z/m`.
"""
struct Quotient{R<:Ring,I,X,Id} <: QuotientRing{R,QuotientClass{X,I}}
    val::R
    Quotient{R,I,X,Id}(v::R, ::NCT) where {I,X,R<:Ring,Id} = new{R,I,X,Id}(v)
end

"""
    QQ{S<:Integer}


"""
struct QQ{S<:Union{Integer,ZZZ}} <: FractionRing{S,QQClass{S}}
    num::S
    den::S
    QQ{T}(num::Union{Integer,ZZZ}, den::Union{Integer,ZZZ}, ::NCT) where T = new{T}(num, den)
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
    MultivariatePolynomial{S<:Ring,N,Id}

Polynomials of ring elements `S` in `N` variables.
The `Id` identifies on object of type `MultiPolyRingClass` which is needed to store
the variable names and properties.

A convenience constructor `S[:x,:y...]` is the preferred way to construct this class.
"""
struct MultivariatePolynomial{S<:Ring,N,Id,T,B} <: Polynomial{S,MultiPolyRingClass{Id,S,N}}
    ind::Vector{T}
    coeff::Vector{S}
end

"""
Power Series (aka Taylor Series) are a generalization of polynomials.
Calculation is restricted to a maximal "precision"(number of terms to be considered).
All further terms are subsumed in a "remainder term".
"""
struct PowerSeries{Y,R,X} <: Ring{PowerSeriesRingClass{X,R}}
    poly::UnivariatePolynomial{R,X}
    prec::Int
    PowerSeries{Y,R,X}(p, prec) where {Y,R,X} = new{Y,R,X}(p, prec)
    function PowerSeries{Y}(p::P, prec::Integer) where {R,X,P<:UnivariatePolynomial{R,X},Y}
        new{Y,R,X}(p, prec)
    end
end

struct GaloisField{C,D,Id,T,Q} <: QuotientRing{ZZmod{T},GaloisFieldClass{Id,T,Q}}
    val::T
    GaloisField{C,D,Id,T,Q}(v, ::NCT) where {C,D,Id,T,Q} = new{C,D,Id,T,Q}(T(v))
end

"""
    AlgebraicNumber(p, approx=-Inf)

Create an AlgebraicNumer with minimal polynomial `p` being a root of `p` closet to `approx`.

An algebraic number `α` of degree `n` is represented as a root of an
irreducible monic polynomial over `Q` of degree `n`, the minimal polynomial of `α`.
The set of algebraic numbers form a field and it is possible to derive representions
of `α` ∘ `β` for all field operations `∘` and `-α` and `inv(α)`.

# Extended help
Algebraic numbers are defined to be real or complex numbers, which are zeros of monic
polynomials over the rational numbers. Each algebraic number `A` is defined by its
minimal polynomial and an approximation of the zero of it. The minimal polynomial is
the uniquely determined irreducible monic polynomial, which has this zero.
Algebraic operations with algebraic numbers are possible but expensive, because polynomials
of a degree of the product of the degrees of the operands have to be factored in the worst
case.
"""
struct AlgebraicNumber <: Ring{AlgebraicNumberClass}
    minpol::UnivariatePolynomial{QQ{BigInt},:x}
    roots::Vector{ComplexF64}
    rootid::Int
    approx::Complex{BigFloat}
    AlgebraicNumber(p::UnivariatePolynomial, r, id::Integer, a, ::NCT) = new(p, r, id, a)
end

"""
    NumberField{<:AlgebraicNumber}
    NF(A::AlgebraicNumber)

Create the NumberField of an algebraic number `A`. Elements of the number field can be
created by `NF(A)(polynomial)`.

A number field is a subfield of the algebraic numbers, which consists of all linear
combinations of powers of a fixed base algebraic number `α`.

As a vector space it has the basis `α^i for i = 1:n-1` where `n`is the degree of `α`.

Each element of a field number is represented by a polynomial modulo the minimal polynomial
of `α`, by a field isomorphism.

# Extended help
A number field over an algebraic number NF(A) is the vector space of rational linear
combinations of the powers of A. It has dimension of the degree of the minimal polynomial.
It has a natural field isomorphism with the quotient ring of the minimal polynomial,
which is used to allow efficient operations.
"""
struct NumberField{T<:AlgebraicNumber,Id,Q<:Quotient} <: Ring{NumberFieldClass{T,Id}}
    repr::Q
    NumberField{T,Id}(r::Q, ::NCT) where {T,Id,Q<:Quotient} = new{T,Id,Q}(r)
end

"""
    RingNumber

Union of all scalar and discrete types.
"""
const RingNumber = Union{Integer,Rational,ZZZ,ZZ,QQ,ZZmod,GaloisField}

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
    Hom{function,R,S}

Represent a ring homomorphism `function:R -> S`.
"""
struct Hom{F,R<:RingInt,S<:RingInt}
    f::F
    function Hom{R,S}(f::F) where {F<:Union{Function,Type},R,S}
        f0 = f(zero(R))
        f0 isa S && iszero(f0) || throw(ArgumentError("f(R(0)) !== S(0)"))
        f1 = f(one(R))
        f1 isa S && isone(f1) || throw(ArgumentError("f(R(1)) !== S(1)"))
        new{F,R,S}(f)
    end
end

"""
    VectorSpace{R,V}

Represent a vector space over a field `R`.
"""
struct VectorSpace{R,V}
    base::V
    pivr::Vector{Int} # row permutation vector
    function VectorSpace{R}(b::B, pivr) where {R,B<:AbstractMatrix}
        pivr = *(size(b)...) == 0 ? collect(eachindex(pivr)) : pivr
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

"""
    IterTerms(p::Polynomial)

Return iterator over all non-zero terms of polynomial `p`.
"""
struct IterTerms{P<:Polynomial}
    p::P
end
Base.IteratorSize(::IterTerms) = Base.HasLength()
Base.IteratorEltype(::IterTerms) = Base.HasEltype()

"""
    DeepIterTerms(p::Polynomial)

Return iterator for the leaf terms for a polynomial of polynomials.
"""
struct DeepIterPolynomial{P<:Polynomial,N}
    p::P
    function DeepIterPolynomial(p::P, n=-1) where P<:Polynomial
        m = pdepth(P)
        n = n < 0 ? m : min(n, m)
        new{P,n}(p)
    end
end
Base.IteratorSize(::DeepIterPolynomial) = Base.SizeUnknown()
Base.IteratorEltype(::DeepIterPolynomial) = Base.HasEltype()

"""
    RNF(polynomials, transformation)

Store the polynomials list and the transformation for rational normal form,
aka Frobenius normal form.
"""
struct RNF{R<:Ring,P<:UnivariatePolynomial{R},V<:AbstractVector{P},M<:AbstractMatrix{R}}
    minpoly::V
    trans::M
end

"""
    WNF(polynomials, transformation)

Store the polynomials list and the transformation for Weierstrass normal form.
The vector of polynomials corresponds to the transformation matrix.
"""
struct WNF{
    R<:Ring,
    P<:UnivariatePolynomial{R},
    V<:AbstractVector{Pair{P,Int}},
    M<:AbstractMatrix{R},
}
    minpoly::P
    polyfact::V
    trans::M
end

"""
    SNF(D, S, T)

Store the elements of a Smith normal form of a matrix `A`.

`D` is a vector with nonzero elements of a principal ideal domain (PID). Each vector element
except the last one divides its successor.

`S` and `T` are invertible matrixes over the PID, with `S * A * T == Diag(D)`.
"""
struct SNF{R<:Ring,V<:AbstractVector{R},S<:AbstractMatrix{R}}
    diag::V
    trans1::S
    trans2::S
end

# types to control dispatch for a few functions
const OtherNumber = Union{AbstractFloat, Complex}
const OtherFloat = Union{AbstractFloat, Complex{<:AbstractFloat}}
