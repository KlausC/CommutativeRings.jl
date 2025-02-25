
import Base: ==, !=, <=, >=, <, >, &, xor, |

wide_type(::Type{ZZZ}) = ZZZ
Base.signbit(a::ZZZ) = a < 0

# construction
category_trait(::Type{<:ZZZ}) = EuclidianDomainTrait
basetype(::Type{<:ZZZ}) = BigInt

Base.IteratorSize(::Type{<:ZZZ}) = Base.IsInfinite()
lcunit(a::Z) where Z<:ZZZ = a < 0 ? -one(a) : one(a)
issimpler(a::T, b::T) where T<:ZZZ = abs(a) < abs(b)
iscoprime(a::T, b::T) where T<:ZZZ = gcd(a, b) == one(T)
value(a::ZZZ) = BigInt(a)

copy(a::ZZZ) = ZZZ(a)
ZZZ(a::T) where T<:Base.BitSignedSmall = ZZZ(Int(a))
ZZZ(a::T) where T<:Base.BitUnsignedSmall = ZZZ(UInt(a))
ZZZ(a::T) where T<:Base.BitInteger = ZZZ(BigInt(a))
ZZZ(a::T) where T<:Real = ZZZ(Integer(a))

function ZZZ(a::Union{QQ{T},Frac{ZZ{T}}}) where T
    a.den != 1 && throw(InexactError(:ZZZ, ZZZ, a))
    ZZZ(a.num)
end

# promotion and conversion
promote_rule(::Type{ZZZ}, ::Type{<:ZZ}) = ZZZ
promote_rule(::Type{ZZZ}, ::Type{QQ{S}}) where {S} = QQ{promote_type(S, BigInt)}
promote_rule(::Type{ZZZ}, ::Type{S}) where {S<:Integer} = ZZZ
promote_rule(::Type{ZZZ}, ::Type{R}) where {R<:Rational} = QQ{promote_type(basetype(R), BigInt)}

# induced homomorphism
function (h::Hom{F,R,S})(p::Z) where {F,R,S,Z<:ZZZ}
    Z(h.f(value(p)))
end

for op in (:+, :-, :*, :/, :div, :rem, :divrem, :gcd, :gcdx, :pgcd, :pgcdx)
    @eval begin
        ($op)(a::ZZZ, b::Integer) = ($op)(promote(a, b)...)
        ($op)(a::Integer, b::ZZZ) = ($op)(promote(a, b)...)
    end
end

Base.isless(p::T, q::T) where T<:ZZZ = p < q
Base.to_power_type(x::ZZZ) = x

# operations for ZZ

fmpz(a::Symbol) = (Symbol(:fmpz_, a), libflint)

for (fJ, fC) in ((:+, :add), (:-, :sub), (:*, :mul), (:&, :and), (:|, :or), (:xor, :xor))
    @eval begin
        function ($fJ)(x::ZZZ, y::ZZZ)
            z = ZZZ(0)
            ccall($(fmpz(fC)), Nothing, (Ref{ZZZ}, Ref{ZZZ}, Ref{ZZZ}), z, x, y)
            return z
        end
        function ($fJ)(x::ZZZ, y::Int)
            z = ZZZ(0)
            ccall($(fmpz(Symbol(fC, "_si"))), Nothing, (Ref{ZZZ}, Ref{ZZZ}, Int), z, x, y)
            return z
        end
        function ($fJ)(x::ZZZ, y::UInt)
            z = ZZZ(0)
            ccall($(fmpz(Symbol(fC, "_ui"))), Nothing, (Ref{ZZZ}, Ref{ZZZ}, UInt), z, x, y)
            return z
        end

        function ($fJ)(y::Int, x::ZZZ)
            z = ZZZ(0)
            ccall($(fmpz(Symbol(fC, "_si"))), Nothing, (Ref{ZZZ}, Ref{ZZZ}, Int), z, x, y)
            return $(fC == :sub) ? -z : z
        end
        function ($fJ)(y::UInt, x::ZZZ)
            z = ZZZ(0)
            ccall($(fmpz(Symbol(fC, "_ui"))), Nothing, (Ref{ZZZ}, Ref{ZZZ}, UInt), z, x, y)
            return $(fC == :sub) ? -z : z
        end
    end
end

function -(a::ZZZ)
    z = ZZZ(0)
    ccall((:fmpz_neg, libflint), Nothing, (Ref{ZZZ}, Ref{ZZZ}), z, a)
    return z
end

function abs(a::ZZZ)
    z = ZZZ(0)
    ccall((:fmpz_abs, libflint), Nothing, (Ref{ZZZ}, Ref{ZZZ}), z, a)
    return z
end

^(a::ZZZ, b::Integer) = pow(a, b)
^(a::ZZZ, b::ZZZ) = pow(a, b)

function pow(a::ZZZ, b::T) where T<:Union{Integer,ZZZ}
    z = ZZZ(0)
    iszero(a) && return z
    if isunit(a)
        return !isone(a) && isodd(b) ? abs(a) : copy(a)
    end
    b < 0 && throw(DomainError(a, "cannot divide by non-unit."))
    ccall((:fmpz_pow_ui, libflint), Nothing, (Ref{ZZZ}, Ref{ZZZ}, UInt), z, a, b)
    return z
end

for (m, f) in ((RoundToZero, :t), (RoundDown, :f), (RoundUp, :c), (RoundNearest, :n))
    @eval begin
        function divrem(a::T, b::T, m::$(typeof(m))) where T<:ZZZ
            q = ZZZ(0)
            r = ZZZ(0)
            ccall(
                $(fmpz(Symbol(f, :div_qr))),
                Nothing,
                (Ref{ZZZ}, Ref{ZZZ}, Ref{ZZZ}, Ref{ZZZ}),
                q,
                r,
                a,
                b,
            )
            return q, r
        end
        function div(a::T, b::T, m::$(typeof(m))) where T<:ZZZ
            q = ZZZ(0)
            ccall(
                $(fmpz(Symbol(f, :div_q))),
                Nothing,
                (Ref{ZZZ}, Ref{ZZZ}, Ref{ZZZ}),
                q,
                a,
                b,
            )
            return q
        end
        function rem(a::T, b::T, m::$(typeof(m))) where T<:ZZZ
            r = ZZZ(0)
            ccall(
                $(fmpz(Symbol(f, :div_r))),
                Nothing,
                (Ref{ZZZ}, Ref{ZZZ}, Ref{ZZZ}),
                r,
                a,
                b,
            )
            return r
        end
    end
end

divrem(a::T, b::T) where T<:ZZZ = divrem(a, b, RoundToZero)
div(a::T, b::T) where T<:ZZZ = div(a, b, RoundToZero)
rem(a::T, b::T) where T<:ZZZ = rem(a, b, RoundToZero)

isunit(a::ZZZ) = abs(a.d) == 1
isone(a::ZZZ) = isone(a.d)
iszero(a::ZZZ) = iszero(a.d)
zero(::Type{ZZZ}) = ZZZ(0)
one(::Type{ZZZ}) = ZZZ(1)
hash(a::ZZZ, h::UInt) = hash(value(a), h)

factor(a::ZZZ) = [ZZZ(first(x)) => last(x) for x in Primes.factor(value(a))]
isirreducible(a::ZZZ) = isirreducible(value(a))

Base.show(io::IO, z::ZZZ) = print(io, value(z))

function (::Type{BigInt})(a::ZZZ)
    r = BigInt()
    ccall((:fmpz_get_mpz, libflint), Nothing, (Ref{BigInt}, Ref{ZZZ}), r, a)
    return r
end

function (::Type{Int})(a::ZZZ)
    (a > typemax(Int) || a < typemin(Int)) && throw(InexactError(:convert, Int, a))
    return ccall((:fmpz_get_si, libflint), Int, (Ref{ZZZ},), a)
end

function (::Type{UInt})(a::ZZZ)
    (a > typemax(UInt) || a < 0) && throw(InexactError(:convert, UInt, a))
    return ccall((:fmpz_get_ui, libflint), UInt, (Ref{ZZZ},), a)
end

function (::Type{Float64})(n::ZZZ)
    # rounds to zero
    ccall((:fmpz_get_d, libflint), Float64, (Ref{ZZZ},), n)
end

(::Type{T})(a::ZZZ) where T<:Union{Int128,UInt128,BigFloat} = T(BigInt(a))

(::Type{T})(a::ZZZ) where T<:Signed = T(Int(a))

(::Type{T})(a::ZZZ) where T<:Unsigned = T(UInt(a))

(::Type{T})(a::ZZZ) where T<:Union{Float16,Float32} = T(Float64(a))

Base.convert(::Type{R}, z::ZZZ) where R<:Real = R(z)

import Base: cmp, ==, <=, >=, <, >

function cmp(x::ZZZ, y::ZZZ)
    Int(ccall((:fmpz_cmp, libflint), Cint, (Ref{ZZZ}, Ref{ZZZ}), x, y))
end

function cmp(x::ZZZ, y::Int)
    Int(ccall((:fmpz_cmp_si, libflint), Cint, (Ref{ZZZ}, Int), x, y))
end

function cmp(x::ZZZ, y::UInt)
    Int(ccall((:fmpz_cmp_ui, libflint), Cint, (Ref{ZZZ}, UInt), x, y))
end

cmp(x::ZZZ, y::Integer) = cmp(value(x), y)

cmp(x::Integer, y::ZZZ) = -cmp(y, x)

for op in (:(==), :(!=), :(<=), :(>=), :(<), :(>))
    @eval begin
        $(op)(x::ZZZ, y::ZZZ) = $(op)(cmp(x, y), 0)
        $(op)(x::ZZZ, y::Integer) = $(op)(cmp(x, y), 0)
        $(op)(x::Integer, y::ZZZ) = $(op)(cmp(x, y), 0)
    end
end
