
# promotions and conversions
Base.convert(::Type{T}, a::Union{RingInt,Rational}) where T<:Ring = T(a)
Base.convert(::Type{T}, a::T) where T<:Ring = a

for op in (:+, :-, :*, :/, :(==), :divrem, :div, :rem, :gcd, :gcdx, :pgcd, :pgcdx)
    @eval begin
        ($op)(a::Ring, b::Ring) where {T,S} = ($op)(promote(a, b)...)
        ($op)(a::Ring, b::Union{Integer,Rational}) where {T,S} = ($op)(promote(a, b)...)
        ($op)(a::Union{Integer,Rational}, b::Ring) where {T,S} = ($op)(promote(a, b)...)
    end
end

# generic operations
function /(a::T, b::T) where T<:Ring
    d, r = divrem(a, b)
    iszero(r) || throw(DomainError((a, b), "not dividable a/b."))
    T(d)
end
/(a::Union{FractionField,QuotientRing}, b::Ring) = inv(a) * b
/(a::Ring, b::Union{FractionField,QuotientRing}) = a * inv(b)
/(a::Union{FractionField,QuotientRing}, b::Union{FractionField,QuotientRing}) = a * inv(b)
\(a::Ring, b::Ring) = b / a
^(a::Ring, n::Integer) = Base.power_by_squaring(a, n)
zero(x::Ring) = zero(typeof(x))
one(x::Ring) = one(typeof(x))
inv(a::Ring) = isunit(a) ? 1 / a : throw(DomainError(a, "cannot divide by non-unit."))
deg(x::Ring) = 0 # fallback
divrem(a::T, b::T) where T<:Ring =  throw(MethodError(divrem, (a, b)))
div(a::T, b::T) where T<:Ring = divrem(a, b)[1]
rem(a::T, b::T) where T<:Ring = divrem(a, b)[2]
isdiv(a::T, b::T) where T <: Ring = iszero(rem(a, b))
divrem(a::T, b::T) where T<:QuotientRing = (a / b, zero(a))

modulus(::T) where T<:Ring = modulus(T)
copy(p::QuotientRing) = typeof(p)(p.val)
# make Ring elements behave like scalars with broadcasting
Base.broadcastable(x::Ring) = Ref(x)

# generic Euclid's algorithm
function gcd(a::T, b::T) where T<:Ring
    while !iszero(b)
        a, b = b, rem(a, b)
    end
    a
end

# extension to array
function gcd(aa::Union{AbstractVector{T},NTuple{N,T}}) where {T<:Ring,N}
    n = length(aa)
    n == 0 && return zero(T)
    n == 1 && return aa[1]
    g = gcd(aa[1], aa[2])
    for i = 3:n
        isunit(g) && break
        g = gcd(aa[i], g)
    end
    g
end
gcd(a::T...) where T<:Ring = gcd(a)

# generic extended Euclid's algorithm
function gcdx(a::T, b::T) where T<:Ring
    s0, s1 = one(T), zero(T)
    t0, t1 = s1, s0
    # invariant: a * s0 + b * t0 == gcd(a, b)
    while !iszero(b)
        q, r = divrem(a, b)
        a, b = b, r
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    end
    a, s0, t0
end

# least common multiplier derived from gcd
function lcm(a::T, b::T) where T<:Ring
    div(a, gcd(a, b)) * b
end

function lcm(aa::AbstractVector{T}) where T<:Ring
    n = length(aa)
    n == 0 && return one(T)
    n == 1 && return aa[1]
    g = lcm(aa[1], aa[2])
    for i = 3:n
        g = lcm(aa[i], g)
    end
    g
end

