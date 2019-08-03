
# generic operations
function /(a::T, b::T) where T<:Ring
    d, r = divrem(a, b)
    iszero(r) || throw(DomainError((a, b), "not dividable a/b."))
    T(d)
end
/(a::T, b::T) where T<:Union{FractionField,QuotientRing} = a * inv(b)
\(a::T, b::T) where T<:Ring = b / a
^(a::Ring, n::Integer) = Base.power_by_squaring(a, n)
zero(x::Ring) = zero(typeof(x))
one(x::Ring) = one(typeof(x))
inv(a::Ring) = isunit(a) ? a : throw(DomainError(a, "cannot divide by non-unit."))
degree(x::Ring) = 0 # fallback
divrem(a::T, b::T) where T<:Ring =  throw(MethodError(divrem, (a, b)))
div(a::T, b::T) where T<:Ring = divrem(a, b)[1]
rem(a::T, b::T) where T<:Ring = divrem(a, b)[2]

# generic Euclid's algorithm
function gcd(a::T, b::T) where T<:Ring
    while !iszero(b)
        a, b = b, rem(a, b)
    end
    a
end

# extension to array
function gcd(aa::AbstractVector{T}) where T<:Ring
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

# generic extended Euclid's algorithm
function gcdx(a::T, b::T) where T<:Ring
    s0, s1 = one(T), zero(T)
    t0, t1 = s1, s0
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

