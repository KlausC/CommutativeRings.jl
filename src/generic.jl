
# promotions and conversions
function promote_rule(::Type{T}, ::Type{S}) where {T<:Ring,S<:Ring}
    dts = depth(T) - depth(S)
    if dts < 0
        promote_rule(S, T)
    elseif dts > 0
        B = basetype(T)
        if B == S
            T
        else
            promote_rule(B, S) == B ? T : _promote_rule(T, S)
        end
    else
        _promote_rule(T, S)
    end
end

promote_rule(::Type{R}, ::Type{S}) where {R<:Ring,S<:Rational}= _promote_rule(R, S)
promote_rule(::Type{S}, ::Type{R}) where {R<:Ring,S<:Rational} = _promote_rule(R, S)
_promote_rule(::Type{R}, ::Type{S}) where {R<:Ring,S<:Rational} = promote_rule(R, promote_type(basetype(R), S))

depth(::Type{<:Number}) = 0

for op in (:+, :-, :*, :/, :(==), :divrem, :div, :rem, :gcd, :gcdx, :pgcd, :pgcdx, :isless)
    @eval begin
        ($op)(a::Ring, b::Ring) = ($op)(promote(a, b)...)
        ($op)(a::Ring, b::Union{Integer,Rational}) = ($op)(promote(a, b)...)
        ($op)(a::Union{Integer,Rational}, b::Ring) = ($op)(promote(a, b)...)
    end
end

# generic operations
basetype(::T) where T<:Ring = basetype(T)
basetype(::Type{T}) where T = T

convert(::Type{T}, a) where T = T(a)
(G::Type{<:Ring})(a) = G !== basetype(G) ? G(convert(basetype(G), a)) : throw(MethodError(G, a))
@generated function basetypes(a)
    _basetypes(::Type{a}) where a = begin b = basetype(a); a == b ? [a] : [a; _basetypes(b)] end
    bt = tuple(_basetypes(a.parameters[1])...)
    :($bt)
end

function /(a::T, b::T) where T<:Ring
    if b isa Union{FractionField,QuotientRing}
        a * inv(b)
    else
        d, r = divrem(a, b)
        iszero(r) || throw(DomainError((a, b), "not dividable a/b."))
        T(d)
    end
end
\(a::Ring, b::Ring) = b / a
^(a::Ring, n::Integer) = Base.power_by_squaring(a, n)
zero(x::Ring) = zero(typeof(x))
one(x::Ring) = one(typeof(x))
inv(a::Ring) = isunit(a) ? 1 / a : throw(DomainError(a, "cannot divide by non-unit."))
# enable generic matrix factorization
abs(a::Ring) = isunit(a) ? 1 : 0
value(a::Ring) = a

import Base: literal_pow
@inline literal_pow(::typeof(^), x::Ring, ::Val{0}) = one(x)
@inline literal_pow(::typeof(^), x::Ring, ::Val{1}) = x
@inline literal_pow(::typeof(^), x::Ring, ::Val{2}) = x * x
@inline literal_pow(::typeof(^), x::Ring, ::Val{3}) = x * x * x

numerator(a::Ring) = a
denominator(::R) where R<:Ring = one(R)

"""
    order(::Type)

Returns the number of elements of (finite) ring `Z` or `0` if `|Z| == inf`. 
"""
order(::Type) = 0
order(::Type{Z}) where Z<:ZZmod = uptype(modulus(Z))

"""
    dimension(::Type)

Returns the number of dimensions of vector-space like rings (like quotient rings over polynomials).
In al other cases return `1`
"""
dimension(R::Type) = 1

"""
    characteristic(::Type)

Returns characteristic `c` of ring `R`.
`c` is the smallest positive integer with `c * one(R) == 0`, or `0` if `c * one(R) != 0` for all positive integers `c`.
"""
characteristic(::Type) = 0

"""
    intpower(a, b)

Calculate `a ^ b` in appropriate result type.
"""
intpower(a::Integer, b::Integer) = uptype(a, mintype_for(a, b, false)) ^ b

"""
    uptype(a, [T::Type])

promote `a` to get at least type `promote_type(typeof(a), T)`.
"""
uptype(a::T, S::Type=Int) where T = promote_type(S, T)(a)

"""
    order(z::Ring)

Returns the order of the cyclic multiplicative group generated by z,
or `0` if `z^k != 1` for all integers `k`. 
"""
function order(x::Ring)
    iszero(x) && return 0
    isone(x) && return 1
    n = mult_order(typeof(x))
    n <= 1 && return n
    r = trailing_zeros(n)
    f = factor(n >> r)
    for k in factors(f)
        y = x^k
        isone(y) && return k
        j = k
        for s = 1:r
            y *= y
            j += j
            isone(y) && return j
        end
    end
    0
end

"""
    mult_order(R::Type{<:Ring})

order of multiplicative subgroup of `R`.
"""
mult_order(R::Type) = 0
mult_order(R::Type{<:ZZmod}) = totient(modulus(R))
mult_order(R::Type{<:GaloisField}) = order(R) - 1
function mult_order(R::Type{<:Quotient{T,T}} where T<:UnivariatePolynomial)
    isirreducible(modulus(R)) ? order(R) - 1 : 0
end

"""
    characteristic(Z::Type{<:Ring})

Returns the characteristic `c` of ring `Z`. `c` is the smallest positive integer
with `c * one(Z) == 0`, or `0` if `c * one(Z) != 0` for all positive integers `c`.
"""
characteristic(::Type{Z}) where Z<:ZZmod = order(Z)
characteristic(::Type{T}) where {Z,T<:Quotient{Z}} = characteristic(Z)
characteristic(::Type{T}) where {Z,T<:Frac{Z}} = characteristic(Z)
characteristic(::Type{T}) where {Z,T<:Polynomial{Z}} = characteristic(Z)

"""
    isfield(::Type{<:Ring})

Return iff type is a field (all elements except `zero` are invertible).
"""
isfield(::Type{<:Ring}) = false

"""
    deg(r::Union{Ring,Number})

Return the degree of ring element or number `r`.

For zero elements, that is `-1`, otherwise `0` for non-polynomials,
the ordinary degree for univariate polynomials and the
maximum sum of exponents for multivariate polynomials.
"""
deg(x::Union{Ring,Number}) = iszero(x) ? -1 : 0 # fallback

function divrem(a::T, b::T) where T<:Ring
    if isunit(b)
        (a * inv(b), zero(b))
    else
        throw(MethodError(divrem, (a, b)))
    end
end
div(a::T, b::T) where T<:Ring = divrem(a, b)[1]
rem(a::T, b::T) where T<:Ring = divrem(a, b)[2]
"""
    isdiv(a, b)

Return if ring element `a` is dividable by `b` without remainder.
"""
isdiv(a::T, b::T) where T <: Ring = iszero(rem(a, b))

"""
    iscoprime(a, b)

Return if there is a non-unit common divisor of `a` and `b`.
"""
iscoprime(a::T, b::T) where T<:Ring = isunit(a) || isunit(b)

divrem(a::T, b::T) where T<:QuotientRing = (a / b, zero(a))
"""
    LC(r::Ring)

Return the leading coefficient of `r`. For non-polynomials return `r` itself.
"""
LC(x::Ring) = x

"""
    lcunit(r::Ring)

Return `one(r)` if it's a unit, otherwise return a unit element `s` of the same ring or of
an object, which may be promoted to this ring, so `r / s` has a simplified form.
Example, for a polynomial over a field, the leading coefficient.
"""
lcunit(x::Ring) = one(x)

modulus(::T) where T<:Ring = modulus(T)
copy(p::QuotientRing) = typeof(p)(p.val)
# make Ring elements behave like scalars with broadcasting
Base.broadcastable(x::Ring) = Ref(x)

# apply homomorphism
(h::Hom{F,R,S})(a::R) where {F,R,S} = h.f(a)::S

divrem2(a::T, b::T) where T = divrem(a, b)
rem2(a::T, b::T) where T = divrem2(a, b)[2]

function divrem2(a::T, b::T) where T<:FractionField
    c = div(a, b)
    d, r = divrem2(c.num, c.den)
    d, a - d * b
end

# generic Euclid's algorithm
function gcd(a::T, b::T) where T<:Ring
    iszero(b) && return a
    a, b = b, rem2(a, b)
    while !iszero(b)
        d, c = divrem2(a, b)
        if iszero(d)
            a = one(a)
            break
        end
        a, b = b, c
        issimpler(b, a) || throw(DomainError((a,b), "b is not simpler than a"))
    end
    u = lcunit(a)
    isone(a) ? a : a * inv(u)
end

# extension to array
function gcd(aa::Union{AbstractVector{T},NTuple{N,T}}) where {N,T<:Ring}
    n = length(aa)
    n == 0 && return zero(T)
    n == 1 && return aa[1]
    g = gcd(aa[1], aa[2])
    for i = 3:n
        isone(g) && break
        g = gcd(aa[i], g)
    end
    g
end
gcd(a::T...) where T<:Ring = gcd(a)

pgcd(a::R, b::R) where R<:Ring = gcd(a, b)

# generic extended Euclid's algorithm
function gcdx(a::T, b::T) where T<:Ring
    s0, s1 = one(T), zero(T)
    t0, t1 = s1, s0
    # invariant: a * s0 + b * t0 == gcd(a, b)
    while !iszero(b)
        q, r = divrem2(a, b)
        a, b = b, r
        issimpler(b, a) || throw(DomainError((a,b), "b is not simpler than a"))
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    end
    u = lcunit(a)
    if isone(a) 
        a, s0, t0
    else
        a, s0, t0 = a / u, s0 / u, t0 / u
    end
end

function gcdx(a::Union{AbstractVector{T},NTuple{N,T}}) where {N,T<:Ring}
    n = length(a)
    n == 0 && return zero(T), zero(T), zero(T)
    u = similar(a)
    g = a[1]
    u[1] = one(T)
    for i = 2:n
        g, s, u[i] = gcdx(g, a[i])
        for j = 1:i-1
            u[j] *= s
        end
    end
    g, u
end
gcdx(a::T...) where T<:Ring = gcdx([a...])

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

function Base.powermod(x::R, p::Integer, m::R) where R<:Ring
    if p == 1
        return rem(x, m)
    elseif p == 0
        return one(x)
    elseif p == 2
        return rem(x * x, m)
    elseif p < 0
        if isunit(x)
            isone(x) && return copy(x)
            isone(-x) && return iseven(p) ? one(x) : copy(x)
            powermod(inv(x), -p, m)
        else
            throw(ArgumentError("negative powers not supported"))
        end
    end
    t = trailing_zeros(p) + 1
    p >>= t
    while (t -= 1) > 0
        x  = rem(x * x, m)
    end
    y = x
    while p > 0
        t = trailing_zeros(p) + 1
        p >>= t
        while (t -= 1) >= 0
            x  = rem(x * x, m)
        end
        y = rem(y * x, m)
    end
    return y
end

const SUPERSCRIPTS = Char[0x2070, 0xb9, 0xb2, 0xb3, 0x2074, 0x2075, 0x2076, 0x2077, 0x2078, 0x2079, 0x207a, 0x207b]
const SUBSCRIPTS = Char[0x2080, 0x2081, 0x2082, 0x2083, 0x2084, 0x2085, 0x2086, 0x2087, 0x2088, 0x2089, 0x208a, 0x208b]

tosuper(a::Integer; sign::Bool=false) = _integer_to_script(a, SUPERSCRIPTS, sign)
tosub(a::Integer; sign::Bool=false) = _integer_to_script(a, SUBSCRIPTS, sign)
function _integer_to_script(a::Integer, chars::Vector{Char}, sign::Bool)
    io = IOBuffer()
    if a < 0
        print(io, chars[12])
    elseif sign
        print(io, chars[11])
    end
    for d in reverse(digits(a))
        print(io, chars[abs(d)+1])
    end
    String(take!(io))
end

function sort_unique!(A::AbstractVector; rev::Bool=false)
    n = length(A)
    n == 0 && return A
    a = sort!(A, rev=rev)
    j = 1
    aj = a[1]
    for i = 2:length(a)
        ai = a[i]
        if !isequal(aj, ai)
            j += 1
            aj = ai
        end
        if i != j
            a[j] = aj
        end
    end
    if j < n
        resize!(a, j)
    end
    a
end

"""
    testrules(io, g)

Test associativity and distributivity for all element combinations from `g`.
Print messages to `io` if errors found.
`g` can be a collection of `Ring` elements or a subtype of `Ring` (which is iterable).
"""
function testrules(io, gg)
    for a in gg
        if isunit(a)
            if !isone(inv(a) * a) || !isone(a * inv(a))
                println(io, "inv($a)")
            end
        end
        if a * a * a != a ^ 3
            println(io, "$(a) ^ 3")
        end
    end
    for (a,b,c) in Iterators.product(gg, gg, gg)
        if (a * b) * c != a * ( b * c)
            println(io, "assoc * $a $b $c")
        end
        if (a + b) + c != a + ( b + c)
            println(io, "assoc + $a $b $c")
        end
        if a * ( b + c) != a * b + a * c
            println(io, "distrib $a $b $c")
        end
    end
end
