
category_trait(::Type{<:Ring}) = CommutativeRingTrait
category_trait(::Type{<:Number}) = IntegralDomainTrait

# promotions and conversions
#=
function promote_rule(::Type{T}, ::Type{S}) where {T<:Ring,S<:RingInt}
    dts = depth(T) - depth(S)
    if dts < 0
        Base.Bottom
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
=#
_promote_rule(::Type, ::Type) = Any
promote_rule(::Type{R}, ::Type{S}) where {R<:Ring,S<:Rational} = _promote_rule(R, S)
promote_rule(::Type{S}, ::Type{R}) where {R<:Ring,S<:Rational} = _promote_rule(R, S)
function _promote_rule(::Type{R}, ::Type{S}) where {R<:Ring,S<:Rational}
    promote_rule(R, promote_type(basetype(R), S))
end

promote_rule(::Type{A}, ::Type{<:QQ{B}}) where {A<:AbstractFloat,B} = promote_rule(A, B)
promote_rule(::Type{A}, ::Type{<:ZZ{B}}) where {A<:AbstractFloat,B} = promote_rule(A, B)

for op in (
    :+,
    :-,
    :*,
    :/,
    :\,
    :(==),
    :(//),
    :divrem,
    :div,
    :rem,
    :mod,
    :gcd,
    :gcdx,
    :pgcd,
    :pgcdx,
    :isless,
)
    @eval begin
        ($op)(a::Ring, b::Ring) = ($op)(promote(a, b)...)
        ($op)(a::Ring, b::Union{Integer,Rational}) = ($op)(promote(a, b)...)
        ($op)(a::Union{Integer,Rational}, b::Ring) = ($op)(promote(a, b)...)
    end
end
for op in (:+, :-, :*, :/, :\, :isapprox)
    @eval begin
        ($op)(a::Union{QQ,ZZ}, b::AbstractFloat) = ($op)(promote(a, b)...)
        ($op)(a::AbstractFloat, b::Union{QQ,ZZ}) = ($op)(promote(a, b)...)
    end
end

# generic operations
basetype(::T) where T<:Ring = basetype(T)
basetype(::Type{T}) where T = Union{}
basetype(::Type{Union{}}) = Union{}

depth(::Type{Union{}}) = -1
depth(::Type) = 0
depth(::Type{R}) where R<:Ring = depth(basetype(R)) + 1

adjoint(a::Ring) = a

convert(::Type{T}, a) where T<:Ring = T(a)
function convert(::Type{T}, a::S) where {T<:Ring,S<:Ring}
    if !(S <: basetype(T)) && depth(T) > depth(S)
        b = convert(basetype(T), a)
        convert(T, b)
    else
        T(a)
    end
end

function convert(::Type{A}, a::Union{ZZ,QQ}) where {A<:AbstractFloat}
    convert(A, value(a))
end

function (G::Type{<:Ring})(a::Any)
    B = basetype(G)
    # println("G = $G $(isconcretetype(G)) B = $B $(isconcretetype(B))")
    isconcretetype(B) ? G(convert(B, a)) : throw(MethodError(G, Ref(a)))
end

@generated function basetypes(a)
    _basetypes(::Type{a}) where a = begin
        b = basetype(a)
        a == b ? [] : [a; _basetypes(b)]
    end
    bt = tuple(_basetypes(a.parameters[1])...)
    :($bt)
end


_xpromote_rule(::Type{T},::Type{S}) where {T<:Ring,S<:RingInt} = begin
    #println("promote($T, $S)")
    depth(T) < depth(S) && return Base.Bottom
    B = basetype(T)
    (S <: T || S <: B) ? T : promote_rule(B, S) == B ? T : Base.Bottom
end
_xpromote_rule(a::Type, b::Type) = promote_rule(a, b)

@generated function Base.promote_rule(a::Type{<:Ring}, b::Type{<:RingInt})
    bt = _xpromote_rule(a.parameters[1], b.parameters[1])
    :($bt)
end

function /(a::T, b::T) where T<:Ring
    d, r = divrem(a, b)
    iszero(r) || throw(DomainError((a, b), "not dividable a/b."))
    T(d)
end
function /(a::T, b::T) where T<:Union{FractionRing,QuotientRing}
    a * inv(b)
end

import Base: literal_pow, power_by_squaring

\(a::T, b::T) where T<:Ring = b / a
^(a::Ring, n::Integer) = power_by_squaring(a, n)
zero(x::Ring) = zero(typeof(x))
one(x::Ring) = one(typeof(x))
inv(a::Ring) = isunit(a) ? 1 / a : throw(DomainError(a, "cannot divide by non-unit."))
# enable generic matrix factorization
abs(a::Ring) = isunit(a) ? 1 : 0
value(a::Ring) = a
isfinite(a::Ring) = true

@inline literal_pow(::typeof(^), x::Ring, ::Val{0}) = one(x)
@inline literal_pow(::typeof(^), x::Ring, ::Val{1}) = x
@inline literal_pow(::typeof(^), x::Ring, ::Val{-1}) = inv(x)
@inline literal_pow(::typeof(^), x::Ring, ::Val{2}) = x * x
@inline literal_pow(::typeof(^), x::Ring, ::Val{3}) = x * x * x

function power_by_squaring(x::Ring, p::Integer)
    if p == 1
        return x
    elseif p == 0
        return one(x)
    elseif p == 2
        return x * x
    elseif p < 0
        x = inv(x)
        p = -p
    end
    t = trailing_zeros(p) + 1
    p >>= t
    while (t -= 1) > 0
        x *= x
    end
    y = x
    while p > 0
        t = trailing_zeros(p) + 1
        p >>= t
        while (t -= 1) >= 0
            x *= x
        end
        y *= x
    end
    return y
end

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
intpower(a::Integer, b::Integer) = uptype(a, mintype_for(a, b, false))^b

"""
    uptype(a, [T::Type])

promote `a` to get at least type `promote_type(typeof(a), T)`.
"""
uptype(a::T, S::Type = Int) where T = promote_type(S, T)(a)


"""
    num_primitives(::Type{G})

Number of primitive elements (generators of multiplicative group) of GaloisField `G`.
"""
function num_primitives(::Type{G}) where G<:Ring
    iszero(mult_order(G)) ? 0 : Primes.totient(fact_mult_order(G))
end

"""
    isprimitive(g::G)

Return iff `g` is a primitive element of its ring
(its powers form the complete multiplicative subgroup of `G`)
"""
function isprimitive(g::G) where G<:Ring
    iszero(g) && return false
    n = mult_order(G)
    iszero(n) && return false
    fact = fact_mult_order(G)
    _isprimitive(g, n, fact)
end
function _isprimitive(g, n::Integer, fact)
    for p in keys(fact)
        isone(pwr(g, n ÷ p)) && return false
    end
    true
end
function pwr(g::G, x::Integer) where G<:Ring
    g^x
end
function pwr((g, m)::Tuple{G,G}, x::Integer) where G<:Ring
    powermod(g, x, m)
end

"""
    order(z::Ring)

Returns the order of the cyclic multiplicative group generated by z,
or `0` if `z^k != 1` for all integers `k`.
"""
function order(x::G) where G<:Ring
    iszero(x) && return 0
    isone(x) && return 1
    ord = mult_order(G)
    iszero(ord) && return 0
    fact = fact_mult_order(G)
    _order(x, ord, fact)
end

function _order(g, mm::Integer, fact)
    opt = mm
    for (p, k) in fact
        for j = 1:k
            isone(pwr(g, opt ÷ p)) || break
            opt = opt ÷ p
        end
    end
    opt
end

"""
    mult_order(R::Type{<:Ring})

order of multiplicative subgroup of `R`.
"""
mult_order(R::Type) = 0
mult_order(R::Type{<:ZZ}) = 2
mult_order(R::Type{<:ZZmod}) = totient(modulus(R))
mult_order(R::Type{<:GaloisField}) = order(R) - 1
mult_order(R::Type{<:Polynomial}) = mult_order(basetype(R))
function mult_order(R::Type{<:Quotient})
    isirreducible(modulus(R)) ? order(R) - 1 : 0
end

"""
    fact_mult_order(::Type{<:Ring})

Return the Primes factorization of the order of the multiplicative group
"""
fact_mult_order(::Type{G}) where G<:Ring = Primes.factor(mult_order(G))

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
isfield(R::Type{<:Ring}) = category_trait(R) <: FieldTrait

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

Base.mod(a::R, b::R) where R<:Ring = rem(a, b)

"""
    isdiv(a, b)

Return if ring element `a` is dividable by `b` without remainder.
"""
isdiv(a::T, b::T) where T<:Ring = iszero(rem(a, b))

"""
    iscoprime(a, b)

Return if there is no non-unit common divisor of `a` and `b`.
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

"""
    isreducible(p::R)

Return iff `p` is neither `0` nor a unit nor irreducible in `R`.
"""
isreducible(p::Ring) = !iszero(p) && !isunit(p) && !isirreducible(p)

"""
    isirreducible(p::R)

Return iff `p` is neither `0` nor a unit nor a product of non-units of `R`.
"""
isirreducible(a::Integer) = Primes.isprime(abs(a))
isirreducible(a::R) where R<:Ring = isirreducible(a, category_trait(R))

"""
    isprime(p::R)

Return iff p is neither `0` nor a unit and
for any `a,b ∈ R` if `p` divides `a*b` then `p` divides `a` or `p` divides `b`.
"""
isprime(a::R) where R<:Ring = _isprime(a, category_trait(R))
_isprime(a::Ring, ::Type{<:GCDDomainTrait}) = isirreducible(a)

# apply homomorphism
(h::Hom{F,R,S})(a::R) where {F,R,S} = h.f(a)::S

divrem2(a::T, b::T) where T = divrem(a, b)
rem2(a::T, b::T) where T = divrem2(a, b)[2]

function divrem2(a::T, b::T) where T<:FractionRing
    c = div(a, b)
    d, r = divrem2(c.num, c.den)
    d, a - d * b
end

# generic Euclid's algorithm
gcd(a::T, b::T) where T<:Ring = _gcd(a, b, category_trait(T))

function _gcd(a::T, b::T, ::Type{<:UniqueFactorizationDomainTrait}) where T<:Ring
    iszero(b) && return a
    a, b = b, rem2(a, b)
    while !iszero(b)
        d, c = divrem2(a, b)
        if iszero(d)
            a = one(a)
            break
        end
        a, b = b, c
        issimpler(b, a) || throw(DomainError((a, b), "b is not simpler than a"))
    end
    u = lcunit(a)
    isone(a) ? a : a * inv(u)
end

# extension to array
function gcd(aa::Union{AbstractVector{T},Tuple{Vararg{T}}}) where {T<:Ring}
    g = zero(T)
    for x in aa
        isone(g) && break
        g = gcd(x, g)
    end
    g
end
# to be used with non-empty generators
function gcd_generator(aa::Base.Generator)
    vs = iterate(aa)
    g, s = vs
    while (vs = iterate(aa, s)) !== nothing && !isone(g)
        x, s = vs
        g = gcd(x, g)
    end
    g
end
gcd(a::T, b::T...) where T<:Ring = gcd([a; b...])

pgcd(a::R, b::R) where R<:Ring = gcd(a, b)
pgcdx(a::R, b::R) where R<:Ring = (gcdx(a, b)..., one(R))

# generic extended Euclid's algorithm
gcdx(a::T, b::T) where T<:Ring = _gcdx(a, b, category_trait(T))

function _gcdx(a::T, b::T, ::Type{<:UniqueFactorizationDomainTrait}) where T<:Ring
    s0, s1 = one(T), zero(T)
    t0, t1 = s1, s0
    # invariant: a * s0 + b * t0 == gcd(a, b)
    while !iszero(b)
        ##println("gcdx($a, $b) T = $T")
        q, r = divrem2(a, b)
        a, b = b, r
        issimpler(b, a) || throw(DomainError((a, b), "b is not simpler than a"))
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    end
    u = lcunit(a)
    if isone(u)
        a, s0, t0
    else
        a, s0, t0 = a / u, s0 / u, t0 / u
    end
end

function gcdx(a::AbstractVector{T}) where T<:Ring
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
gcdx(a::T, b::T...) where T<:Ring = gcdx([a; b...])

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
        x = rem(x * x, m)
    end
    y = x
    while p > 0
        t = trailing_zeros(p) + 1
        p >>= t
        while (t -= 1) >= 0
            x = rem(x * x, m)
        end
        y = rem(y * x, m)
    end
    return y
end

const SUPERSCRIPTS = Char[
    0x2070,
    0xb9,
    0xb2,
    0xb3,
    0x2074,
    0x2075,
    0x2076,
    0x2077,
    0x2078,
    0x2079,
    0x207a,
    0x207b,
]
const SUBSCRIPTS = Char[
    0x2080,
    0x2081,
    0x2082,
    0x2083,
    0x2084,
    0x2085,
    0x2086,
    0x2087,
    0x2088,
    0x2089,
    0x208a,
    0x208b,
]

tosuper(a::Integer; sign::Bool = false) = _integer_to_script(a, SUPERSCRIPTS, sign)
tosub(a::Integer; sign::Bool = false) = _integer_to_script(a, SUBSCRIPTS, sign)
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

function sort_unique!(A::AbstractVector; rev::Bool = false)
    n = length(A)
    n == 0 && return A
    a = sort!(A; rev = rev)
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
        if a * a * a != a^3
            println(io, "$(a) ^ 3")
        end
    end
    for (a, b, c) in Iterators.product(gg, gg, gg)
        if (a * b) * c != a * (b * c)
            println(io, "assoc * $a $b $c")
        end
        if (a + b) + c != a + (b + c)
            println(io, "assoc + $a $b $c")
        end
        if a * (b + c) != a * b + a * c
            println(io, "distrib $a $b $c")
        end
    end
end
