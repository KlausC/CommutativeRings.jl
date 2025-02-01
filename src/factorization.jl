
using Primes
import Primes.factor
import Random: rand, SamplerType, AbstractRNG
export factor

"""
    num_irreducibles(::Type{<:UnivariatePolynomial{F}}, r)

Number of irreducible polynomials over `F` of degree `r`.
"""
function num_irreducibles(::Type{<:UnivariatePolynomial{G}}, r::Integer) where G
    k = order(G)
    iszero(k) && throw(ArgumentError("order of base type is zero"))
    T = mintype_for(k, r, false)
    necklace(T(k), r)
end
function num_irreducibles(::Type{G}, r) where G<:Ring
    num_irreducibles(G[:x], r)
end

"""
    isirreducible(p::F[X])

Returns iff `p` is an irreducible (prime) polynomial over field `F`. See also `factor`.
"""
function isirreducible(
    p::UnivariatePolynomial{F},
    ::Type{<:EuclidianDomainTrait},
) where F<:QuotientRing
    (iszero(p) || isunit(p)) && return false
    deg(p) <= 1 && return true
    iszero(p.coeff[1]) && return false
    pp = gcd(p, derive(p))
    deg(pp) > 0 && return false
    isddf(p)
end

import Base.Iterators: Filter, take, drop
"""::UnivariatePolynomial{<:QuotientRing}
    irreducible(P, n, nr=0)

Returns an irreducible polynomial with in `P` with degree `n`. Skip first `nr` hits.
"""
irreducible(::Type{P}, n) where P<:UnivariatePolynomial = first(irreducibles(P, n))
function irreducible(::Type{P}, n, nr::Integer) where P<:UnivariatePolynomial
    first(drop(irreducibles(P, n), nr))
end
"""
    reducible(P, n, nr=0)

Returns a reducible polynomial with in `P` with degree `n`. Skip first `nr` hits.
"""
reducible(::Type{P}, n) where P<:UnivariatePolynomial = first(reducibles(P, n))
function reducible(::Type{P}, n, nr::Integer) where P<:UnivariatePolynomial
    first(drop(reducibles(P, n), nr))
end
"""
    irreducibles(P, n)

Returns iterator of all irreducible monic polynomials in `P` with degree `n`.
"""
function irreducibles(::Type{P}, n) where P<:UnivariatePolynomial{<:Ring}
    Base.Iterators.Filter(isirreducible, Monic(P, n))
end
"""
reducibles(P, n)

Returns iterator of all reducible monic polynomials in `P` with degree `n`.
"""
function reducibles(::Type{P}, n) where P<:UnivariatePolynomial{<:Ring}
    Base.Iterators.Filter(!isirreducible, Monic(P, n))
end

"""
    factor(p::F[:x])

Factorize polynomial in `F[X]` where `F` is a field
(`ZZ/p` or `GF(p,m)` with `p` prime number).
"""
function factor(p::P) where P<:UnivariatePolynomial{<:QuotientRing}
    res = Pair{P,Int}[]
    u = lcunit(p)
    if !isone(u)
        p /= u
        push!(res, P(u) => 1)
    end
    if deg(p) <= 1
        if !isone(p) || isempty(res)
            push!(res, p => 1)
        end
        return res
    end
    pp = sff(p)
    for (q, k) in pp
        qq = ddf(q)
        for (r, l) in qq
            rr = edf(r, l)
            for s in rr
                push!(res, s => k)
            end
        end
    end
    sort!(res)
end

"""
    sff(p)

`Square-free factorization`.

Factor polynomial `p` into into coprime squarefree factors `u_i for i = 1:e`
such that `p = u_1^1 * u_2^2 * ... * u_e^e`.

Return an array of pairs of squarefree factors and corresponding powers.
The implementation depends on the characteristic of the Ring.

For characteristic 0 see:
`https://en.wikipedia.org/wiki/Square-free_polynomial#Yun's_algorithm`

For characteristic > 0 see:
`https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields#Square-free_factorization`
"""
function sff(f::UnivariatePolynomial{R}) where R
    _sff(f, Val(characteristic(R)))
end

function _sff(f::P, vch::Val{p}) where {p,P<:UnivariatePolynomial}
    @assert p > 0
    i = 1
    R = Pair{P,Int}[]
    fs = derive(f)
    c = gcd(f, fs) # c contains all multiple factors of f
    w = f / c # w is square-free
    while !isunit(w)
        y = gcd(w, c)
        z = w / y
        if deg(z) > 0
            push!(R, Pair(z, i))
        end
        c /= y
        w = y
        i += 1
    end

    if deg(c) > 0
        c = proot(c)
        for (g, i) in _sff(c, vch)
            push!(R, Pair(g, i * p))
        end
    end
    R
end
"""
    proot(p)

Calculate the `p`-th root of a polynomial over a field with characteristic `p != 0`.
"""
function proot(g::P) where {R,P<:UnivariatePolynomial{R}}
    p = characteristic(R)
    r = p^(dimension(R) - 1)
    compress(P([x^r for x in coeffs(g)]), p)
end

"""
    compress(p, n)

Return polynomial `q` with `q(x^n) == p(x)`.

Assuming `p` has this form. `compress(uncompress(p) == p`.
"""
function compress(p::P, n::Integer) where P<:UnivariatePolynomial
    r = (size(p.coeff, 1) + n - 1) ÷ n - 1
    nc = [p.coeff[k*n+1] for k ∈ 0:r]
    P(nc, ord(p) ÷ n)
end

"""
    uncompress(p, n)

Return polynomial `p(x^n)`.

Same as [`spread`](@ref)
"""
function uncompress(p::P, n::Integer) where {R,P<:UnivariatePolynomial{R}}
    r = length(p.coeff)
    nc = zeros(R, (r - 1) * n + 1)
    for k = 0:r-1
        nc[k*n+1] = p.coeff[k+1]
    end
    P(nc, ord(p) * n)
end

"""
    ddf(p)

`Distinct-degree factorization`.
Input is a squarefree polynomial.
Returns a list of pairs `g_i => d_i` of polynomials g_i, each of which is a product of
all irreducible monic polynomials of equal degree `d_i`. The product of all `g_i == p`.
"""
function ddf(f::P) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    S = Pair{P,Int}[]
    x = monom(typeof(f), 1)
    i = 1
    fs = f
    xqi = x
    while deg(fs) >= 2i
        xqi = powermod(xqi, q, fs)
        g = gcd(fs, xqi - x)
        if deg(g) > 0
            push!(S, Pair(g, i))
            fs /= g
        end
        i += 1
    end
    if deg(fs) > 0
        push!(S, Pair(fs, deg(fs)))
    end
    if isempty(S)
        push!(S, Pair(f, 1))
    end
    S
end

function isddf(f::P) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    x = monom(typeof(f), 1)
    i = 1
    fs = f
    xqi = x
    while deg(fs) >= 2i
        xqi = powermod(xqi, q, fs)
        g = gcd(fs, xqi - x)
        deg(g) > 0 && return false
        i += 1
    end
    return true
end

"""
    edf(p::Polynomial, d::Integer)

`Equal-degree factorization`.
Algorithm of Cantor-Zassenhaus to find the factors of `p`, a product of monomials of
degree `d`. (Such polynomials are in the output of `ddf`).
The base type for `p` must be a finite field. Odd charcteristic is a covered special case.
"""
function edf(f::P, d::Integer) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    n = deg(f)
    S = [f]
    n == d && return S
    rem(n, d) == 0 || throw(DomainError((n, d), "degree of f must be multiple of d = $d"))
    ex = big(q)^d ÷ 2 # isodd(q) ? (q^d - 1) ÷ 2 : (q^d ÷ 2)
    r = div(n, d)
    power = isodd(q) ? powermod : powersum
    while length(S) < r
        h = P(rand(Z, n))
        s = length(S)
        g = power(h, ex, f) - 1
        for k = 1:s
            u = S[k]
            gu = gcd(g, u)
            if 0 < deg(gu) < deg(u)
                S[k] = gu
                push!(S, u / gu)
            end
        end
    end
    S
end

"""
    powersum(h, ex, f)

Calculate the sum `h + h^2 + h^4 + h^8 + ... + h^ex mod f`
"""
function powersum(h, ex, f)
    s = h
    n = 1
    while n < ex
        h = rem(h * h, f)
        n *= 2
        s += h
    end
    s
end

# random samplers for finite rings
function rand(r::AbstractRNG, ::SamplerType{Z}) where {Z<:ZZmod}
    m = modulus(Z)
    Z(rand(r, 0:m-1))
end
# Random field element of `Q = P / (polynomial)`, whith `basetype(P) <: ZZmod`.
function rand(
    r::AbstractRNG,
    ::SamplerType{Q},
) where {Z,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}

    m = deg(modulus(Q))
    r = Q(P(rand(r, Z, m)))
end

function Base.isless(p::T, q::T) where T<:Pair{<:Ring,<:Integer}
    first(p) < first(q) || first(p) == first(q) && second(p) == second(q)
end

import Base: prod
function Base.prod(ff::Vector{<:Pair{T,<:Integer}}) where T<:Ring
    res = one(T)
    for p in ff
        res *= first(p)^p.second
    end
    res
end
