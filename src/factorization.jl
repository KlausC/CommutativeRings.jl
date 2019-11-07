
using Primes
import Primes.factor
import Random: rand, SamplerType, AbstractRNG
export factor

"""
    isirreducible(p::F[X])

Returns iff `p` is an irreducible (prime) polynomial over field `F`. See also `factor`.
"""
function isirreducible(p::P) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    deg(p) <= 1 && return true
    iszero(p.coeff[1]) && return false
    pp = gcd(p, derive(p))
    deg(pp) > 0 && return false
    isddf(p)
end

import Base.Iterators: Filter, take, drop
"""
    irreducibles(X, F, n)

Returns array of all irreducible monic polynomials with variable `X` of degree `n`
over field `F`.

    irreducible(X, F, n)

Returns an irreducible polynomial with variable 'X' of degree `n`.
"""
irreducible(X, ::Type{Z}, n) where Z = first(irreducible_filter(X, Z, n))
irreducible(X, ::Type{Z}, n, nr::Integer) where Z = first(drop(irreducible_filter(X, Z, n), nr))
irreducibles(X, ::Type{Z}, n) where Z = collect(irreducible_filter(X, Z, n))
function irreducible_filter(X, ::Type{Z}, n) where Z<:QuotientRing
    Base.Iterators.Filter(isirreducible, Monic(X, Z, n))
end

"""
    factor(p::F[:x])

Factorize polynomial in `F[X]` where `F` is a field
(`ZZ/p` or `GF(p,m)` with `p` prime number).
"""
function factor(p::P) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    res = Pair{P,Int}[]
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
    sort(res)
end

"""
    sff(p)

`Square-free factorization`.
Algorithm to split polynomial `p` into a product of powers of squarefree factors.
Return an array of pairs of squarefree factors and corresponding powers.
"""
function sff(f::P) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    q = order(Z)
    p = characteristic(Z)
    i = 1
    R = Pair{P,Int}[]
    fs = derive(f)
    c = gcd(f, fs) # c contains all multiple factors of f
    w = f / c # w is square-free
    while !isunit(w)
        y = gcd(w, c)
        z = w / y
        if !isone(z)
            push!(R, Pair(z, i))
        end
        c /= y
        w = y
        i += 1
    end
    
    if !isone(c)
        c = shrink(c, p)
        for (g, i) in sff(c)
            push!(R, Pair(g, i * p))
        end
    end
    R
end

# assuming p(x) = q(x^p), return q. Formally q(x) = p(x^(1/p)).
function shrink(a::P, p::Integer) where P<:UnivariatePolynomial
    n = deg(a)
    c = similar(a.coeff, (n÷p)+1)
    for k = 0:n÷p
        c[k+1] = a.coeff[p*k+1]
    end
    P(c)
end

"""
    ddf(p)

`Distinct-degree factorization`.
Input is a squarefree polynomial.
Returns a list of pairs `g_i => d_i` of polynomials g_i, each of which is a product of
all irreducible monic polynomials of equal degree `d_i`. The product of all `g_i == p`.
"""
function ddf(f::P) where {X,Z<:QuotientRing, P<:UnivariatePolynomial{X,Z}}
    q = order(Z)
    S = Pair{P, Int}[]
    x = monom(typeof(f), 1)
    i = 1
    fs = f
    xqi = x
    while deg(fs) >= 2i
        xqi = powermod(xqi, q, fs)
        g = gcd(fs, xqi - x)
        if !isone(g)
            push!(S, Pair(g, i))
            fs /= g
        end
        i += 1
    end
    if !isone(fs)
        push!(S, Pair(fs, deg(fs)))
    end
    if isempty(S)
        push!(S, Pair(f, 1))
    end
    S
end

function isddf(f::P) where {X,Z<:QuotientRing, P<:UnivariatePolynomial{X,Z}}
    q = order(Z)
    x = monom(typeof(f), 1)
    i = 1
    fs = f
    xqi = x
    while deg(fs) >= 2i
        xqi = powermod(xqi, q, fs)
        g = gcd(fs, xqi - x)
        isone(g) || return false
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
function edf(f::P, d::Integer) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    q = order(Z)
    n = deg(f)
    S = [f]
    n == d && return S
    rem(n, d) == 0 || throw(DomainError((n, d), "degree of f must be multiple of d = $d"))
    ex = q^d ÷ 2 # isodd(q) ? (q^d - 1) ÷ 2 : (q^d ÷ 2)
    r = div(n, d)
    while length(S) < r
        h = P(rand(Z, n))
        g = (q & 1 == 1 ? powermod : powersum)(h, ex, f) - 1
        s = length(S)
        for k = 1:s
            u = S[k]
            gu = gcd(g, u)
            if !isone(gu) && gu != u
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
function rand(r::AbstractRNG, ::SamplerType{Q}) where 
    {X,Y,Z,P<:UnivariatePolynomial{X,Z},Q<:Quotient{Y,P}}
    
    m = deg(modulus(Q))
    r = Q(P(rand(r, Z, m)))
end

function Base.isless(p::T, q::T) where T<:Pair{<:Ring,<:Integer}
    p.first < q.first ||
    p.first == q.first && p.second == q.second
end

import Base: prod
function Base.prod(ff::Vector{<:Pair{T,<:Integer}}) where T<:Ring
    res = one(T)
    for p in ff
        res *= p.first^p.second
    end
    res
end

