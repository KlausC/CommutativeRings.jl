
export cyclotomic
using Primes: isprime, factor
"""
    cyclotomic(P, n)

Calculate cylotomic polynomial of degree `n` in polynom ring `P`.
This polynom is defined to be the disisor of `x^n - 1`, which is coprime to
all `x^k - 1` with `k < n`.

If `n` is prime, `cyclotomic(P, n) = (x^n - 1) / (x - 1).

If `n` is squarefree (product of distinct primes `p1 * p2 * ... * pk`)
and `c_k(x) = cyclotomic(P, p1*...*pk)` we use the recursion formula
` c_(k+1)(x) = c_k(x^pk) / c_k(x)`.

If `v = p1*...*pk` with the distinct prime factors of `n`, we have
`cyclotomic(P, n)(x) = cyclotomic(P, v)(x^(n/v))`.
"""
function cyclotomic(::Type{P}, n::Integer) where P<:UnivariatePolynomial
    (n < 2 || isprime(n)) && return P(ones(basetype(P), n))
    T = basetype(P)
    f = factor(n)
    l = length(f)
    v = collect(keys(f))
    v1 = prod(v)
    q = P(ones(T, v[1]))
    for k = 2:l
        q = div(spread(q, v[k]), q)
    end
    n == v1 ? q : spread(q, n ÷ v1)
end
   
# all monic polynomials
monic(Z::Type{<:ZZmod}, n) = Z[:x].([[p; 1] for p in poldeg(modulus(Z),n)])
# generate polynomial coefficients for all possible polynomials of degree `n`
# and modulus `m`.
function poldeg(m::Integer, n::Integer)
    n == 0 && return [typeof(m)[]]
    pd = poldeg(m, n-1)
    [ [p; j] for p in pd for j in 0:m-1]
end

import Base: length, iterate, eltype
export Monic

struct Monic{X,T<:QuotientRing}
    n::Int
    Monic(X::Symbol, ::Type{T}, n) where T = new{X,T}(n)
end
eltype(mo::Type{Z}) where Z<:Ring = Z
function iterate(m::Type{Z}) where Z<:QuotientRing
    z = zero(Z)
    (z, z)
end
length(mo::Type{Z}) where Z<:ZZmod = modulus(Z)
function iterate(m::Type{Z}, s) where Z<:ZZmod
    v = s + 1
    iszero(v) ? nothing : (v, v)
end
function length(mo::Type{Q}) where {X,Y,Z<:ZZmod,P<:UnivariatePolynomial{X,Z},Q<:Quotient{Y,P}}
    modulus(Z)^deg(modulus(Q))
end
function iterate(mo::Type{Q}, s) where {X,Y,Z<:ZZmod,P<:UnivariatePolynomial{X,Z},Q<:Quotient{Y,P}}
    c = copy(s.val.coeff)
    m = length(c)
    n = deg(modulus(Q))
    for i = 1:m
        ci = iterate(Z, c[i])
        if ci != nothing
            c[i] = ci[1]
            z = Q(c)
            return (z, z)
        else
            c[i] = zero(Z)
        end
    end
    if m < n
        resize!(c, m+1)
        c[m+1] = one(Z)
        m >= 1 && (c[m] = zero(Z))
        z = Q(c)
        return (z, z)
    end
    nothing
end

Base.length(mo::Monic{X,Z}) where {X,Z<:Ring} = length(Z)^mo.n
Base.eltype(mo::Monic{X,Z}) where {X,Z<:Ring} = Z[X]
function Base.iterate(mo::Monic{X,Z}) where {X,Z<:Ring}
    p0 = monom(Z[X], mo.n)
    p0, p0
end
function Base.iterate(mo::Monic{X,Z}, s) where {X,Z<:Ring}
    c = copy(s.coeff)
    n = deg(s)
    for i = 1:n
        ci = iterate(Z, c[i])
        if ci != nothing
            c[i] = ci[1]
            z = Z[X](c)
            return (z, z)
        else
            c[i] = zero(Z)
        end
    end
    nothing
end
    





export irreducibles
"""
    irreducibles(ZZp, n)

Calculate all irreducible monic polynomials of degree `n` over `ZZp <:ZZmod`.
The method is brute-force, so the degree and modulus should reasonably sized.
"""
function withoutzeros(Z::Type{<:ZZmod}, n::Integer)
    ev(p::UnivariatePolynomial) = evaluate.(p, 0:modulus(Z))
    filter(x->(all(!iszero, ev(x))), monic(Z, n))
end

function isirreducible1(p::P, ip=Vector{P}[]) where {X,Z,P<:UnivariatePolynomial{X,Z}}
    c = p.coeff[1]
    c != 0 || return false
    m = modulus(Z)
    for b = 1:m-1
        iszero(rem(c, gcd(b, m))) || continue
        iszero(p(b)) && return false
    end
    n = deg(p)
    n <= 3 && return true
    for m = 2:n÷2
        while length(ip) < m-1
            push!(ip, irreducibles1(Z, 2+length(ip), ip))
        end
        ipk = ip[m-1]
        for pk in ipk
            b = pk.coeff[1]
            iszero(rem(c, gcd(b, m))) || continue
            iszero(rem(p, pk)) && return false
        end
        m = length(ip)
    end
    return true
end

function irreducibles1(::Type{Z}, n) where {X,Z<:ZZmod}
    P = UnivariatePolynomial{:x,Z}
    irreducibles1(Z, n, Vector{P}[])
end

function irreducibles1(::Type{Z}, n, ip::Vector{Vector{P}}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{X,Z}}
    m = modulus(Z)
    println("irreducibles(ZZ/$m,$n)")
    n <= 3 && return withoutzeros(Z, n)
    pol = CommutativeRings.monic(Z, n)
    filter(isirreducible, pol)
end

function irreducible_filter(X, ::Type{Z}, n) where Z<:QuotientRing
    Filter(isirreducible, Monic(X, Z, n))
end
irreducibles(X, ::Type{Z}, n) where Z = collect(irreducible_filter(X, Z, n))

"""
    factorise(p::ZZmod[:x])

For a prime modulus, factorize polynomial in (ZZ/p)[x]`.
"""
function factorise1(p::P) where {X,Z<:ZZmod,P<:UnivariatePolynomial{X,Z}}
    m = modulus(Z)
    isprime(m) || throw(ArgumentError("modulus must be prime"))
    n = deg(p)
    n < 2 && return [p]
    c = p.coeff[1]
    x = monom(P, 1)
    iszero(c) && return vcat(x, factorise1(div(p, x)))
    for b in 1:m-1
        if iszero(rem(c, gcd(b, m))) && iszero(p(Z(b)))
            return vcat(x - b, factorise1(div(p, x - b)))
        end
    end
    ip = [irreducibles(Z, k) for k = 2:n÷2]
    for ipk in ip, pk in ipk
        b = pk.coeff[1]
        if iszero(rem(c, gcd(b, m)))
            d, r = divrem(p, pk)
            if iszero(r)
                return vcat(pk, factorise1(d))
            end
        end
    end
    return [p]
end

export GF
"""
    GF(p[, m=1])

Return a representation for Galois Field `GF(p, m)`. `p` must be a prime number and
`m` a positive integer.

If `m == 1`, `ZZmod{p}` is returned,
otherwise an irreducible polynomial `g ∈ ZZmod{p}[:x] and deg(g) == m` is generated and
`ZZmod{p}[:x]/(g)` is returned.

Elements of the field can be created like
```´
    GF7 = GF(7)
    GF7(5)  # or
    GF53 = GF(5, 3)
    GF53([1,2,3])
```
"""
function GF(p::Integer, m::Integer=1)
    isprime(p) || throw(ArgumentError("p=$p is not prime"))
    m > 0 || throw(ArgumentError("exponent m=$m must be positive"))
    Z = typeof(p) / p
    if m == 1
        Z
    else
        gen = first(irreducible_filter(:γ, Z, m))
        typeof(gen) / gen
    end
end


export sff, ddf

"""
    sff(p)

Squarefree factorization of p.
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

function shrink(a::P, p::Integer) where P<:UnivariatePolynomial
    n = deg(a)
    c = similar(a.coeff, (n÷p)+1)
    for k = 0:n÷p
        c[k+1] = a.coeff[p*k+1]
    end
    P(c)
end


order(::Type{Z}) where Z<:ZZmod = modulus(Z)
function order(::Type{T}) where {m,X,Z<:ZZmod,T<:Quotient{m,UnivariatePolynomial{X,Z}}}
    modulus(Z) ^ deg(modulus(T))
end
characteristic(::Type{Z}) where Z<:ZZmod = modulus(Z)
function characteristic(::Type{T}) where {m,X,Z<:ZZmod,T<:Quotient{m,UnivariatePolynomial{X,Z}}}
    modulus(Z)
end

"""
    ddf(p)

Input is a squarefree polynomial.
Output is a list of polynomials `g_i, d_i`, each of which is a product of all irreducible
monic polynomials of equal degree `d_i`. The product of all `g_i == p`.
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

# random samplers
import Random: rand, SamplerType, AbstractRNG
function rand(r::AbstractRNG, ::SamplerType{Z}) where {Z<:ZZmod}
    m = modulus(Z)
    Z(rand(r, 0:m-1))
end
"""
    rand(Q)

Random field element of `Q = P / (polynomial)`, whith `basetype(P) <: ZZmod`.
E.g. the Galois fields.
"""
function rand(r::AbstractRNG, ::SamplerType{Q}) where {X,Y,Z<:ZZmod,P<:UnivariatePolynomial{X,Z},Q<:Quotient{Y,P}}
    m = deg(modulus(Q))
    p = modulus(Z)
    r = Q(P(rand(r, 0:p, m)))
end

"""
    cantor(p::Polynomial, d::Integer)

Algorithm of Cantor-Zassenhaus to find the factors of `p`, a product of monomials of
degree `d`. (Such polynomials are in the output of by `ddf`.
The base type for `p` must be a field of odd degree.
"""
function cantor(f::P, d::Integer) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    q = order(Z)
    n = deg(f)
    S = [f]
    n == d && return S
    rem(n, d) == 0 || throw(DomainError((n, d), "degree of f must be multiple of d = $d"))
    ex = isodd(q) ? (q^d - 1) ÷ 2 : (q^d ÷ 2)
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

function factorise(p::P) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    res = Pair{P,Int}[]
    pp = sff(p)
    for (q, k) in pp
        qq = ddf(q)
        for (r, l) in qq
            rr = cantor(r, l)
            for s in rr
                push!(res, s => k)
            end
        end
    end
    res
end

function isirreducible(p::P) where {X,Z<:QuotientRing,P<:UnivariatePolynomial{X,Z}}
    deg(p) <= 1 && return true
    iszero(p.coeff[1]) && return false
    pp = gcd(p, derive(p))
    deg(pp) > 0 && return false
    isddf(p)
end

# Jacobi symbol
function jacobi(n::Integer, k::Integer)
    k > 0 && k & 1 == 1 || throw(DomainError(k, "k must be positive odd number"))
    n = mod(n, k)
    t = 1
    while n != 0
        while n & 1 == 0
            n >>= 1
            r = k & 7
            if r == 3 || r == 5
                t = -t
            end
        end
        n, k = k, n
        if n & 3 == k & 3 == 3
            t = -t
        end
        n = mod(n, k)
    end
    k == 1 ? t : 0
end

# Kronecker symbol
function kronecker(n::Integer, k::Integer)
    n&1 == 0 && k&1 == 0 && return 0
    k == 0 && return n == 1 || n == -1 ? 1 : 0
    ks = k < 0 && n < 0 ? -1 : 1
    if k < 0
        k = -k
    end
    t = trailing_zeros(k)
    k >>= t
    ks = (n&7 == 3 || n&7 == 5 ) && t&1 == 1 ? -ks : ks
    jacobi(n, k) * ks
end

