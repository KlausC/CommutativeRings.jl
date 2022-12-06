
export cyclotomic
export jacobi, kronecker, moebius, necklace

using Primes

"""
    cyclotomic(P, n)

Calculate `n`th cylotomic polynomial in polynom ring `P` over the integers.
This polynom is defined to be the unique irreducible divisor of `x^n - 1`,
which is coprime to all `x^k - 1` with `k < n`.

If `n` is prime, `cyclotomic(P, n) = (x^n - 1) / (x - 1).

If `n` is squarefree (product of distinct primes `p1 * p2 * ... * pk`)
and `c_k(x) = cyclotomic(P, p1*...*pk)` we use the recursion formula
` c_(k+1)(x) = c_k(x^pk) / c_k(x)`.

If `v = p1*...*pk` with the distinct prime factors of `n`, we have
`cyclotomic(P, n)(x) = cyclotomic(P, v)(x^(n/v))`.
"""
function cyclotomic(::Type{P}, n::Integer) where P<:UnivariatePolynomial
    T = basetype(P)
    (n < 2 || isprime(n)) && return P(ones(T, n))
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
    n & 1 == 0 && k & 1 == 0 && return 0
    k == 0 && return n == 1 || n == -1 ? 1 : 0
    ks = k < 0 && n < 0 ? -1 : 1
    if k < 0
        k = -k
    end
    t = trailing_zeros(k)
    k >>= t
    ks = (n & 7 == 3 || n & 7 == 5) && t & 1 == 1 ? -ks : ks
    jacobi(n, k) * ks
end

# moebius function
function moebius(n::Integer)
    n > 0 || throw(ArgumentError("moebius defined for positive integers only"))
    n == 1 && return 1
    f = Primes.factor(n)
    if maximum(values(f)) == 1
        ifelse(isodd(length(f)), -1, 1)
    else
        0
    end
end

# necklace polynomial - Moreau's necklace-counting function
"""
    necklace(q, n)

Return the value of the `necklace polynomial` of order `n` at `q`.

Return count of irreducible monic polynomials of degree `n` over `ZZ/x`.
"""
necklace(q::RingInt, n::Integer) = n == 0 ? one(q) : _necklace(q, Int(n))
@inline function _necklace(q, n::Int)
    f = Primes.factor(n)
    p = collect(keys(f))
    m = length(p)
    s = q^n
    for x = 1:(2^m-1)
        d = n
        μ = 1
        k = 1
        while x != 0
            if x & 1 == 1
                d ÷= p[k]
                μ = -μ
            end
            x >>= 1
            k += 1
        end
        s += q^d * μ
    end
    div(s, n)
end
