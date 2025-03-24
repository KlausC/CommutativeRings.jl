
export cyclotomic
export jacobi, kronecker, moebius, necklace, carmichael, fibonacci, lucas

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
    n < 0 && throw(ArgumentError("Index of cyclotomic polynomial is negative"))
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

"""
    jacobi(k, n)

Calculate Jacobi symbol of `k` over `n`. `0 < n && isodd(n)`, `jacobi(k, n) ∈ {-1, 0, 1}`.
"""
function jacobi(k::Integer, n::Integer)
    n > 0 && n & 1 == 1 || throw(DomainError(n, "k must be positive odd number"))
    k = mod(k, n)
    t = 1
    while k != 0
        while k & 1 == 0
            k >>= 1
            r = n & 7
            if r == 3 || r == 5
                t = -t
            end
        end
        k, n = n, k
        if k & 3 == n & 3 == 3
            t = -t
        end
        k = mod(k, n)
    end
    n == 1 ? t : 0
end

"""
    kronecker(k, n)

Calculate Kronecker symbol of `k` over `n`. Generalization of `jacobi` without
restrictions to `n` or `k`. kronecker(k, n) ∈ {-1, 0, 1}`
"""
function kronecker(k::Integer, n::Integer)
    k & 1 == 0 && n & 1 == 0 && return 0
    n == 0 && return k == 1 || k == -1 ? 1 : 0
    ks = n < 0 && k < 0 ? -1 : 1
    if n < 0
        n = -n
    end
    t = trailing_zeros(n)
    n >>= t
    ks = (k & 7 == 3 || k & 7 == 5) && t & 1 == 1 ? -ks : ks
    jacobi(k, n) * ks
end

"""
    moebius(n)

Calculate Moebius function of `n`.
"""
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

"""
    necklace(q, n)

Return the value of the `necklace polynomial` of order `n` at `q`.

Return count of irreducible monic polynomials of degree `n` over `ZZ/x`.

Sometimes also called "Moreau's necklace-counting function".
The necklace polynomial of degree in polynomial ring `R` is obtained by calling
`necklace(monomial(R), n)`.
"""
necklace(q::Base.BitInteger, n::Integer) = n == 0 ? one(q) : _necklace(q, intpower(q, n), Int(n))
necklace(q::Union{BigInt,RingInt}, n::Integer) = n == 0 ? one(q) : _necklace(q, q^n, Int(n))
@inline function _necklace(q, s, n::Int)
    q = oftype(s, q)
    f = Primes.factor(n)
    p = collect(keys(f))
    m = length(p)
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
    _div(s, n)
end
_div(s, n) = div(s, n)
_div(s::UnivariatePolynomial{Z,X}, n) where {X,Z<:ZZ} = QQ[X](s) / n

"""
    carmichael(n::Integer)

Return the Carmichael λ-function value at of `n`, also called the `reduced totient`.

It is a divisor of the Euler ϕ-function (aka `totient`).
"""
function carmichael(n::T) where T<:Integer
    n <= 0 && throw(ArgumentError("Carmichael λ($n) is not defined"))
    f = factor(n)
    res = one(T)
    for (p, r) in f
        pp = convert(T, p)
        t = p == 2 && r > 2 ? pp^(r - 2) : pp^(r - 1) * (pp - 1)
        res = lcm(res, t)
    end
    res
end

"""
    fibonacci(n)

Calculate the n^th Fibonacci number `F_n`. (`F_0 = 0, F_1 = 1, F_n+1 = F_n + F_n-1`)
Valid for all integer `n`.

Algorithm by D. Takahashi / Information Processing Letters 75 (2000) 243–246
"""
function fibonacci(n::Integer)
    s = n >= 0 ? 1 : 2isodd(n) - 1
    n = abs(n)
    if n == 0
        return big(0)
    elseif n <= 2
        return big(s)
    else
        f = big(1)
        l = big(1)
        sign = -1
        log2n = ilog2(n)
        mask = oftype(n, 2)^(log2n - 1)
        for _ = 1:log2n-1
            temp = f * f
            f = (f + l) ÷ 2
            f = 2 * (f * f) - 3 * temp - 2 * sign
            l = 5 * temp + 2 * sign
            sign = 1
            if (n & mask) != 0
                temp = f
                f = (f + l) ÷ 2
                l = f + 2 * temp
                sign = -1
            end
            mask = mask ÷ 2
        end
        if (n & mask) == 0
            f = f * l
        else
            f = (f + l) ÷ 2
            f = f * l - sign
        end
        return f * s
    end
end

"""
    lucas(n)

Calculate the n^th Lucas number `L_n`. (`L_0 = 2, L_1 = 1, L_n+1 = L_n + L_n-1`)
"""
lucas(n) = 2fibonacci(n) + fibonacci(n - 3)
