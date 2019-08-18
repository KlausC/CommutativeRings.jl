
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
   
# alternative implemention
function irreducibles_sets(Z::Type{<:ZZmod}, n::Integer)
    collect(setdiff(Set(monic(Z, n)), products(Z, n)))
end
# set of all products of monic polynomials of degrees summing up to `n`.
products(Z, n) = union(products.(Z, n, 1:n÷2)...)
products(Z, n, k) = Set([p * q for p in monic(Z, k) for q in monic(Z, n-k)])
# all monic polynomials
monic(Z::Type{<:ZZmod}, n) = Z[:x].([[p; 1] for p in poldeg(modulus(Z),n)])
# generate polynomial coefficients for all possible polynomials of degree `n`
# and modulus `m`.
function poldeg(m::Integer, n::Integer)
    n == 0 && return [typeof(m)[]]
    pd = poldeg(m, n-1)
    [ [p; j] for p in pd for j in 0:m-1]
end

export irreducibles
"""
    irreducibles(ZZp, n)

Calculate all irreducible monic polynomials of degree `n` over `ZZp <:ZZmod`.
The method is brute-force, so the degree and modulus should reasonably sized.
"""
function irreducibles(Z::Type{<:ZZmod}, n::Integer)
    ev(p::UnivariatePolynomial) = evaluate.(p, 0:modulus(Z))
    filter(x->(all(!iszero, ev(x))), CommutativeRings.monic(Z, n))
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
        P = Z[:x]
        gen = irreducibles(Z, m)[1]
        P / gen
    end
end

