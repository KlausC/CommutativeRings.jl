
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
function GF(p::Integer)
    isprime(p) || throw(ArgumentError("p=$p is not prime"))
    typeof(p) / p
end

function GF(p::Integer, m::Integer)
    Z = GF(p)
    m > 0 || throw(ArgumentError("exponent m=$m must be positive"))
    if m == 1
        Z
    else
        gen = irreducible(:γ, Z, m)
        typeof(gen) / gen
    end
end

function Base.show(io::IO, q::Q) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}

    m = deg(modulus(Q))
    p = modulus(Z)
    c = q.val.coeff
    n = length(c)
    cc(i) = i > n ? 0 : c[i].val
    print(io, '{', cc(m))
    for k = m-1:-1:1
        print(io, ':', cc(k))
    end
    print(io, '%', p, '}')
end

