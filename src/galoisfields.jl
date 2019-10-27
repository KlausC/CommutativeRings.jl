
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

function GF(p::Integer, m::Integer; nr::Integer=1)
    Z = GF(p)
    m > 0 || throw(ArgumentError("exponent m=$m must be positive"))
    if m == 1
        Z
    else
        gen = irreducible(:γ, Z, m, nr)
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

"""
    normalmatrix(a::Q)

Return a square matrix of element type `ZZ/p`, whose colums are the coefficient
vectors of `a^(p^i) for i = 0:r-1`.

Here Q is a galois field of characteristic `p` and order `p^r`.

If `normalmatrix(a))` is regular, the field elements `a^(p^i) for i = 0:r-1` form a
base of `Q` as a vector space over `ZZ/p` (a normal base).
"""
function normalmatrix(a::Q) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    p = characteristic(Q)
    r = deg(modulus(Q))
    M = Matrix{Z}(undef, r, r)
    for i = 0:r-1
        c = a.val.coeff
        k = length(c)
        for j = 1:r
            M[j,i+1] = j <= k ? c[j] : 0
        end
        a ^= p
    end
    M
end

"""
    normalmatrix(::Type{Q})

Return `normalmatrix(a)` for the first `a` in `Q` for which this is regular. 
"""
function normalmatrix(::Type{Q}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    normalmatrix(normalbase(Q))
end

function normalbases(::Type{Q}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    r = deg(modulus(Q))
    Base.Iterators.filter(x->rank(normalmatrix(x)) == r, Q)
end
"""
    normalbase(::Type{Q})

Find the first `a in Q` for which `normalmatrix(a)` is regular.
"""
function normalbase(::Type{Q}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    first(normalbases(Q))
end

import Base: *

"""
    sized(a::Vector, r)

Return a vector of length `r`, which starts with `a` and is filled up with zeros if required.
"""
function sized(a::Vector{Z}, r::Integer) where Z
    n = length(a)
    n == r ? a : n < r ? vcat(a, zeros(Z, r - n)) : a[1:r]
end

function *(M::Matrix{Z}, a::Vector{Z}) where Z<:Ring
    invoke(*, Tuple{AbstractMatrix,AbstractVector}, M, sized(a, size(M, 2)))
end

function *(M::Matrix{Z}, a::Q) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    Q(M * a.val.coeff)
end

"""
    isomorphism(Q, R)

Return a function `iso:Q -> R`, which describes an isomorphism between two galois fields
`Q` and `R` of the same order.
"""
function isomorphism(::Type{Q}, ::Type{R}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P},Y,R<:Quotient{Y,P}}
    characteristic(Q) == characteristic(R) || throw(ArgumentError("both fields have different characteristics"))
    order(Q) == order(R) || throw(ArgumentError("both fields have different orders"))
    f = normalbase(Q)
    M = normalmatrix(f)
    r = deg(modulus(Q))
    k = characteristic(Q) == 2 ? 3 : 2
    nrep(M, f) = (inv(M) * f^k).val
    h = nrep(M, f)
    for g in R
        N = normalmatrix(g)
        if rank(N) == r && nrep(N, g) == h
            M1 = inv(M)
            iso(a::Q) = R(N * (M1 * a.val.coeff))
            return iso
        end
    end
    throw(ErrorException("no isomorphism found - not reachable"))
end

