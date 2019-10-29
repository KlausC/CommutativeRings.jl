
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
    normalmatrix(a::Q[, m])

Return a matrix of element type `ZZ/p`, whose colums are the coefficient
vectors of `a^(p^i) for i = 0:m-1`.

Here Q is a galois field of characteristic `p` and order `p^r`.

`m` m defaults to `r`.

If `normalmatrix(a))` is regular, the field elements `a^(p^i) for i = 0:r-1` form a
base of `Q` as a vector space over `ZZ/p` (a normal base).
"""
function normalmatrix(a::Q, m::Integer=0) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    p = characteristic(Q)
    r = deg(modulus(Q))
    m = m <= 0 ? r : m
    M = Matrix{Z}(undef, r, m)
    for i = 0:m-1
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
    normalmatrix(::Type{Q}[, m])

Return `normalmatrix(a, m)` for the first `a` in `Q` for which this ihas maximal rank. 
"""
function normalmatrix(::Type{Q}, m::Integer=0) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    normalmatrix(normalbase(Q), m)
end

function normalbases(::Type{Q}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    r = deg(modulus(Q))
    Base.Iterators.filter(x->rank(normalmatrix(x, r)) == r, Q)
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

    r = deg(modulus(Q))
    s = deg(modulus(R))
    mod(s, r) == 0 || throw(ArgumentError("dimension of Q ($r) must divide that of R ($s)"))
    f = normalbase(Q)
    M = normalmatrix(f, r)
    p = characteristic(Q)
    k = p == 2 ? 3 : 2
    h = (inv(M) * f^k).val.coeff
    for g in R
        N = normalmatrix(g, r)
        if g^k == R(N * h) && R(view(N,:,r))^p == R(view(N,:,1)) && rank(N) == r
            M1 = inv(M)
            iso(a::Q) = R(N * (M1 * a.val.coeff))
            return iso
        end
    end
    throw(ErrorException("no isomorphism found - not reachable"))
end

function isomorphism(::Type{Z}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Y,R<:Quotient{Y,P}}
    iso(a::Z) = R(a)
end

function isomorphism(::Type{Q}, ::Type{R}, nr::Integer) where {Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q,Y,R<:Quotient{Y,P}}

    iso1 = isomorphism(Q, R)
    r = Q <: Quotient ? deg(modulus(Q)) : 1
    nr = mod(nr, r)
    r == 0 && return iso1
    N = hcat(iso1.N[:,nr+1:r], iso1.N[:,1:nr])
    M1 = iso1.M1
    iso(a::Q) = R(N * (M1 * a.val.coeff))
    iso
end

function rank(a::Q) where Q
    p = characteristic(Q)
    r = Q <: Quotient ? deg(modulus(Q)) : 1
    iszero(a) && return 0
    m = 1
    b = a
    while m < r
        b = b^p
        b == a && break
        m += 1
    end
    m
end

