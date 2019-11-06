
export GF, isomorphism, normalmatrix, allzeros

function GaloisField(p::Integer, r::Integer; nr::Integer=0)
    Q = GF(p, r)
    T = UInt32
    ord = order(Q)
    Id = Int(ord)
    gen = first(Iterators.filter(x -> order(x) == ord-1, Q))
    c = fill(gen, ord)
    c[1] = c[2] = 1
    cumprod!(c, c)
    exptable = [T(tonumber(x, p)) for x in c]
    exptable[1] = 0
    logtable = invperm(exptable .+ 1) .- 1
    new_class(GaloisField{Id,T,Q}, tonumber(gen, p), logtable, exptable)
end

function GaloisField{Id,T,Q}(num::Integer) where {Id,T,Q}
    ord = order(Q)
    exp = mod(num, ord) + 1
    tv = gettypevar(GaloisField{Id,T,Q})
    logtable = tv.logtable
    GaloisField{Id,T,Q}(logtable[exp], NOCHECK)
end

order(::Type{GaloisField{Id,T,Q}}) where {Id,T,Q} = order(Q)
characteristic(::Type{GaloisField{Id,T,Q}}) where {Id,T,Q} = characteristic(Q)

function *(a::G, b::G) where G<:GaloisField
    ord = order(G)
    a.val == 0 && return a
    b.val == 0 && return b
    G(mod(a.val + b.val - 2, ord - 1) + 1, NOCHECK) 
end

function +(a::G, b::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    ord = order(Q)
    p = characteristic(Q)
    tv = gettypevar(G)
    exptable = tv.exptable
    na = exptable[a.val+1]
    nb = exptable[b.val+1]
    if p == 2
        ns = xor(na, nb)
    else
        s = toquotient(na, Q) + toquotient(nb, Q)
        ns = tonumber(s, p)
    end
    logtable = tv.logtable
    nl = logtable[ns+1]
    G(nl, NOCHECK)
end

iszero(a::G) where G<:GaloisField = v.val == order(G)

import Base: ^
function ^(a::G, x::Integer) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    ord = order(Q)
    a.val == ord && x != 0 && return a
    nlog = mod(widemul(a.val - 1, x), ord-1) + 1
    G(nlog, NOCHECK)
end

function Base.show(io::IO, g::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    tvar = gettypevar(G)
    exptable = tvar.exptable
    Base.show(io, toquotient(exptable[g.val+1], Q))
end

function tonumber(a::Quotient, p::Integer)
    s = 0
    for c = reverse(a.val.coeff)
        s = s * p + c.val
    end
    s
end

function toquotient(a::Integer, ::Type{Q}) where {X,Z,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    p = characteristic(Q)
    r = deg(modulus(Q))
    c = zeros(Z, r)
    b = a % (p^r)
    for i = 1:r
        iszero(b) && break
        b, c[i] = divrem(b, p)
    end
    Q(c)
end

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
    bases = normalbases(Q)
    isempty(bases) && throw(ArgumentError("quotient type with modulus $(modulus(Q)) has no normal bases - probably modulus is not an irreducible polynomial"))
    first(bases)
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

mulsized(M::Matrix{Z}, a::Vector{Z}) where Z<:Ring = M * sized(a, size(M, 2))
mulsized(M::Diagonal{Z}, a::Vector{Z}) where Z<:Ring = M * sized(a, size(M, 2))

function *(M::AbstractMatrix{Z}, a::Q) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P}}
    mulsized(M, a.val.coeff)
end

function monom(::Type{Q}, k::Integer) where {X, P<:UnivariatePolynomial,Q<:Quotient{X,P}}
    Q(monom(P, k))
end

"""
    isomorphism(Q, R)

Return a function `iso:Q -> R`, which describes an isomorphism between two galois fields
`Q` and `R` of the same order, or `Q` being mapped to a subfield of `R`. In both cases, if `order(Q) == p^r`,
then necessarily `order(R) == p^(r*s)` for some positive integer `s`.
"""
function isomorphism end
function _isomorphism(::Type{Q}, ::Type{R}) where {X,Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q<:Quotient{X,P},Y,R<:Quotient{Y,P}}

    r = deg(modulus(Q))
    s = deg(modulus(R))
    p = characteristic(Q)
    pr = p^r
    mod(s, r) == 0 || throw(ArgumentError("dimension of Q ($r) must divide that of R ($s)"))
    f = normalbase(Q)
    M = normalmatrix(f, r)
    M1 = inv(M)
    k = 3 - (p % 2)
    h = M1 * f^k

    xr = monom(R, 1)
    L = ((xr^k)^pr for k = 0:s-1)
    S = hcat(collect(sized(x.val.coeff, s) for x in L)...)
    for i = 1:s
        S[i,i] -= 1
    end
    K = nullspace(S)

    for g0 in Q
        if R == Q
            g = f
            N = M
        else
            g = R(K * g0)
            deg(g.val) <= 1 && continue
            N = normalmatrix(g, r)
        end
        if sized((g^k).val.coeff, s) == N * h
            #if rank(N) != r
            #    throw(ErrorException("expected rank $r, but was $(rank(N)) $g"))
            #end
            return N, M1
        end
    end
    throw(ErrorException("no isomorphism found - not reachable"))
end

function _isomorphism(::Type{Z}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Y,R<:Quotient{Y,P}}
    1, 1
end

function isomorphism(iso::Function, nr::Integer=0)
    N = iso.A.N
    M1 = iso.A.M1
    Q = iso.A.Q
    R = iso.A.R
    _isomorphism(Q, R, N, M1, nr)
end

function isomorphism(::Type{Q}, ::Type{R}, nr::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{:γ,Z},Q,Y,R<:Quotient{Y,P}}

    N, M1 = _isomorphism(Q, R)
    _isomorphism(Q, R, N, M1, nr)
end

function _isomorphism(::Type{Q}, ::Type{R}, N, M1, nr::Integer) where {Q,R}
    r = size(N, 2)
    nr = mod(nr, r)
    if nr != 0
        N = hcat(N[:,nr+1:r], N[:,1:nr])
    end
    A = (T = N * M1, N = N, M1 = M1, Q = Q, R = R)
    iso(a::Q) = R(A[1] * a)
    iso
end

"""
    allzeros(p, vx)

Assuming `p(vx) == 0` for an irreducible polynomial `p` and a galois field element `vx`
find all zeros of `p` inthe galois field, vx belongs to.
"""
function allzeros(p::P, vx::Q) where {X,P<:UnivariatePolynomial{X,<:ZZmod},Y,Q<:Quotient{Y,P}}
    r = deg(p)
    m = deg(modulus(Q))
    M = normalmatrix(normalbase(P/p), r)
    N = hcat( (sized((vx^k).val.coeff, m) for k = 0:r-1)...) *  M
    a = inv(M)[:,2]
    cp(N, k) = [N[:,k+1:r] N[:,1:k]] # cyclically permutating columns
    [ Q(cp(N, k) * a) for k in 0:r-1]
end

