
export GF, dimension, isomorphism, normalmatrix, allzeros

"""
    GF(p, r; nr=0)

Create a class of element type `GaloisField` of order `p^r`.
`p` must be a prime integer and `r` a positive integer.
If `nr != 0` is given, it triggers the use of an alternate modulus
for the `GFImpl` class.
"""
function GF(p::Integer, r::Integer; nr::Integer=0)
    Q = GFImpl(p, r, nr=nr)
    r == 1 && return Q
    T = mintype_for(p, r, true)
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
function GF(n::Integer; nr=0)
    f = factor(n)
    length(f) == 1 || throw(ArgumentError("$n is not p^r with p prime and r >= 1"))
    p, r = f.pe[1]
    GF(p, r, nr=nr)
end

"""
    GaloisField{Id,T,Q}(num::Integer)

Ring element constructor. `num` is *not* the canonical isomorphism, but enumerates
all elements of `GF(p, r)` in `0:p^r-1`.
The numbers `0:p-1` correspond to the base field, and `p` to the polynomial `x` in
the representation of `Q`.
"""
function GaloisField{Id,T,Q}(num::Integer) where {Id,T,Q}
    s = num < 0 ? -1 : 1
    exp = abs(num)
    tv = gettypevar(GaloisField{Id,T,Q})
    g = GaloisField{Id,T,Q}(tv.logtable[exp+1], NOCHECK)
    s < 0 ? -g : g
end

function GaloisField{Id,T,Q}(a::GaloisField{Id,T,Q}) where {Id,T,Q}
    GaloisField{Id,T,Q}(a.val, NOCHECK)
end

function GaloisField{Id,T,Q}(a::GaloisField{Id2,T,Q2}) where {Id,T,Q,Id2,Q2}
    GaloisField{Id,T,Q}(a.val, NOCHECK)
end

convert(::Type{G}, a::Integer) where G<:GaloisField = G(a)
GaloisField{Id,T,Q}(q::Q) where {Id,T,Q} = convert(GaloisField{Id,T,Q}, q)

function convert(::Type{G}, q::Q) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    G(tonumber(q, characteristic(Q)))
end

Quotient(g::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}} = convert(Q, g)

promote_rule(G::Type{GaloisField{Id,T,Q}}, ::Type{<:Integer}) where {Id,T,Q} = G
_promote_rule(G::Type{GaloisField{Id,T,Q}}, ::Type{Q}) where {Id,T,Q} = G

function convert(::Type{Q}, g::G) where {Id,T,Z,Q<:Quotient{UnivariatePolynomial{Z,:γ}},G<:GaloisField{Id,T,Q}}
    et = gettypevar(G).exptable
    toquotient(et[g.val+1], Q)
end

(::Type{Q})(g::G) where {Id,T,Z,Q<:Quotient{UnivariatePolynomial{Z,:γ}},G<:GaloisField{Id,T,Q}} = convert(Q, g)


function isless(a::G, b::G) where G<:GaloisField
    isless(Quotient(a), Quotient(b))
end

basetype(::Type{GaloisField{Id,T,Q}}) where {Id,T,Q} = Q
depth(G::Type{<:GaloisField}) = depth(basetype(G)) + 1
characteristic(G::Type{<:GaloisField}) = characteristic(basetype(G))
order(G::Type{<:GaloisField}) = order(basetype(G))
dimension(G::Type{<:GaloisField}) = dimension(basetype(G))
modulus(G::Type{<:GaloisField}) = modulus(basetype(G))

# multiplication using lookup tables
function *(a::G, b::G) where G<:GaloisField
    ord = order(G)
    a.val == 0 && return a
    b.val == 0 && return b
    G(mod(a.val - 2 + b.val, ord - 1) + 1, NOCHECK) 
end

+(a::G, b::G) where G<:GaloisField = addop(+, a, b)
-(a::G, b::G) where G<:GaloisField = addop(-, a, b)
-(a::G) where G<:GaloisField = a * (-1) 
*(a::G, b::Integer) where G<:GaloisField = G(mod(b, characteristic(G))) * a
*(b::Integer, a::G) where G<:GaloisField =  a * b
==(a::G, b::G) where G<:GaloisField = a.val == b.val

function addop(op::Function, a::G, b::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    ord = order(Q)
    p = characteristic(Q)
    tv = gettypevar(G)
    exptable = tv.exptable
    logtable = tv.logtable
    nl = _addop(op, a.val, b.val, p, exptable, logtable)
    G(nl, NOCHECK)
end

function _addop(op::Function, a::Integer, b::Integer, p::Integer, exptable, logtable)
    na = exptable[a+1]
    nb = exptable[b+1]
    if p == 2
        ns = xor(na, nb)
    else
        ns = oftype(na, 0)
        pp = oftype(p, 1)
        while !iszero(na) || !iszero(nb)
            na, xa = fldmod(na, p)
            nb, xb = fldmod(nb, p)
            xc = op(xa, xb)
            xc = mod(xc, p)
            ns += xc * pp
            pp *= p
        end
    end
    logtable[ns+1]
end

iszero(a::G) where G<:GaloisField = iszero(a.val)
isunit(a::GaloisField) = !iszero(a)
issimple(a::GaloisField) = true

import Base: ^

function ^(a::G, x::Integer) where G<:GaloisField
    ord = order(G)
    if iszero(a)
        return x > 0 ? a : throw(ArgumentError("cannot invert zero"))
    end
    nlog = mod(widemul(a.val - 1, x), ord-1) + 1
    G(nlog, NOCHECK)
end

function inv(a::G) where G<:GaloisField
    ord = order(G)
    iszero(a) && throw(ArgumentError("cannot invert zero"))
    nlog = mod(ord-a.val, ord - 1) + 1
    G(nlog, NOCHECK)
end

zero(::Type{G}) where G<:GaloisField = G(0)
one(::Type{G}) where G<:GaloisField = G(1)

function /(a::G, b::G) where G<:GaloisField
    iszero(b) && throw(ArgumentError("cannot invert zero"))
    a * inv(b)
end

function rand(r::AbstractRNG, ::SamplerType{G}) where G<:GaloisField
    ord = order(G)
    G(rand(0:ord-1))
end

function Base.show(io::IO, g::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    tvar = gettypevar(G)
    exptable = tvar.exptable
    Base.show(io, toquotient(exptable[g.val+1], Q))
end

function Base.show(io::IO, g::Type{<:GaloisField})
    sc(f, g) = try f(g) catch; "?" end
    print(io, g.name.name, '{', sc(characteristic, g), ',', sc(dimension, g), '}')
end

function tonumber(a::Quotient, p::Integer)
    s = 0
    for c = reverse(a.val.coeff)
        s = s * p + c.val
    end
    s
end

function toquotient(a::Integer, ::Type{Q}) where {Z,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    p = characteristic(Q)
    r = dimension(Q)
    c = zeros(Z, r)
    b = a % order(Q)
    for i = 1:r
        iszero(b) && break
        b, c[i] = divrem(b, p)
    end
    Q(c)
end

"""
    GFImpl(p[, m=1])

Return a representation for Galois Field `GFImpl(p, m)`. `p` must be a prime number and
`m` a positive integer.

If `m == 1`, `ZZmod{p}` is returned,
otherwise an irreducible polynomial `g ∈ ZZmod{p}[:x] and deg(g) == m` is generated and
`ZZmod{p}[:x]/(g)` is returned.

Elements of the field can be created like
```´
    GF7 = GFImpl(7)
    GF7(5)  # or
    GF53 = GFImpl(5, 3)
    GF53([1,2,3])
```
"""
function GFImpl(p::Integer, m::Integer=1; nr::Integer=0)
    isprime(p) || throw(ArgumentError("base $p must be prime"))
    m > 0 || throw(ArgumentError("exponent m=$m must be positive"))
    Z = ZZ / p
    if m == 1
        Z
    else
        gen = irreducible(Z[:γ], m, nr)
        typeof(gen) / gen
    end
end

function dimension(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    deg(modulus(Q))
end

function Base.show(io::IO, q::Q) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}

    m = dimension(Q)
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
function normalmatrix(a::Q, m::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    p = characteristic(Q)
    r = dimension(Q)
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
function normalmatrix(::Type{Q}, m::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    normalmatrix(normalbase(Q), m)
end

function normalbases(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    r = dimension(Q)
    Base.Iterators.filter(x->rank(normalmatrix(x, r)) == r, Q)
end
"""
    normalbase(::Type{Q})

Find the first `a in Q` for which `normalmatrix(a)` is regular.
"""
function normalbase(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
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

function *(M::AbstractMatrix{Z}, a::Q) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P}}
    mulsized(M, a.val.coeff)
end

function monom(::Type{Q}, k::Integer) where {P<:UnivariatePolynomial,Q<:Quotient{P}}
    Q(monom(P, k))
end

"""
    isomorphism(Q, R)

Return a function `iso:Q -> R`, which describes an isomorphism between two galois fields
`Q` and `R` of the same order, or `Q` being mapped to a subfield of `R`. In both cases, if `order(Q) == p^r`,
then necessarily `order(R) == p^(r*s)` for some positive integer `s`.
"""
function isomorphism end
function _isomorphism(::Type{Q}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q<:Quotient{P},R<:Quotient{P}}

    r = dimension(Q)
    s = dimension(R)
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
        S[i,i] -= one(Z)
    end
    K = Matrix(nullspace(S))

    for g0 in Q
        if R == Q
            g = f
            N = M
        else
            g = R(K * g0)
            deg(g.val) <= 0 && continue
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

function _isomorphism(::Type{Z}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},R<:Quotient{P}}
    1, 1
end

function isomorphism(iso::Function, nr::Integer=0)
    N = iso.A.N
    M1 = iso.A.M1
    Q = iso.A.Q
    R = iso.A.R
    _isomorphism(Q, R, N, M1, nr)
end

function isomorphism(::Type{Q}, ::Type{R}, nr::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:γ},Q,R<:Quotient{P}}

    N, M1 = _isomorphism(Q, R)
    _isomorphism(Q, R, N, M1, nr)
end

function _isomorphism(::Type{Q}, ::Type{R}, N, M1, nr::Integer) where {Q,R}
    r = size(N, 2)
    nr = mod(nr, r)
    # cyclic permutation of columns of N
    if nr != 0
        N = hcat(N[:,nr+1:r], N[:,1:nr])
    end
    A = (T = N * M1, N = N, M1 = M1, Q = Q, R = R)
    iso(a::Q) = R(A.T * a)
    iso
end

"""
    allzeros(p, vx)

Assuming `p(vx) == 0` for an irreducible polynomial `p` and a galois field element `vx`
find all zeros of `p` inrreducibles the galois field, vx belongs to.
"""
function allzeros(p::P, vx::Q) where {P<:UnivariatePolynomial{<:ZZmod},Q<:Quotient{P}}
    q = characteristic(Q)
    r = deg(p)
    return (vx^q^k for k = 0:r-1)
    #=
    r = deg(p)
    m = dimension(Q)
    M = normalmatrix(normalbase(P/p), r)
    N = hcat( (sized((vx^k).val.coeff, m) for k = 0:r-1)...) *  M
    a = inv(M)[:,2]
    cp(N, k) = [N[:,k+1:r] N[:,1:k]] # cyclically permutating columns
    [ Q(cp(N, k) * a) for k in 0:r-1]
    =#
end

