
export GF, normalmatrix, allzeros

category_trait(::Type{<:GaloisField}) = FieldTrait

"""
    GF(p, r; mod=nothing, nr=0)

Create a class of element type `GaloisField` of order `p^r`.
`p` must be a prime integer and `r` a positive integer.
If `nr != 0` is given, it triggers the use of an alternate modulus
for the `GFImpl` class.

Optionally either the modulus polynomial `mod` or an integer search modifier `nr` may be given
to control the selection of the modulus polynomial.
"""
function GF(p::Integer, r::Integer; nr::Integer=0, mod=nothing)
    Q = GFImpl(p, r, nr=nr, mod=mod)
    ord = order(Q)
    r = dimension(Q)
    r == 1 && mod === nothing && return Q

    T = mintype_for(p, r, true)
    gen = first(Iterators.filter(x -> order(x) == ord-1, Q))

    function gfclass(p, ord, gen)
        c = fill(gen, ord)
        c[1] = c[2] = 1
        cumprod!(c, c)
        c[1] = 0
        exptable = [T(tonumber(x, p)) for x in c]
        logtable = invperm(exptable .+ 1) .- 1
        zechtable = logtable[[T(tonumber(x + 1, p)) for x in c] .+ 1] 
        exptable, zechtable
    end

    Id = (p, r, ord, tonumber(gen, p))

    new_class(gfclass, GaloisField{Id,T,Q}, p, ord, gen)
end
function GF(n::Integer; mod=nothing, nr=0)
    f = factor(n)
    length(f) == 1 || throw(ArgumentError("$n is not p^r with p prime and r >= 1"))
    p, r = f.pe[1]
    GF(p, r, mod=mod, nr=nr)
end

"""
    GaloisField{Id,T,Q}[num::Integer]

Ring element constructor. `num` is *not* the canonical homomorphism, but enumerates
all elements of `GF(p, r)` in `0:p^r-1`.
The numbers `G[0:p-1]` correspond to the base field, and `G[p]` to the polynomial `x` in
the representation of `Q`.
"""
function Base.getindex(::Type{G}, num::Integer) where G<:GaloisField
    tv = log_calc(num, G) + 1
    G(tv, NOCHECK)
end
function Base.getindex(::Type{G}, ind::AbstractRange{<:Integer}) where G<:GaloisField
    p, r, ord = characteristic(G), dimension(G), order(G)
    zt = gettypevar(G).zechtable
    logt = logg0(G)
    v = Vector{G}(undef, length(ind))
    for (i, k) in enumerate(ind)
        tv = log_calc(tocoeffs(k, p, r, ord, Int), ord, zt, logt) + 1
        v[i] = G(tv, NOCHECK)
    end
    v
end

Base.collect(::Type{G}) where G<:GaloisField = G[0:order(G)-1]

function GaloisField{Id,T,Q}(a::GaloisField{Id,T,Q}) where {Id,T,Q}
    GaloisField{Id,T,Q}(a.val, NOCHECK)
end
function GaloisField{Id,T,Q}(a::GaloisField{Id2,T,Q2}) where {Id,T,Q,Id2,Q2}
    GaloisField{Id,T,Q}(a.val, NOCHECK)
end
(::Type{G})(q::Q) where {Id,T,Q,G<:GaloisField{Id,T,Q}} = G[tonumber(q, characteristic(Q))]
(::Type{G})(q::Q) where {Id,T,Q,G<:GaloisField{Id,T,<:Quotient{<:UnivariatePolynomial{Q}}}} = G[q.val]

Quotient(g::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}} = quotient(Q, g)
Quotient(::Type{G}) where {Id,T,Q,G<:GaloisField{Id,T,Q}} = Q
Polynomial(::Type{G}) where G<:GaloisField = Polynomial(Quotient(G))

promote_rule(G::Type{GaloisField{Id,T,Q}}, ::Type{<:Integer}) where {Id,T,Q} = G
_promote_rule(G::Type{GaloisField{Id,T,Q}}, ::Type{Q}) where {Id,T,Q} = G
_promote_rule(G::Type{<:GaloisField{Id,T,<:Quotient{<:UnivariatePolynomial{Q}}}}, ::Type{Q}) where {Id,T,Q} = G

function quotient(::Type{Q}, g::G) where {Id,T,Z,Q<:Quotient{UnivariatePolynomial{Z,:α}},G<:GaloisField{Id,T,Q}}
    et = gettypevar(G).exptable
    toquotient(et[g.val+1], Q)
end

(::Type{Q})(g::G) where {Id,T,Z,Q<:Quotient{UnivariatePolynomial{Z,:α}},G<:GaloisField{Id,T,Q}} = quotient(Q, g)

import Base.Broadcast: broadcastable
broadcastable(x::Type{<:GaloisField}) = collect(x)

function isless(a::G, b::G) where G<:GaloisField
    isless(Quotient(a), Quotient(b))
end

basetype(::Type{GaloisField{Id,T,Q}}) where {Id,T,Q} = Q
depth(G::Type{<:GaloisField}) = depth(basetype(G)) + 1
characteristic(G::Type{<:GaloisField}) = characteristic(basetype(G))
dimension(G::Type{<:GaloisField}) = dimension(basetype(G))
order(G::Type{<:GaloisField}) = order(basetype(G))
lognegone(G::Type{<:GaloisField}) = characteristic(G) == 2 ? 0 : (order(G) - 1) ÷ 2
modulus(G::Type{<:GaloisField}) = modulus(basetype(G))
issimpler(a::G, b::G) where G<:GaloisField = a.val < b.val

# multiplication using lookup tables
function *(a::G, b::G) where G<:GaloisField
    iszero(a.val) && return a
    iszero(b.val) && return b
    ord = order(G)
    # beware of overflows
    G(mod(a.val - 2 + b.val, ord - 1) + 1, NOCHECK) 
end
function /(a::G, b::G) where G<:GaloisField
    iszero(a.val) && return a
    a.val == b.val && return one(G)
    iszero(b.val) && division_error()
    ord = order(G)
    # beware of overflows
    G(mod(a.val - 1 + ord - b.val, ord - 1) + 1, NOCHECK) 
end
function inv(a::G) where G<:GaloisField
    ord = order(G)
    iszero(a) && division_error()
    nlog = mod(ord - a.val, ord - 1) + 1
    G(nlog, NOCHECK)
end

"""
    num_primitives(::Type{G})

Number of primitive elements (generators of multiplicative group) of GaloisField `G`.
"""
function num_primitives(::Type{G}) where G<:Union{ZZmod,GaloisField,QuotientRing}
    Primes.totient(order(G)-1)
end

"""
    isprimitive(g::G)

Return iff `g` is a primitive element of its ring (its powers are the complete multilicative subgroup of `G`)
"""

function isprimitive(g::G) where G<:Union{ZZmod,GaloisField,QuotientRing}
    iszero(g) && return false
    n = order(G) - 1
    for p in keys(factor(n))
        isone(g ^ (n ÷ p)) && return false
    end
    true
end

import Base: ^, log

function ^(a::G, x::Integer) where G<:GaloisField
    ord = order(G)
    if iszero(a)
        return x > 0 ? a : division_error()
    end
    T = typeof(a.val)
    v = (log(a))
    #xx = T(mod(x, ord - 1))
    nlog = T(mod(widemul(v, x), ord-1) + 1)
    G(nlog, NOCHECK)
end

"""
    log(g::GaloisField)

Return the integer `k in 0:order(G)-2` with `g == α ^ k`, where `α` is the generator of `G`
or `-1` if `g == 0`. For example `log(one(G) == 0`.
"""
log(a::G) where G<:GaloisField = a.val - 1

"""
    log_zech(k::Integer, G::Type{<:GaloisField})

If `α` is the generator of `G`, for `k >= 0` return the `log(α^k + 1)`, for `k < 0` return `0`.
In other words: `α ^ log_zech(k, G) == α ^ k + 1` for `k >= 0`.
"""
function log_zech(k, G::Type{<:GaloisField})
    ord = order(G)
    zt = gettypevar(G).zechtable
    log_zech(k, ord, zt)
end
function log_zech(k::Integer, ord::Integer, zt::AbstractVector)
    k < 0 && return 0
    zt[mod(k, ord - 1) + 2] - 1
end

"""
    generator(::Type{<:GaloisField})

Return the generator element of this implementation of Galois field.
"""
function generator(G::Type{<:GaloisField})
    G[generatornum(G)]
end

"""
   generatornum(::Type{<:GaloisField})

Return numeric representation of generator (in range `0:order(G)-1`). Ideally `== characteristic(G)`.
"""
generatornum(::Type{<:GaloisField{Id}}) where Id = Id[4]

division_error() = throw(ArgumentError("cannot invert zero"))

*(a::G, b::Integer) where G<:GaloisField = G[mod(b, characteristic(G))] * a
*(b::Integer, a::G) where G<:GaloisField =  a * b
==(a::G, b::G) where G<:GaloisField = a.val == b.val

function typedep(::Type{G}) where G<:GaloisField
    ord = order(G)
    zechtable = gettypevar(G).zechtable
    e = lognegone(G)
    ord, e, zechtable
end

function +(a::G, b::G) where G <:GaloisField
    iszero(a) && return b
    iszero(b) && return a
    a = a.val
    b = b.val
    if a < b
        a, b = b, a
    end
    ord, e, zechtable = typedep(G)
    k = a - b
    k == e && return zero(G)
    @inbounds G(mod1(zechtable[k+2] - 1 + b, ord - 1), NOCHECK)
end

function -(a::G, b::G) where G <:GaloisField
    iszero(b) && return a
    iszero(a) && return -b
    a = a.val
    b = b.val
    a == b && return zero(G)
    ord, e, zechtable = typedep(G)
    b = b > e ? b - e : b + e
    if a < b
        a, b = b, a
    end
    k = a - b
    G(mod1(zechtable[k+2] - 1 + b, ord - 1), NOCHECK)
end

function -(a::G) where G<:GaloisField
    characteristic(G) == 2 && return a
    iszero(a) && return a
    e = lognegone(G)
    a = a.val
    a = a > e ? a - e : a + e
    G(a, NOCHECK)
end

iszero(a::GaloisField) = iszero(a.val)
isone(a::GaloisField) = isone(a.val)
isunit(a::GaloisField) = !iszero(a)
issimple(a::GaloisField) = true
value(g::GaloisField) = value(toquotient(g))

zero(::Type{G}) where G<:GaloisField = G(0, NOCHECK)
one(::Type{G}) where G<:GaloisField = G(1, NOCHECK)

function rand(r::AbstractRNG, ::SamplerType{G}) where G<:GaloisField
    ord = order(G)
    G[rand(r, 0:ord-1)]
end

function Base.show(io::IO, g::Type{<:GaloisField})
    sc(f, g) = try f(g) catch; "?" end
    print(io, :GaloisField, '{', sc(characteristic, g), ',', sc(dimension, g), '}')
end

function tonumber(a::Quotient, p::Integer)
    s = 0
    for c = reverse(a.val.coeff)
        s = s * p + c.val
    end
    s
end

function toquotient(g::G) where {Id,T,Q,G<:GaloisField{Id,T,Q}}
    tvar = gettypevar(G)
    exptable = tvar.exptable
    toquotient(exptable[g.val+1], Q)
end

function toquotient(a::Integer, ::Type{Q}) where {Z,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
    p = characteristic(Q)
    r = dimension(Q)
    ord = order(Q)
    Q(tocoeffs(a, p, r, ord, Z))
end
function tocoeffs(a::Integer, p::Integer, r::Integer, ord::Integer, Z::Type)
    c = zeros(Z, r)
    0 <= a < ord || throw(ArgumentError("index must be in 0:$(ord-1)"))
    b = a
    for i = 1:r
        iszero(b) && break
        b, c[i] = divrem(b, p)
    end
    c
end

"""
    GFImpl(p[, m=1]; mod=modulus, nr=0)

Return a representation for Galois Field `GFImpl(p, m)`. `p` must be a prime number and
`m` a positive integer.

If `m == 1`, `ZZmod{p}` is returned,
otherwise an irreducible polynomial `g ∈ ZZmod{p}[:x] and deg(g) == m` is generated and
`ZZmod{p}[:x]/(g)` is returned.

Optionally either the modulus polynomial `mod` or a integer search modifier `nr` may be given
to control the selection of the modulus polynomial.

Elements of the field can be created like
```´
    GF7 = GFImpl(7)
    GF7(5)  # or
    GF53 = GFImpl(5, 3)
    GF53([1,2,3])
```
"""
function GFImpl(p::Integer, m::Integer=1; nr::Integer=0, mod=nothing)
    isprime(p) || throw(ArgumentError("base $p must be prime"))
    m > 0 || throw(ArgumentError("exponent m=$m must be positive"))
    Z = ZZ / p
    m == 1 && mod === nothing && return Z
    mm = intpower(p, m) - 1
    list = factors(mm)
    P = Z[:α]
    if mod === nothing
        x = monom(P)
        nx = max(nr, 0)
        for gen = irreducibles(P, m)
            if order(x, gen, list) == mm
                nx == 0 && return P / gen
                nx -= 1
            end
        end
        throw(ArgumentError("no irreducible polynomial of degree $m found with generator p(γ) = γ (nr = $nr)"))
    else
        gen = P(Z.(mod.coeff))
        if isirreducible(gen)
            return P / gen
        end
        throw(ArgumentError("given polynomial $gen is not irreducible in $P"))
    end
end

function Base.show(io::IO, g::G) where G<:GaloisField

    m = dimension(G)
    p = characteristic(G)
    c = toquotient(g).val.coeff
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
function normalmatrix(a::Q, m::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
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
function normalmatrix(::Type{Q}, m::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
    normalmatrix(normalbase(Q), m)
end

function normalbases(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
    r = dimension(Q)
    Base.Iterators.filter(x->rank(normalmatrix(x, r)) == r, Q)
end
"""
    normalbase(::Type{Q})

Find the first `a in Q` for which `normalmatrix(a)` is regular.
"""
function normalbase(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
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

mulsized(M::AbstractMatrix{Z}, a::Vector{Z}) where Z<:Ring = M * sized(a, size(M, 2))

function *(M::AbstractMatrix{Z}, a::Q) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P}}
    mulsized(M, a.val.coeff)
end

function monom(::Type{Q}, k::Integer) where {P<:UnivariatePolynomial,Q<:Quotient{P}}
    Q(monom(P, k))
end

"""
    homomorphism(Q, R [,nr=0])

Return a function `iso: Q -> R`, which describes an homomorphism between two Galois fields
`Q` and `R` of the same characteristic. If `Q == R` that are the Frobenius automorphisms,
if `order(Q) == order(R)` isomorphisms, in the case of `order(R) == order(S)^s` with s > 1
the (injective) monomorphisms.

The optional `nr ∈ 0:r-1` produces all possible monomorphisms (automorphisms) between `Q` and `R`.
In the automorphism case, `nr = 0` is the identity.co
"""
function homomorphism end
function homomorphism(f::Function, ::Type{G}, ::Type{H}) where {G,H}
    Hom{G,H}(f)
end
function _homomorphism(::Type{Q}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q<:Quotient{P},R<:Quotient{P}}

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
    throw(ErrorException("no homomorphism found - not reachable"))
end

function _homomorphism(::Type{Z}, ::Type{R}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},R<:Quotient{P}}
    1, 1
end

function homomorphism(iso::Function, nr::Integer=0)
    N = iso.A.N
    M1 = iso.A.M1
    Q = iso.A.Q
    R = iso.A.R
    _homomorphism(Q, R, N, M1, nr)
end

function homomorphism(::Type{Z}, ::Type{H}, nr::Integer=0) where {Z<:ZZmod,H<:GaloisField}
    Hom{Z,H}(x -> H(x))
end 

function homomorphism(::Type{G}, ::Type{H}, nr::Integer=0) where {G<:GaloisField,H<:GaloisField}
    N, M1 = _homomorphism(basetype(G), basetype(H))
    Hom{G,H}(_homomorphism(G, H, N, M1, nr))
end

function homomorphism(::Type{Q}, ::Type{R}, nr::Integer=0) where {Z<:ZZmod,P<:UnivariatePolynomial{Z,:α},Q,R<:Quotient{P}}
    N, M1 = _homomorphism(Q, R)
    _homomorphism(Q, R, N, M1, nr)
end

function _homomorphism(::Type{Q}, ::Type{R}, N, M1, nr::Integer) where {Q,R}
    r = size(N, 2)
    nr = mod(nr, r)
    # cyclic permutation of columns of N
    if nr != 0
        N = hcat(N[:,nr+1:r], N[:,1:nr])
    end
    A = (T = N * M1, N = N, M1 = M1, Q = Q, R = R)
    quot(x) = x
    quot(x::GaloisField) = Quotient(x)
    iso(a::Q) = R(A.T * quot(a))
    iso
end

"""
    allzeros(p, vx)

Assume `p` is an irreducible polynomial over `ZZ/q`.
If `p(vx) == 0` for a galois field element `vx`,
find all zeros of `p` in the galois field, vx belongs to.
"""
function allzeros(p::P, vx::Q) where {P<:UnivariatePolynomial,Q<:Ring}
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

"""
    order(p, q, xlist)

Return first `n` in `xlist` where `rem(p^n, q) == 1`; otherwise 0.
"""
function order(p, q, xlist)
    for x in xlist
        rem(p^x, q) == 1 && return x
    end
    0
end

function order(x::G) where G<:GaloisField
    iszero(x) && return 0
    isone(x) && return 1
    ord = mult_order(G)
    ord ÷ gcd(x.val - 1, ord)
end

function logg0(G)
    p = characteristic(G)
    ord = order(G)
    zt = gettypevar(G).zechtable
    logg0(p, ord, zt)
end
function logg0(p::Integer, ord::Integer, zt)
    v = Vector{Int}(undef, p)
    v[1] = -1
    s = v[2] = 0
    for i = 3:length(v)
        s = log_zech(s, ord, zt)
        v[i] = s
    end
    v
end

loggx(a::AbstractVector, G::Type{<:GaloisField}) = loggx(a, order(G), gettypevar(G).zechtable, logg0(G))
function loggx(a::AbstractVector, ord::Integer, zt::AbstractVector, logt::AbstractVector)
    loggi(k) = logt[k+1]
    k = findfirst(!iszero, a)
    k === nothing && return -1
    accu = loggi(a[k]) + k - 1
    for i = k+1:length(a)
        ai = a[i]
        if !iszero(ai)
            lai = loggi(ai) + i - 1
            accu = log_zech(mod(accu - lai, ord-1), ord, zt) + lai
        end
    end
    mod(accu, ord-1)
end

function log_calc(k::Integer, G::Type{<:GaloisField})
    p, r, ord = characteristic(G), dimension(G), order(G)
    zt = gettypevar(G).zechtable
    log_calc(tocoeffs(k, p, r, ord, Int), ord, zt, logg0(p, ord, zt))
end
function log_calc(a::AbstractVector, ord::Integer, zt::AbstractVector, logt::AbstractVector)
    loggx(a, ord, zt, logt)
end
