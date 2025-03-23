
export GF, normalmatrix, allzeros, @G_str

category_trait(::Type{<:GaloisField}) = FieldTrait
"""
    GaloisField

@see [`GF`](@ref), [`ofindex`](@ref).
"""
function GaloisField end
"""
    GF(p, r; mod=:conway, nr=0, maxord=2^20)

Create a class of element type `GaloisField` of order `p^r`.
`p` must be a prime integer and `r` a positive integer.

The modulus polynomial is looked up or calculated dependant on argument `mod`:

- If `mod == nothing`, an irreducible monic primitive polynomial of degree `r` over `ZZ/p`
    is calculated, which has the constant coefficient `(-1)^r * generator(ZZ/p)`.
- If `mod == :conway` (default), the compatible Conway polynomial is used if available,
    otherwise a less restrictive polynomial is calculated as described above.
- If `mod` is a polynomial, that irreducible monic polynomial is used as the modulus.

If `nr != 0` is given, in the case of modulus calculation, the first `nr` solutions are skipped.

`maxord` defines the maximal order, for which logarithm tables are stored to implement the class.
Otherwise a representation by quotient space of the polynomial over `ZZ/p` is used.
"""
function GF(n::Integer, k::Integer = 1; mod = :conway, nr = 0, maxord = 2^20)
    f = Primes.factor(n)
    length(f) == 1 || terror("$n is not p^r with p prime and r >= 1")
    p, r = f.pe[1]
    _GF(p, r * k, mod, nr, maxord)
end
function _GF(p::Integer, r::Integer, mod, nr::Integer, maxord::Int)
    modpol = mod isa UnivariatePolynomial
    if modpol
        B = basetype(mod)
        if r != 1
            terror(lazy"given modulus derives dimension from that, r must be 1 but is $r")
        end
        r = deg(mod) * dimension(B)
    end
    mm = intpower(p, r) - 1
    fact = Primes.factor(mm)
    Q = GFImpl(p, r, fact; nr, mod)
    r == 1 && mod === nothing && return Q
    ord = order(Q)
    q = dimension(subfield(Q))
    r = dimension(Q) * q
    T = mintype_for(p, r, true)
    pq = T(p)^q

    gen = monom(Q)
    while order(gen) != ord - 1
        gen, = next(gen)
    end
    g = tonumber(gen, pq)

    function gfclass0(fact, p, ord, gen, T)
        c = fill(gen, ord)
        c[1] = c[2] = 1
        cumprod!(c, c)
        c[1] = 0
        exptable = [T(tonumber(x, p)) for x in c]
        logtable = invperm(exptable .+ 1) .- 1
        zechtable = logtable[[T(tonumber(x + 1, p)) for x in c].+1]
        fact, exptable, logtable, zechtable
    end

    function gfclass1(fact, p, ord, gen, T)
        fact, T[], T[], T[]
    end

    sp = sintern(p)
    sord = sintern(ord)
    sg = sintern(g)

    gfclass, Id, V = if ord <= maxord
        gfclass0, (sp, r, sord, sg), T
    else
        gfclass1, (sp, r, sord, sg), Q
    end

    new_class(gfclass, GaloisField{sp,r,Id,V,Q}, fact, pq, ord, gen, V)
end

function Base.isequal(a::G, b::G) where G<:GaloisField
    tonumber(a) == tonumber(b)
end
Base.hash(a::GaloisField, x::UInt) = hash(tonumber(a), x)

"""
    ofindex(num::Integer, G) where G <: GaloisField

Ring element constructor. `num` is *not* the canonical homomorphism, but enumerates
all elements of `GF(p, r)` in `0:p^r-1`.
The numbers `ofindex.(0:p-1,G)` correspond to the base field, and `ofindex(p, G)`
to the polynomial `x` in the representation of `Q`.
"""
function ofindex(num::Integer, G::Type{<:GaloisField})
    G(internal_val(G, num), NOCHECK)
end

Base.getindex(::Type{G}, ix::Integer) where G<:GaloisField = ofindex(ix, G)
Base.firstindex(::Type{G}) where G<:GaloisField = 0
Base.lastindex(::Type{G}) where G<:GaloisField = order(G) - 1
Base.collect(::Type{G}) where G<:GaloisField = ofindex.(firstindex(G):lastindex(G), Ref(G))

function (::Type{G})(a::G) where G<:GaloisField
    G(a.val, NOCHECK)
end
function (::Type{G})(a::H) where {C,D,Id,T,Q,G<:GaloisField{C,D,Id,T,Q},P,H<:ZZmod{P,T}}
    characteristic(G) == characteristic(H) || terror("characteristic mismatch")
    G(a.val)
end
function (::Type{G})(q::Q) where {C,D,Id,T,Q<:RingInt,G<:GaloisField{C,D,Id,T,Q}}
    ofindex(tonumber(q, order(subfield(Q))), G)
end

(::Type{<:Quotient})(g::G) where G<:GaloisField = quotient(g)
Polynomial(g::G) where G<:GaloisField = value(Quotient(g))
Quotient(::Type{G}) where {C,D,Id,T,Q,G<:GaloisField{C,D,Id,T,Q}} = Q
Quotient(a::Type{Union{}}) = merror(Quotient, (a,))
Polynomial(::Type{G}) where G<:GaloisField = Polynomial(Quotient(G))
Polynomial(a::Type{Union{}}) = merror(Polynomial, (a,))
monom(::Type{G}) where G<:GaloisField = G(monom(Quotient(G)))
monom(a::Type{Union{}}, s...) = merror(monom, (a, s...))

promote_rule(G::Type{GaloisField{C,D,Id,T,Q}}, ::Type{<:Integer}) where {C,D,Id,T,Q} = G
_promote_rule(
    G::Type{GaloisField{C,D,Id,T,Q}},
    ::Type{Q},
) where {C,D,Id,T,Q<:QuotientRing} = G
_promote_rule(
    G::Type{<:GaloisField{C,D,Id,T,<:Quotient{<:UnivariatePolynomial{B}}}},
    ::Type{B},
) where {C,D,Id,T,B} = G

function quotient(g::G) where {C,D,Id,T<:Integer,Q<:Quotient,G<:GaloisField{C,D,Id,T,Q}}
    et = gettypevar(G).exptable
    quotient(et[g.val+1], Q)
end
quotient(g::G) where {C,D,Id,T,Q<:Quotient,G<:GaloisField{C,D,Id,T,Q}} = g.val


function isless(a::G, b::G) where G<:GaloisField
    isless(Quotient(a), Quotient(b))
end

basetype(::Type{GaloisField{C,D,Id,T,Q}}) where {C,D,Id,T,Q} = Q
characteristic(G::Type{<:GaloisField}) = characteristic(basetype(G))
characteristic(a::Type{Union{}}) = merror(characteristic, (a,))
dimension(G::Type{<:GaloisField}) = dimension(basetype(G)) * dimension(subfield(G))
@generated function order(a::Type{<:GaloisField})
    function order(::Type{<:Type{<:GaloisField{C,D}}}) where {C,D}
        ord = intpower(C, D)
        convert(promote_type(typeof(ord), Int), ord)
    end
    order(a)
end
lognegone(G::Type{<:GaloisField}) = characteristic(G) == 2 ? 0 : (order(G) - 1) ÷ 2
modulus(G::Type{<:GaloisField}) = modulus(basetype(G))
modulus(a::Type{Union{}}) = merror(modulus, (a,))
issimpler(a::G, b::G) where G<:GaloisField = tonumber(a) < tonumber(b)

# multiplication using lookup tables
function *(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    iszero(a) && return a
    iszero(b) && return b
    ord = order(G)
    # beware of overflows
    G(mod(a.val - 2 + b.val, ord - 1) + 1, NOCHECK)
end
function *(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    iszero(a) && return a
    iszero(b) && return b
    G(a.val * b.val, NOCHECK)
end

function /(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    iszero(a) && return a
    a.val == b.val && return one(G)
    iszero(b) && division_error()
    ord = order(G)
    # beware of overflows
    G(mod(a.val - 1 + ord - b.val, ord - 1) + 1, NOCHECK)
end
function /(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    iszero(a) && return a
    a.val == b.val && return one(G)
    iszero(b) && division_error()
    G(a.val / b.val, NOCHECK)
end
function inv(a::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    ord = order(G)
    iszero(a) && division_error()
    nlog = mod(ord - a.val, ord - 1) + 1
    G(nlog, NOCHECK)
end
function inv(a::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    iszero(a) && division_error()
    G(inv(a.val), NOCHECK)
end

fact_mult_order(::Type{G}) where G<:GaloisField = gettypevar(G).factors

import Base: ^, log

function ^(a::G, x::Integer) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    ord = mult_order(G)
    if iszero(a)
        return x > 0 ? a : x == 0 ? one(G) : division_error()
    end
    T = typeof(a.val)
    v = log(a)
    nlog = T(mod(widemul(v, mod(x, ord)), ord) + 1)
    G(nlog, NOCHECK)
end

"""
    log(g::GaloisField)

Return the integer `k in 0:order(G)-2` with `g == α ^ k`, where `α` is the generator of `G`
or `-1` if `g == 0`. For example `log(one(G)) == 0` and `log(generator(G)) == 1`.
"""
function log(a::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    a.val - 1
end

log(g::G) where G<:Ring = log(generator(G), g)

function log(g::G, a::G) where {G<:Ring}
    if iszero(a)
        -1
    else
        # calculating the discrete log is an expensive operation in general
        # which requires special algorithmic effort (==> Adleman et. al.)
        # here a naive implementation of the "baby-step-giant-step" method, which tries to
        # balance memory and runtime efficiency.

        n = order(G) - 1
        m = isqrt(n - 1) + 1 # smallest integer >= sqrt(n)
        baby = Dict{G,Int}()
        sizehint!(baby, m)
        b = one(G)
        for i = 0:m-1
            baby[b] = i
            b == a && return i
            b *= g
        end
        i = get(baby, a, -1)
        i >= 0 && return i
        giant = inv(b) # g^(-m)
        b = a * giant
        for j = 1:m-1
            i = get(baby, b, -1)
            if i >= 0
                return j * m + i
            end
            b *= giant
        end
        throw(DomainError("log: $a is not a power of $g"))
    end
end

"""
    sqrt(z::GaloisField)

Calculate a `x` in the same field with `x ^ 2 == z`.

Throw `DomainError` if no solution exists. With `x`always `-x` is a solution.
With characteristic 2, every `z` has a square root`.
"""
function Base.sqrt(x::G) where G<:Union{GaloisField,ZZmod}
    iszero(x) && return x
    if isodd(characteristic(G))
        g = generator(G)
        lo = log(x)
        if isodd(lo)
            throw(DomainError(x, "no square root exists in $G"))
        else
            g^(lo ÷ 2)
        end
    else
        x^(order(G) ÷ 2)
    end
end

"""
    log_zech(k::Integer, G::Type{<:GaloisField})

If `α` is the generator of `G`, for `k >= 0` return the `log(α^k + 1)`, for `k < 0` return `0`.
In other words: `α ^ log_zech(k, G) == α ^ k + 1` for `k >= 0`.
"""
function log_zech(k::Integer, ::Type{G}) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    ord = order(G)
    zt = gettypevar(G).zechtable
    log_zech(k, ord, zt)
end
function log_zech(k::Integer, ord::Integer, zt::AbstractVector)
    k < 0 && return 0
    zt[mod(k, ord - 1)+2] - 1
end
function log_zech(k::Integer, ::Type{G}) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    g = generator(G)
    log(g^k + 1)
end
log_zech(k, a::Type{Union{}}) = merror(log_zech, (k, a))

"""
    generator(::Type{<:GaloisField})

Return the generator element of this implementation of Galois field.
"""
function generator(::Type{G}) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    id = min(2, order(G) - 1)
    G(id, NOCHECK)
end
function generator(::Type{G}) where {C,D,Id,Q<:Quotient,G<:GaloisField{C,D,Id,Q}}
    G(generator(Q))
end

"""
   logmonom(::Type{<:GaloisField})

Return numeric representation of generator (in range `0:order(G)-1`). Ideally `== characteristic(G)`.
"""
logmonom(::Type{G}) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}} = Id[4]
logmonom(::Type{G}) where {G<:GaloisField} = tonumber(Quotient(generator(G)))
logmonom(a::Type{Union{}}) = merror(logmonom, (a,))

division_error() = terror("cannot invert zero")

*(a::G, b::Integer) where G<:GaloisField = G(b) * a
*(b::Integer, a::G) where G<:GaloisField = a * b
==(a::G, b::G) where G<:GaloisField = a.val == b.val
==(a::G, b::H) where {G<:GaloisField,H<:GaloisField} = quotient(a) == quotient(b)
function ==(::Type{A}, ::Type{B}) where {A<:GaloisField,B<:GaloisField}
    A === B || A !== Union{} && B != Union{} && Quotient(A) == Quotient(B)
end

function typedep(::Type{G}) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    ord = order(G)
    zechtable = gettypevar(G).zechtable
    e = lognegone(G)
    ord, e, zechtable
end

function +(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
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
    #@inbounds G(mod1(zechtable[k+2] - 1 + b, ord - 1), NOCHECK)
    G(mod1(zechtable[k+2] - 1 + b, ord - 1), NOCHECK)
end
function +(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    G(a.val + b.val, NOCHECK)
end

function -(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
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
function -(a::G, b::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    G(a.val - b.val, NOCHECK)
end

function -(a::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Integer}}
    characteristic(G) == 2 && return a
    iszero(a) && return a
    e = lognegone(G)
    a = a.val
    a = a > e ? a - e : a + e
    G(a, NOCHECK)
end
function -(a::G) where {C,D,Id,G<:GaloisField{C,D,Id,<:Quotient}}
    G(-a.val, NOCHECK)
end

iszero(a::GaloisField) = iszero(a.val)
isone(a::GaloisField) = isone(a.val)
isunit(a::GaloisField) = !iszero(a)
issimple(a::GaloisField) = true
value(g::GaloisField) = value(quotient(g))
subfield(::Type{G}) where G<:GaloisField = subfield(Quotient(G))
subfield(a::Type{Union{}}) = merror(subfield, (a,))

zero(::Type{G}) where G<:GaloisField = G(0, NOCHECK)
one(::Type{G}) where G<:GaloisField = G(1, NOCHECK)

function rand(r::AbstractRNG, ::SamplerType{G}) where G<:GaloisField
    ord = order(G)
    ofindex(rand(r, 0:ord-1), G)
end

function Base.show(io::IO, g::Type{<:GaloisField})
    sc(f, g) =
        try
            f(g)
        catch
            "?"
        end
    if g isa UnionAll
        Base._show_type(io, g)
    else
        print(io, :GaloisField, '{', sc(characteristic, g), ',', sc(dimension, g), '}')
    end
end

function internal_val(::Type{G}, num::Integer) where G<:GaloisField
    logtable = gettypevar(G).logtable
    n = length(logtable)
    logtable[mod(num, n)+1]
end
function internal_val(
    ::Type{G},
    num::Integer,
) where {C,D,Id,V<:Quotient,G<:GaloisField{C,D,Id,V}}
    n = order(G)
    quotient(mod(num, n), V)
end

"""
    tonumber(a)

Return an integer, which can represent the polynomial or quotient `a` if the coeffs of `a`
are not negative and `p` is not less than the maximum of those coeffs.

If `a` is `GaloisField` element, p defaults to the order of the subfield, which is used
to represent the field.
"""
function tonumber(u::UnivariatePolynomial, p::Integer = order(basetype(typeof(u))))
    s = zero(intpower(p, deg(u) + 1))
    for c in reverse(u.coeff)
        s = s * p + tonumber(c)
    end
    s * intpower(p, ord(u))
end
function tonumber(a::Q, p::Integer = order(subfield(Q))) where Q<:Quotient
    tonumber(value(a), p)
end
function tonumber(g::G) where G<:GaloisField
    tonumber(quotient(g), order(subfield(G)))
end

function quotient(a::Integer, ::Type{Q}) where {Z,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    p = order(subfield(Q))
    r = dimension(Q)
    ord = order(Q)
    Q(tocoeffs(a, p, r, ord, Z))
end
quotient(b::Integer, a::Type{Union{}}) = merror(quotient, (b, a))
function tocoeffs(a::Integer, p::Integer, r::Integer, ord::Integer, Z::Type)
    c = zeros(Z, r)
    0 <= a < ord || terror("index must be in 0:$(ord-1)")
    b = a
    for i = 1:r
        iszero(b) && break
        b, d = divrem(b, p)
        c[i] = ofindex(d, Z)
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
function GFImpl(
    p::Integer,
    m::Integer = 1,
    factors = nothing;
    nr::Integer = 0,
    mod = :conway,
)
    isprime(p) || terror("base $p must be prime")
    m > 0 || terror("exponent m=$m must be positive")

    m == 1 && mod === nothing && return ZZ / p
    if mod === :conway
        gen = conway(p, m, :γ)
        if !ismissing(gen)
            return typeof(gen) / gen
        end
        mod = nothing
    end

    if isnothing(mod)
        poly = quasi_conway(p, m, :α; nr, factors)
        return typeof(poly) / poly

    elseif mod isa UnivariatePolynomial{<:GaloisField}
        G = basetype(mod)
        characteristic(G) == p || terror("characteristic mismatch")
        dg = dimension(G)
        gen = mod
        # assuming gen is irreducible!
        return typeof(gen) / gen

    elseif mod isa UnivariatePolynomial
        m == deg(mod) || terror(lazy"given modulus requires degree $m")
        Z = ZZ / p
        P = Z[:β]
        # do not check if x is primitive here
        gen = P(Z.(mod.coeff), ord(mod))
        if isirreducible(gen)
            return P / gen
        end
        terror("given polynomial $gen is not irreducible over $Z")
    else
        terror("modulus '$mod' not supported")
    end
end

"""
    G_str

Constructor literal for elements of Galois Fields. Example: `G"::1:2"5`.
"""
macro G_str(a::String, b::Integer)
    gf(a, b)
end
function gf(a::String, b::Integer)
    f = factor(b)
    length(f) != 1 && throw(ArgumentError("only powers of primes"))
    p, r = f.pe[1]
    digs = split(a, ':')
    s = findfirst(!isempty, a)
    r1 = size(digs, 1)
    r > 1 && r1 > r && throw(ArgumentError("invalid GF string"))
    r = max(r, r1)
    G = GF(p, r)
    tp(x) = isempty(x) ? 0 : tryparse(Int, x)
    v = mapfoldl(tp, (a, b) -> a * p + b, digs; init = 0)
    ofindex(v, G)
end

function Base.show(io::IO, g::G) where G<:GaloisField
    print(io, "G\"")
    _show(io, g)
    print(io, '"', characteristic(G))
end
function _show(io::IO, g::G) where G<:GaloisField
    m = deg(modulus(G))
    p = characteristic(G)
    cc = quotient(g).val
    for k = m-1:-1:1
        _showelement(io, cc[k])
        print(io, ':')
    end
    _showlastelement(io, cc[0])
end

_showelement(io, x::ZZmod) = !iszero(x) && _showlastelement(io, x)
_showelement(io, g::GaloisField) = _showlastelement(io, g)
_showlastelement(io, x::ZZmod) = print(io, x.val)
_showlastelement(io, g::GaloisField) = _show(io, g)

"""
    normalmatrix(a::Q[, m])

Return a matrix of element type `ZZ/p`, whose colums are the coefficient
vectors of `a^(p^i) for i = 0:m-1`.

Here Q is a Galois field of characteristic `p` and order `p^r`.

`m` m defaults to `r`.

If `normalmatrix(a))` is regular, the field elements `a^(p^i) for i = 0:r-1` form a
base of `Q` as a vector space over `ZZ/p` (a normal base).
"""
function normalmatrix(
    a::Q,
    m::Integer = 0,
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    p = characteristic(Q)
    r = dimension(Q)
    m = m <= 0 ? r : m
    M = Matrix{Z}(undef, r, m)
    for i = 0:m-1
        c = a.val
        for j = 1:r
            M[j, i+1] = c[j-1]
        end
        a ^= p
    end
    M
end

"""
    normalmatrix(::Type{Q}[, m])

Return `normalmatrix(a, m)` for the first `a` in `Q` for which this has maximal rank.
"""
function normalmatrix(
    ::Type{Q},
    m::Integer = 0,
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    normalmatrix(normalbase(Q), m)
end

function normalbases(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    r = dimension(Q)
    Base.Iterators.filter(x -> rank(normalmatrix(x, r)) == r, Q)
end
"""
    normalbase(::Type{Q})

Find the first `a in Q` for which `normalmatrix(a)` is regular.
"""
function normalbase(::Type{Q}) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    bases = normalbases(Q)
    isempty(bases) && nonormalbaseserror(Q)
    first(bases)
end

function nonormalbaseserror(Q)
    text =
        "quotient type with modulus $(modulus(Q)) has no normal bases" *
        " - probably modulus is not an irreducible polynomial"
    terror(text)
end

import Base: *

"""
    sized(a::Vector, r)

Return a vector of length `r`, which starts with `a` and is filled up with zeros if required.
"""
function sized(a::UnivariatePolynomial{Z}, r::Integer) where Z
    n = deg(a) + 1
    v = coeffs(a)
    n == r ? v : n < r ? vcat(v, zeros(Z, r - n)) : v[1:r]
end

mulsized(M::AbstractMatrix{Z}, a::UnivariatePolynomial{Z}) where Z<:Ring =
    M * sized(a, size(M, 2))

function *(
    M::AbstractMatrix{Z},
    a::Q,
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    mulsized(M, a.val)
end

function monom(::Type{Q}, k::Integer, lc = 1) where {P<:UnivariatePolynomial,Q<:Quotient{P}}
    k < dimension(Q) ? Q(monom(P, k, lc)) : lc == 1 ? Q(monom(P))^k : Q(monom(P))^k * lc
end

"""
    homomorphism(R, S [,nr=0])

Return a function `iso: R -> S`, which describes an homomorphism between two Galois fields
`R` and `S` of the same characteristic. If `R == S` that are the Frobenius automorphisms,
if `order(R) == order(S)` isomorphisms, in the case of `dim(S) == dim(R) * s` with s > 1
the (injective) monomorphisms.

The optional `nr ∈ 0:r-1` produces all possible monomorphisms (automorphisms) between `R`
and `S`. In the automorphism case, `nr = 0` is the identity.
"""
function homomorphism end
function homomorphismf(f::Function, ::Type{G}, ::Type{H}) where {G,H}
    Hom{G,H}(f)
end

function homomorphism(
    ::Type{R},
    ::Type{S},
    nr::Integer = 0,
) where {T<:Union{Quotient{<:UnivariatePolynomial{<:ZZmod}},GaloisField},R<:T,S<:T}

    r = dimension(R)
    s = dimension(S)
    p = characteristic(R)
    q = characteristic(S)
    p == q || terror("fields with differing characteristics")
    mod(s, r) == 0 || terror("dimension of R ($r) must divide that of S ($s)")
    pr = p^r
    m = s ÷ r
    w = (pr^m - 1) ÷ (pr - 1)
    x = generator(S)
    y = x^(w * p^nr)
    @assert order(y) == pr - 1
    f(a::R) = evaluate(Polynomial(a), y)
    homomorphismf(f, R, S)
end

function _homomorphism(
    ::Type{R},
    ::Type{S},
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},R<:Quotient{P},S<:Quotient{P}}

    r = dimension(R)
    s = dimension(S)
    p = characteristic(R)
    pr = p^r
    mod(s, r) == 0 || terror("dimension of Q ($r) must divide that of R ($s)")
    f = normalbase(R)
    M = normalmatrix(f, r)
    M1 = inv(M)
    k = 3 - (p % 2)
    h = M1 * f^k

    xr = monom(S, 1)
    L = ((xr^k)^pr for k = 0:s-1)
    U = hcat(collect(sized(x.val, s) for x in L)...)
    for i = 1:s
        U[i, i] -= one(Z)
    end
    K = Matrix(nullspace(U))

    for g0 in R
        if S == R
            g = f
            N = M
        else
            g = S(K * g0)
            deg(g.val) <= 0 && continue
            N = normalmatrix(g, r)
        end
        if sized((g^k).val, s) == N * h
            #if rank(N) != r
            #    throw(ErrorException("expected rank $r, but was $(rank(N)) $g"))
            #end
            return N, M1
        end
    end
    throw(ErrorException("no homomorphism found - not reachable"))
end

function _homomorphism(
    ::Type{Z},
    ::Type{R},
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},R<:Quotient{P}}
    1, 1
end

function homomorphism(iso::Function, nr::Integer = 0)
    N = iso.A.N
    M1 = iso.A.M1
    Q = iso.A.Q
    R = iso.A.R
    _homomorphism(Q, R, N, M1, nr)
end

function homomorphism(::Type{Z}, ::Type{H}, nr::Integer = 0) where {Z<:ZZmod,H<:GaloisField}
    characteristic(Z) == characteristic(H) || terror("different characteristics")
    Hom{Z,H}(x -> H(x))
end

function homomorphism2(
    ::Type{G},
    ::Type{H},
    nr::Integer = 0,
) where {G<:GaloisField,H<:GaloisField}
    N, M1 = _homomorphism(basetype(G), basetype(H))
    Hom{G,H}(_homomorphism(G, H, N, M1, nr))
end

function homomorphism2(
    ::Type{Q},
    ::Type{R},
    nr::Integer = 0,
) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q,R<:Quotient{P}}
    N, M1 = _homomorphism(Q, R)
    _homomorphism(Q, R, N, M1, nr)
end

function _homomorphism(::Type{Q}, ::Type{R}, N, M1, nr::Integer) where {Q,R}
    r = size(N, 2)
    nr = mod(nr, r)
    # cyclic permutation of columns of N
    if nr != 0
        N = hcat(N[:, nr+1:r], N[:, 1:nr])
    end
    A = (T = N * M1, N = N, M1 = M1, Q = Q, R = R)
    quot(x) = x
    quot(x::GaloisField) = Quotient(x)
    iso(a::Q) = R(A.T * quot(a))
    iso
end

function ==(a::H, b::H) where {F,R<:GaloisField,S<:GaloisField,H<:Hom{F,R,S}}
    a.f.A == b.f.A && a.f.quot.contents == b.f.quot.contents
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
    cp(N, k) = [N[:,k+1:r] N[:,1:k]] # cyclically permuting columns
    [ Q(cp(N, k) * a) for k in 0:r-1]
    =#
end

function order(x::G) where {C,D,Id,V<:Integer,G<:GaloisField{C,D,Id,V}}
    iszero(x) && return 0
    isone(x) && return 1
    ord = mult_order(G)
    ord ÷ gcd(x.val - 1, ord)
end
