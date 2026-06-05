


using Primes
import Primes.factor
import Random: rand
using Random: SamplerType, AbstractRNG
export factor

"""
    num_irreducibles(::Type{<:UnivariatePolynomial{F}}, r)

Number of irreducible polynomials over `F` of degree `r`.
"""
function num_irreducibles(::Type{<:UnivariatePolynomial{G}}, r::Integer) where G
    k = order(G)
    iszero(k) && throw(ArgumentError("order of base type is zero"))
    T = mintype_for(k, r, false)
    necklace(T(k), r)
end
function num_irreducibles(::Type{G}, r) where G<:Ring
    num_irreducibles(G[:x], r)
end
num_irreducibles(a::Type{Union{}}) = throw(MethodError(num_irreducibles, (a,)))

"""
    isirreducible(p::F[X])

Returns iff `p` is an irreducible (prime) polynomial over field `F`. See also `factor`.
"""
function isirreducible(
    p::UnivariatePolynomial{F},
    ::Type{T},
) where {T<:EuclidianDomainTrait,F<:QuotientRing}
    _isirreducible(p, T, Val(characteristic(F)))
end
function _isirreducible(
    p::UnivariatePolynomial{F},
    ::Type{T},
    ::Val, # Val{N} whith N > 0
) where {T<:EuclidianDomainTrait,F<:QuotientRing}
    (iszero(p) || isunit(p)) && return false
    deg(p) <= 1 && return true
    iszero(p[0]) && return false
    pp = gcd(p, derive(p)) # check if p is squarefree
    deg(pp) > 0 && return false
    isddf(p)
end

import Base.Iterators: Filter, take, drop
"""::UnivariatePolynomial{<:QuotientRing}
    irreducible(P, n, nr=0)

Returns an irreducible polynomial with in `P` with degree `n`. Skip first `nr` hits.
"""
irreducible(a::Type{Union{}}, s...) = merror(irreducible, (a, s...))
irreducible(::Type{P}, n) where P<:UnivariatePolynomial = first(irreducibles(P, n))
function irreducible(::Type{P}, n, nr::Integer) where P<:UnivariatePolynomial
    first(drop(irreducibles(P, n), nr))
end
"""
    reducible(P, n, nr=0)

Returns a reducible polynomial with in `P` with degree `n`. Skip first `nr` hits.
"""
reducible(a::Type{Union{}}, s...) = merror(reducible, (a, s...))
reducible(::Type{P}, n) where P<:UnivariatePolynomial = first(reducibles(P, n))
function reducible(::Type{P}, n, nr::Integer) where P<:UnivariatePolynomial
    first(drop(reducibles(P, n), nr))
end
"""
    irreducibles(P, n)

Returns iterator of all irreducible monic polynomials in `P` with degree `n`.
"""
function irreducibles(::Type{P}, n) where P<:UnivariatePolynomial{<:Ring}
    Base.Iterators.Filter(isirreducible, Monic(P, n))
end
"""
reducibles(P, n)

Returns iterator of all reducible monic polynomials in `P` with degree `n`.
"""
irreducibles(a::Type{Union{}}, s...) = merror(reducibles, (a, s...))
function reducibles(::Type{P}, n) where P<:UnivariatePolynomial{<:Ring}
    Base.Iterators.Filter(!isirreducible, Monic(P, n))
end

"""
    factor(p::F[:x])

Factorize polynomial in `F[X]` where `F` is a field
(`ZZ/p`, `GF(p,m)`, or finite extension of `QQ` with `p` prime number).
"""
function factor(p::P) where P<:UnivariatePolynomial{<:QuotientRing}
    res = Pair{P,Int}[]
    u = lcunit(p)
    if !isone(u)
        p /= u
        push!(res, P(u) => 1)
    end
    if deg(p) <= 1
        if !isone(p) || isempty(res)
            push!(res, p => 1)
        end
        return res
    end
    pp = sff(p)
    for (q, k) in pp
        ff = factor2(q, Val(characteristic(basetype(P))))
        for f in ff
            push!(res, f => k)
        end
    end
    sort!(res)
end

# assuming q has finite characteristic
function factor2(q::P, ::Val) where P<:UnivariatePolynomial{<:QuotientRing}
    qq = ddf(q)
    res = P[]
    for (r, l) in qq
        rr = edf(r, l)
        append!(res, rr)
    end
    res
end

"""
    sff(p)

`Square-free factorization`.

Factor polynomial `p` into into coprime squarefree factors `u_i for i = 1:e`
such that `p = u_1^1 * u_2^2 * ... * u_e^e`.

Return an array of pairs of squarefree factors and corresponding powers.
The implementation depends on the characteristic of the Ring.

For characteristic 0 see:
`https://en.wikipedia.org/wiki/Square-free_polynomial#Yun's_algorithm`

For characteristic > 0 see:
`https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields#Square-free_factorization`
"""
function sff(f::UnivariatePolynomial{R}) where R
    _sff(f, Val(characteristic(R)))
end

function _sff(f::P, vch::Val{p}) where {p,P<:UnivariatePolynomial}
    @assert p > 0
    i = 1
    R = Pair{P,Int}[]
    fs = derive(f)
    c = gcd(f, fs) # c contains all multiple factors of f
    w = f / c # w is square-free
    while !isunit(w)
        y = gcd(w, c)
        z = w / y
        if deg(z) > 0
            push!(R, Pair(z, i))
        end
        c /= y
        w = y
        i += 1
    end

    if deg(c) > 0
        c = proot(c)
        for (g, i) in _sff(c, vch)
            push!(R, Pair(g, i * p))
        end
    end
    R
end
"""
    proot(p)

Calculate the `p`-th root of a polynomial over a field with characteristic `p != 0`.
"""
function proot(g::P) where {R,P<:UnivariatePolynomial{R}}
    p = characteristic(R)
    r = p^(dimension(R) - 1)
    compress(P([x^r for x in coeffs(g)]), p)
end

"""
    compress(p, n)

Return polynomial `q` with `q(x^n) == p(x)`.

Assuming `p` has this form. `compress(uncompress(p) == p`.
"""
function compress(p::P, n::Integer) where P<:UnivariatePolynomial
    r = (size(p.coeff, 1) + n - 1) ÷ n - 1
    nc = [p.coeff[k*n+1] for k ∈ 0:r]
    P(nc, ord(p) ÷ n)
end

"""
    uncompress(p, n)

Return polynomial `p(x^n)`.

Same as [`spread`](@ref)
"""
function uncompress(p::P, n::Integer) where {R,P<:UnivariatePolynomial{R}}
    r = length(p.coeff)
    nc = zeros(R, (r - 1) * n + 1)
    for k = 0:r-1
        nc[k*n+1] = p.coeff[k+1]
    end
    P(nc, ord(p) * n)
end

"""
    ddf(p)

`Distinct-degree factorization`.
Input is a squarefree polynomial.
Returns a list of pairs `g_i => d_i` of polynomials g_i, each of which is a product of
all irreducible monic polynomials of equal degree `d_i`. The product of all `g_i == p`.
"""
function ddf(f::P) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    S = Pair{P,Int}[]
    x = monom(typeof(f), 1)
    i = 1
    fs = f
    xqi = x
    while deg(fs) >= 2i
        xqi = powermod(xqi, q, fs)
        g = gcd(fs, xqi - x)
        if deg(g) > 0
            push!(S, Pair(g, i))
            fs /= g
        end
        i += 1
    end
    if deg(fs) > 0
        push!(S, Pair(fs, deg(fs)))
    end
    if isempty(S)
        push!(S, Pair(f, 1))
    end
    S
end

function isddf(f::P) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    _isddf(f, Val(characteristic(Z)))
end

function _isddf(f::P, ::Val) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    x = monom(typeof(f), 1)
    i = 1
    xqi = x
    d = deg(f)
    while d >= 2i
        xqi = powermod(xqi, q, f)
        g = gcd(f, xqi - x)
        deg(g) > 0 && return false
        i += 1
    end
    return true
end

"""
    edf(p::Polynomial, d::Integer)

`Equal-degree factorization`.
Algorithm of Cantor-Zassenhaus to find the factors of `p`, a product of monomials of
degree `d`. (Such polynomials are in the output of `ddf`).
The base type for `p` must be a finite field. Odd charcteristic is a covered special case.
"""
function edf(f::P, d::Integer) where {Z<:QuotientRing,P<:UnivariatePolynomial{Z}}
    q = order(Z)
    n = deg(f)
    S = [f]
    n == d && return S
    rem(n, d) == 0 || throw(DomainError((n, d), "degree of f must be multiple of d = $d"))
    ex = big(q)^d ÷ 2 # isodd(q) ? (q^d - 1) ÷ 2 : (q^d ÷ 2)
    r = div(n, d)
    power = isodd(q) ? powermod : powersum
    while length(S) < r
        h = P(rand(Z, n))
        s = length(S)
        g = power(h, ex, f) - 1
        for k = 1:s
            u = S[k]
            gu = gcd(g, u)
            if 0 < deg(gu) < deg(u)
                S[k] = gu
                push!(S, u / gu)
            end
        end
    end
    S
end

"""
    powersum(h, ex, f)

Calculate the sum `h + h^2 + h^4 + h^8 + ... + h^ex mod f`
"""
function powersum(h, ex, f)
    s = h
    n = 1
    while n < ex
        h = rem(h * h, f)
        n *= 2
        s += h
    end
    s
end

# random samplers for finite rings
function Base.rand(r::AbstractRNG, ::SamplerType{Z}) where {Z<:ZZmod}
    m = modulus(Z)
    Z(rand(r, 0:m-1))
end
# Random field element of `Q = P / (polynomial)`, whith `basetype(P) <: ZZmod`.
function Base.rand(
    r::AbstractRNG,
    ::SamplerType{Q},
) where {Z,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}

    m = deg(modulus(Q))
    r = Q(P(rand(r, Z, m)))
end

function Base.isless(p::T, q::T) where T<:Pair{<:Ring,<:Integer}
    first(p) < first(q) || first(p) == first(q) && last(p) == last(q)
end

import Base: prod
function Base.prod(ff::Vector{<:Pair{T,<:Integer}}) where T<:Ring
    res = one(T)
    for p in ff
        res *= first(p)^last(p)
    end
    res
end

function vector2quotient(
    v::AbstractVector{C},
    ::Type{Q},
) where {C,B,Q<:Quotient{<:UnivariatePolynomial{B}}}
    n = length(v)
    n == dimension(Q) || throw(DimensionMismatch())
    Q(v)
end
function vector2quotient(
    v::AbstractVector{C},
    ::Type{Q},
) where {X,C,B,Q<:Quotient{<:UnivariatePolynomial{B,X}}}
    n = length(v)
    m = dimension(Q)
    d, r = divrem(n, m)
    (r != 0 || n != qdimension(Q)) && throw(DimensionMismatch())
    if n == m
        return Q(convert(AbstractVector{B}, v))
    end
    c = Vector{B}(undef, m)
    for i = 0:m-1
        vi = view(v, i*d+1:(i+1)*d)
        c[i+1] = vector2quotient(vi, B)
    end
    Q(c)
end

function quotient2vector(q::Q, ::Type{Z}) where {Z,Q<:Quotient{<:UnivariatePolynomial}}
    v = Vector{Z}(undef, qdimension(Q))
    quotient2vector!(v, q)
end

function quotient2vector!(
    v::AbstractVector{C},
    q::Q,
) where {C,Q<:Quotient{<:UnivariatePolynomial}}
    nn = length(v)
    n = qdimension(Q)
    nn != n && resize!(v, n)
    m = dimension(Q)
    d, r = divrem(n, m)
    (r != 0) && throw(DimensionMismatch())
    if n == m
        copyto!(v, q[:])
        return v
    end
    for i = 0:m-1
        vi = view(v, i*d+1:(i+1)*d)
        quotient2vector!(vi, q[i])
    end
    v
end

qdimension(T::Type) = dimension_type(T, QQ)[1]

function factor2(q::P, V::Val{0}) where P<:UnivariatePolynomial{<:QuotientRing}
    d = deg(q)
    d <= 1 && return [q]
    if isbasetype(q)
        bq = tobasetype(q)
        f = factor(bq)
        res = P[]
        for (qf, k) in f
            @assert k == 1
            ff = factor(qf)
            for (qff, _) in ff
                append!(res, factor2c(P(qff[:]), V))
            end
        end
        return res
    else
        return factor2c(q, V)
    end
end

"""
    isbasetype(q)

All coefficients `c` of polynomial `q` can be represented as `basetype(basetype(c))`
"""
function isbasetype(q::P) where P<:UnivariatePolynomial{<:QuotientRing}
    for c in q.coeff
        deg(Polynomial(c)) >= 1 && return false
    end
    return true
end
function tobasetype(q::P) where {X,Q<:QuotientRing,P<:UnivariatePolynomial{Q,X}}
    B = basetype(basetype(Q))[X]
    B([c[0] for c in q[:]])
end

# assuming q has characteristic 0
function factor2c(q::P, ::Val{0}) where {B<:QuotientRing,P<:UnivariatePolynomial{B}}
    deg(q) <= 1 && return [q]
    qq, alpha = find_q_generator(q)
    Q = typeof(alpha)
    R = typeof(qq)
    f = factor(qq)
    length(f) == 1 && return [q]
    res = P[]
    for (qf, k) in f
        @assert(k == 1)
        #vi = M * (R / qq)(qf)[:]
        #qi = Polynomial(Q(vi, eltype(vi)))
        qi = Polynomial(qf(alpha))
        mx = gcd(qi / LC(qi), q)
        push!(res, mx)
    end
    unique!(res)
end

function _isddfc(q::P, ::Val{0}) where {Q<:QuotientRing,P<:UnivariatePolynomial{Q}}
    qq, = find_q_generator(q)
    isirreducible(qq)
end


function _isddf(q::P, V::Val{0}) where P<:UnivariatePolynomial{<:QuotientRing}
    d = deg(q)
    d <= 1 && return false
    if isbasetype(q)
        bq = tobasetype(q)
        !isirreducible(bq) && return false
    end
    return _isddfc(q, V)
end

function find_q_generator(q::P) where {B<:QuotientRing,P<:UnivariatePolynomial{B}}
    m = qdimension(B)
    n = m * deg(q)
    QQQ = QQ{ZZZ}
    qalpha = zeros(QQQ, n)
    qalpha[m+1] = 1
    qalpha[m] = 1
    Q = Quotient(P, q, false) # don't use `P / q` to avoid calling `isirreducible(q)`
    alpha = Q(qalpha, QQQ)
    while true
        ma = minimal_polynomial(alpha, QQQ)
        deg(ma) >= n && return ma, alpha
        qalpha = rand(-1:1, n)
        alpha = Q(qalpha, QQQ)
    end
end

const QU{B} = Quotient{<:UnivariatePolynomial{B}}
const UQU{B} = Union{UnivariatePolynomial{B},QU{B}}

"""
    minimal_polynomial(x::Quotient{<:Polynomial}, ::Type{QQ})

Return minimal degree polynomial `m ∈ QQ[:x]` such that `m(x) == 0`.
"""
function minimal_polynomial(x::T, ::Type{Q}) where {Q,T<:QU}
    n, Z = dimension_type(T, Q)
    P = Z[:x]
    M = zeros(Z, n, n + 1)
    M[1, 1] = 1
    xk = x
    pr = collect(1:n)
    for k = 1:n
        b = coeffs(xk, Z)
        lu_incremental!(M, pr, k + 1, b)
        if k >= n || iszero(b[k+1])
            c = UpperTriangular(view(M, 1:k, 1:k)) \ b[1:k]
            return monom(P, k) - P(c)
        end
        for i = 1:n
            M[i, k+1] = b[i]
        end
        xk *= x
    end
end

isextensiontype(::Type{T}, ::Type{Q}) where {T,Q} = T <: Q
function isextensiontype(::Type{T}, ::Type{Q}) where {B,T<:QU{B},Q<:QU}
    T <: Q ? true : isextensiontype(B, Q)
end
function isextensiontype(::Type{T}, ::Type{Q}) where {B,T<:QU{B},Q}
    isextensiontype(B, Q)
end

dimension_type(::Type{T}, ::Type{Q}) where {Q,T<:Q} = 1, T
function dimension_type(::Type{T}, ::Type{Q}) where {B,T<:QU{B},Q<:QU}
    if T <: Q
        (1, T)
    else
        d, t = dimension_type(B, Q)
        d * dimension(T), t
    end
end
function dimension_type(::Type{T}, ::Type{Q}) where {B,T<:QU{B},Q}
    d, t = dimension_type(B, Q)
    d * dimension(T), t
end

function coeffs(p::UnivariatePolynomial{B}, ::Type{Q}, m::Integer = deg(p) + 1) where {B,Q}
    isextensiontype(B, Q) ||
        throw(ArgumentError("B = $B) must be extension type of Q = $Q"))
    d, T = dimension_type(B, Q)
    v = zeros(T, m * d)
    _coeffs!(v, p, T, m)
    v
end
function coeffs(p::QU{B}, ::Type{Q}) where {B,Q}
    isextensiontype(B, Q) ||
        throw(ArgumentError("B = $B) must be extension type of Q = $Q"))
    d, T = dimension_type(B, Q)
    m = dimension(typeof(p))
    v = zeros(T, m * d)
    _coeffs!(v, p, T, m)
    v
end
coeffs(p::QU{B}, ::Type{<:QU{B}}) where B = [p]

function _coeffs!(v::AbstractVector, p::UQU{Q}, ::Type{Q}, m::Integer) where Q
    n = min(m, length(v))
    for i = 1:n
        v[i] = p[i-1]
    end
    nothing
end
function _coeffs!(v::AbstractVector, p::UQU{B}, ::Type{Q}, m::Integer) where {B,Q}
    d, _ = dimension_type(B, Q)
    n = dimension(B)
    for i = 0:m-1
        _coeffs!(view(v, i*d+1:(i+1)*d), p[i], Q, n)
    end
end

(::Type{T})(v::AbstractVector{Q}, ::Type{V}) where {Q,V<:Ring,T<:QU} = T(V.(v), V)
function (::Type{T})(v::AbstractVector{Q}, ::Type{Q}) where {Q<:Ring,B<:Q,T<:QU{B}}
    T(Polynomial(T)(v))
end
function (::Type{T})(v::AbstractVector{Q}, ::Type{Q}) where {Q<:Ring,B,T<:QU{B}}
    nn = length(v)
    m = dimension(T)
    d, _ = dimension_type(B, Q)
    m, r = fldmod(nn, d)
    w = Vector{B}(undef, m + (r > 0))
    for i = 0:m-1
        w[i+1] = B(view(v, d*i+1:d*(i+1)))
    end
    if r > 0
        w[m+1] = vcat(view(v, d*m+1:nn), zeros(Q, d - r))
    end
    T(w)
end
(::Type{T})(v::AbstractVector{T}, ::Type{T}) where {B,T<:QU{B}} = v[1]
