# class constructors
# convenience type constructor:
# enable `R[:x,:y,:z,...]` as short for `MultivariatePolynomial{R,N,Id}`
function getindex(R::Type{<:Ring}, s::Symbol, t::Symbol...)
    vs = collect((s, t...))
    check_varnames(vs, varnameset(R))
    N = length(vs)
    Id = sintern(vs)
    new_class(MultivariatePolynomial{R,N,Id,Int,Tuple{N}}, vs)
end
# enable `R[[:x,:y],[:z]]` for non-standard monomial orderings
function getindex(R::Type{<:Ring}, s::AbstractVector{Symbol}, t::AbstractVector{Symbol}...)
    blocks = collect((s, t...))
    construct(R, blocks)
end

function lextend(::Type{P}, s::Symbol, t::Symbol...) where {R,P<:MultivariatePolynomial{R}}
    blocks = [collect((s, t...)), varblocks(P)...]
    construct(R, blocks)
end

function construct(::Type{R}, blocks) where R<:Ring
    vs = vcat(blocks...)
    check_varnames(vs, varnameset(R))
    N = length(vs)
    Id = sintern(vs)
    n = length(blocks)
    T = n == 1 ? Int : NTuple{n,Int}
    B = Tuple{[length(x) for x in blocks]...}
    new_class(MultivariatePolynomial{R,N,Id,T,B}, vs)
end

function check_varnames(vs, bs)
    for v in vs
        if v in bs
            str = lazy"Duplicate variable names '$(join(string.(vs), ' '))'"
            throw(ArgumentError(str))
        end
    end
end

import Base: copy, promote_rule
import Base: +, -, *, zero, one, ==, hash, isless, iszero, isone

# make new copy
copy(p::P) where P<:MultivariatePolynomial = P(copy(p.ind), copy(p.coeff))

# promotion and conversion
# _promote_rule(::Type{<:MultivariatePolynomial{R,M,X}}, ::Type{<:Polynomial}) where {X,M,R} =
# Base.Bottom
_promote_rule(
    ::Type{MultivariatePolynomial{R,N,X,T,B}},
    ::Type{MultivariatePolynomial{S,N,X,T,B}},
) where {X,N,R,S,T,B} = MultivariatePolynomial{promote_type(R, S),N,X,T,B}

_promote_rule(
    ::Type{P},
    ::Type{S},
) where {R,N,X,B,T,S<:Ring,P<:MultivariatePolynomial{R,N,X,T,B}} =
    MultivariatePolynomial{promote_type(R, S),N,X,T,B}

function promote_rule(
    ::Type{P},
    ::Type{Q},
) where {R,N,X,T,B,Y,P<:MultivariatePolynomial{R,N,X,T,B},Q<:UnivariatePolynomial{R,Y}}

    if Y ∈ varnames(P)
        P
    else
        Base.Bottom
    end
end

function (P::Type{MultivariatePolynomial{R,N,X,T,B}})(
    a::MultivariatePolynomial{S,N,X,T,B},
) where {R,N,X,T,B,S}
    P(a.ind, R.(a.coeff))
end

function (P::Type{<:MultivariatePolynomial{R,N,X,T}})(
    a::MultivariatePolynomial{S},
) where {R,N,X,T,S}
    deg(a) <= 0 && return P(LC(a))
    vp = varnames(P)
    va = varnames(a)
    pos = positionsin(va, vp)
    n = length(a.ind)
    pind = Vector{T}(undef, n)
    for i = 1:n
        xa = index2expo(a, i)
        checkpositions(pos, xa, va, vp)
        xp = reindex2(xa, pos, N)
        pind[i] = expo2ordblock(P, xp)
    end
    perm = sortperm(pind)
    pind = pind[perm]
    pc = a.coeff[perm]
    P(pind, pc)
end
function (P::Type{<:MultivariatePolynomial{R,N,X,T}})(
    a::U) where {R,N,X,T,S,U<:UnivariatePolynomial{S}}

    deg(a) <= 0 && return P(LC(a))
    if promote_type(R, U) == R
        b = convert(R, a)
        return P([zeroindex(P)], [b])
    end
    U <: R && return P([zeroindex(P)], [a])

    vp = varnames(P)
    va = varnames(a)
    issubset(va, vp) || throw(ArgumentError("Variable :$(va[1]) not contained in $vp"))
    pos = positionsin(va, vp)
    ac = a.coeff
    n = length(ac)
    pind = Vector{T}(undef, n)
    perm = Vector{Int}(undef, n)
    j = 0
    for i = 1:n
        ii = i + ord(a)
        aci = ac[i]
        if !iszero(aci)
            j += 1
            xa = [ii - 1]
            perm[j] = i
            xp = reindex2(xa, pos, N)
            pind[j] = expo2ordblock(P, xp)
        end
    end
    resize!(perm, j)
    resize!(pind, j)
    P(pind, ac[perm])
end

function (P::Type{<:MultivariatePolynomial{S}})(a::S) where S
    iszero(a) ? zero(P) : P([zeroindex(P)], [a])
end
function (P::Type{<:MultivariatePolynomial{S}})(a::T) where {S,T}
    iszero(a) ? zero(P) : P([zeroindex(P)], [S(a)])
end

deg(p::MultivariatePolynomial) = isempty(p.ind) ? -1 : Base.sum(multideg(p))
isunit(a::MultivariatePolynomial) = deg(a) == 0 && isunit(a.coeff[1])
ismonom(p::MultivariatePolynomial) = length(p.ind) <= 1

function Base.iterate(x::IterTerms{P}, st = typemin(Int)) where {P<:MultivariatePolynomial}
    st = max(st, 1)
    p = x.p
    d = length(p.coeff)
    st > d && return nothing
    q = monom(P, index2expo(p, st))
    q.coeff[1] = p.coeff[st]
    (q, st + 1)
end

"""
    derive(p::MultivariatePolynomial, (d1,...dN))

Derive polynomial with N variables with respect to variables `1` ... `N` with the
respective degrees `d1` ... `dN`.
"""
function derive(p::P, d::NTuple{N,<:Integer}) where {S,N,P<:MultivariatePolynomial{S,N}}
    all(d .>= 0) || throw(ArgumentError("negative derivation degrees not allowed"))
    ind = similar(p.ind)
    coeff = similar(p.coeff)
    j = 0
    for i in eachindex(p.ind)
        a = index2expo(p, i)
        b = a .- d
        if all(b .>= 0)
            c = p.coeff[i]
            for k = 1:N
                for f = a[k]-d[k]+1:a[k]
                    c *= f
                end
            end
            if !iszero(c)
                j += 1
                coeff[j] = c
                ind[j] = expo2ordblock(P, b)
            end
        end
    end
    resize!(coeff, j)
    resize!(ind, j)
    P(ind, coeff)
end

"""
    monom(::Type{<:Polynomial}, expos::Vector{Int}[, lc=LC])

Return monic monomial with given exponent(s). (`monom(Z[:x.:y],[1,2]) == x * y^2`)
"""
function monom(P::Type{<:MultivariatePolynomial}, xv::AbstractVector{<:Integer}, lc = 1)
    n = length(xv)
    n == 0 && return zero(P)
    N = length(varnames(P))
    if length(xv) != N
        throw(ArgumentError(lazy"multivariate monom needs exponents for $N variables"))
    end
    P([expo2ordblock(P, xv)], [lc])
end

"""
    generators(P)

Return an array of all monomial generators (variables) of a polynomial type `P`.
"""
generators(P::Type{<:UnivariatePolynomial}) = [monom(P, 1)]
function generators(P::Type{<:MultivariatePolynomial{S,N}}) where {S,N}
    v = zeros(Int, N)
    res = Vector{P}(undef, N)
    for i = 1:N
        v[i] = 1
        res[i] = monom(P, v)
        v[i] = 0
    end
    res
end

function multideg(p::MultivariatePolynomial{S,N}) where {S,N}
    isempty(p.ind) ? Int[] : index2expo(p, length(p.ind))
end

function LM(p::P) where {S,P<:MultivariatePolynomial{S}}
    n = length(p.ind)
    n == 0 && return zero(P)
    P([p.ind[n]], S[1])
end

function LT(p::P) where {S,P<:MultivariatePolynomial{S}}
    n = length(p.ind)
    n == 0 && return zero(P)
    P([p.ind[n]], [p.coeff[n]])
end

function CC(p::P) where {S,N,P<:MultivariatePolynomial{S,N}}
    getindex(p, zeros(Int, N)...)
end

"""
    index2expo(p::Polynomial, i::Integer)

Return the tuple of variable exponents stored at this index (of `p.ind`).
"""
function index2expo(p::MultivariatePolynomial{S,N,X,<:Integer}, i::Integer) where {S,N,X}
    ord2expo(p.ind[i], N)
end

function index2expo(
    p::MultivariatePolynomial{S,N,X,<:Tuple,B},
    i::Integer,
) where {S,N,X,B<:Tuple}
    vp = tupcon(B)
    m = length(vp)
    vcat([ord2expo(p.ind[i][k], vp[k]) for k = 1:m]...)
end

# arithmetic
function zero(::Type{<:T}) where {S,T<:MultivariatePolynomial{S}}
    T(Int[], S[])
end
function one(::Type{<:T}) where {S,T<:MultivariatePolynomial{S}}
    T([zeroindex(T)], S[1])
end

function splitpoly(p::MultivariatePolynomial, var1, var2, var3...)
    varn = varsrc.([var2, var3...])
    q = splitpoly(p, var1, varn)
    npol(q) = splitpoly(q, var2, var3...)
    coeff = npol.(q.coeff)
    newcoeff(q, vardst(var1), coeff)
end

function newcoeff(q::MultivariatePolynomial, var, c::Vector{S}) where {S}
    R = S[var...]
    R(q.ind, c)
end
function newcoeff(q::UnivariatePolynomial{T,X}, var, c::Vector{S}) where {S,T,X}
    R = S[var...]
    R(q.first, c, NOCHECK)
end

"""
    splitpoly(p::MultivariatePolynomial, var1, var2)

Construct a new polynomial with variables `var1` of polynomials with variables `var2`.

The sets of variable names `var1` and `var2` must be disjoint subsets
of the varnames of `p`.
"""
function splitpoly(p::MultivariatePolynomial{T}, var1, var2) where T<:Ring
    vdq = vardst.(var1)
    vde = vardst.(var2)
    vsq = vecsym(varsrc.(var1))
    vse = vecsym(varsrc.(var2))
    vp = varnames(p)
    allunique(Iterators.flatten((vsq, vse))) || throw(ArgumentError("duplicate var names"))
    Set(vp) == Set(vse) ∪ Set(vsq) || throw(ArgumentError("inconsistent old var names"))
    allunique(vde) && allunique(vdq) || throw(ArgumentError("new var names not unique"))
    length(vecsym(vdq)) == length(vsq) || throw(ArgumentError("insufficient vars in var1"))
    length(vecsym(vde)) == length(vse) || throw(ArgumentError("insufficient vars in var2"))

    E = T[vde...]
    Q = E[vdq...]
    _splitpoly(p, E, Q, vse, vsq)
end

function _splitpoly(
    p::MultivariatePolynomial{T},
    ::Type{E},
    ::Type{Q},
    ve,
    vq,
) where {T<:Ring,E,Q<:MultivariatePolynomial}
    vp = varnames(p)
    xe = findin(vp, ve)
    xq = findin(vp, vq)
    pq = zero(Q)
    qind = similar(pq.ind)
    qcoeff = similar(pq.coeff)
    pe = zero(E)
    for i in axes(p.ind, 1)
        c = p.coeff[i]
        e = index2expo(p, i)
        ee = e[xe]
        eq = e[xq]
        indq = expo2ordblock(Q, eq)
        iq = findfirst(isequal(indq), qind)
        if iq === nothing
            push!(qind, indq)
            push!(qcoeff, monom(E, ee) * E(c))
        else
            qcoeff[iq] += monom(E, ee) * E(c)
        end
    end
    Q(qind, qcoeff)
end

function _splitpoly(
    p::MultivariatePolynomial{T},
    ::Type{E},
    ::Type{Q},
    ve,
    vq,
) where {T<:Ring,E,Q<:UnivariatePolynomial}
    vp = varnames(p)
    xe = findin(vp, ve)
    xq = findin(vp, vq)[1]
    q = zero(Q)
    for i in axes(p.ind, 1)
        c = p.coeff[i]
        e = index2expo(p, i)
        ee = e[xe]
        eq = e[xq]
        q += monom(Q, eq) * (monom(E, ee) * E(c))
    end
    q
end

function findin(all, some)
    findfirst.(isequal.(some), Ref(all))
end

varsrc(a::Any) = a
varsrc(a::Pair) = first(a)
vardst(a::Any) = a
vardst(a::Pair) = last(a)

vecsym(a::AbstractVector{<:Symbol}) = a
vecsym(a::AbstractVector{<:AbstractVector{<:Symbol}}) = vcat(vecsym.(a)...)

"""
    joinpoly(p::Polynomial{<:Polynomial}, var)

Convert polynomial of polynomials to multivariate polynomial with variables `var`.
"""
function joinpoly(p::P, var) where {T,E<:Polynomial{T},P<:Polynomial{E}}
    Q = T[var...]
    vp = varnames(P)
    ve = varnames(E)
    vq = varnames(Q)
    isempty(intersect(ve, vp)) || throw(ArgumentError("overlapping var names"))
    Set(vq) == Set(union(ve, vp)) || throw(ArgumentError("varnames not complete"))
    xe = findin(vq, [vp; ve])
    itp = IterTerms(p)
    r = zero(Q)
    for tp in itp
        q = LC(tp)
        itq = IterTerms(q)
        ep = multideg(tp)
        for tq in itq
            c = LC(tq)
            eq = multideg(tq)
            r += monom(Q, [ep; eq][xe], c)
        end
    end
    r
end

-(p::T) where T<:MultivariatePolynomial = T(p.ind, -p.coeff)
-(a::T, b::T) where T<:MultivariatePolynomial = +(a, -b)
function *(p::T, a::Integer) where T<:MultivariatePolynomial
    iszero(a) && return zero(T)
    isone(a) && return p
    pc = p.coeff .* a
    pind = copy(p.ind)
    for i = length(pc):-1:1
        if iszero(pc[i])
            deleteat!(pind, i)
            deleteat!(pc, i)
        end
    end
    T(pind, pc)
end

*(a::Integer, p::T) where T<:MultivariatePolynomial = p * a
==(a::T, b::T) where T<:MultivariatePolynomial = a.ind == b.ind && a.coeff == b.coeff
function hash(a::MultivariatePolynomial, h::UInt)
    n = deg(a)
    n < 0 ? hash(0, h) : n == 0 ? hash(LC(a), h) : hash(a.ind, hash(a.coeff, h))
end
function Base.isless(a::T, b::T) where T<:MultivariatePolynomial
    m = length(a.ind)
    n = length(b.ind)
    if m == 0
        n != 0
    elseif n == 0
        false
    else
        a.ind[m] < b.ind[n]
    end
end

function +(a1::T, a2::T...) where T<:MultivariatePolynomial
    a = (a1, a2...)
    n = length(a)
    n > 0 || throw(ArgumentError("+ requires at least one argument"))
    n == 1 && return a1
    c = similar(a1.coeff)
    d = similar(a1.ind)
    j = 0
    p = ones(Int, n)
    pm = [mindex(x, 1) for x in a]
    bound = maxindex(T)

    while true
        m, imin = findmin(pm)
        m == bound && break
        cj = a[imin].coeff[p[imin]]
        p[imin] += 1
        pm[imin] = mindex(a[imin], p[imin])
        for i = imin+1:n
            if pm[i] == m
                cj += a[i].coeff[p[i]]
                p[i] += 1
                pm[i] = mindex(a[i], p[i])
            end
        end
        if !iszero(cj)
            j += 1
            if j > length(d)
                resize!(d, 2 * j)
                resize!(c, 2 * j)
            end
            d[j] = m
            c[j] = cj
        end
    end
    resize!(c, j)
    resize!(d, j)
    T(d, c)
end

function *(a::T, b::T) where {N,S,T<:MultivariatePolynomial{S,N}}
    m = length(a.ind)
    n = length(b.ind)
    m >= n || return *(b, a)
    n == 0 && return zero(T)

    c = similar(a.coeff)
    d = similar(a.ind)
    j = 0
    p = ones(Int, n)
    pm = [exposum(a, 1, b, j) for j = 1:n]
    bound = maxindex(T)

    while true
        min, imin = findmin(pm)
        min == bound && break
        cj = a.coeff[p[imin]] * b.coeff[imin]
        p[imin] += 1
        pm[imin] = exposum(a, p[imin], b, imin)
        for i = imin+1:n
            if pm[i] == min
                cj += a.coeff[p[i]] * b.coeff[i]
                p[i] += 1
                pm[i] = exposum(a, p[i], b, i)
            end
        end
        if !iszero(cj)
            j += 1
            if j > length(d)
                resize!(d, 2 * j)
                resize!(c, 2 * j)
            end
            d[j] = min
            c[j] = cj
        end
    end
    resize!(c, j)
    resize!(d, j)
    T(d, c)
end

(p::MultivariatePolynomial)(a, b...) = evaluate(p, a, b...)
function evaluate(
    p::T,
    a::Union{Ring,Int,Rational}...,
) where {N,S,T<:MultivariatePolynomial{S,N}}
    length(a) != N &&
        throw(ArgumentError("wrong number of arguments of polynomial with $N variables"))
    n = length(p.ind)
    R = promote_type(S, typeof.(a)...)
    deg(p) < 0 && return zero(R)
    deg(p) == 0 && return R(p.coeff[1])
    vdeg = maximum(hcat(index2expo.(p, 1:n)...); dims = 2)
    xpot = [Vector{R}(undef, vdeg[i]) for i = 1:N]
    # precalculate all required monoms.
    for i = 1:N
        m = vdeg[i]
        if m > 0
            ai = bi = a[i]
            xpot[i][1] = bi
            for k = 2:m
                bi *= ai
                xpot[i][k] = bi
            end
        end
    end
    s = zero(R)
    for j = 1:n
        ex = index2expo(p, j)
        t = p.coeff[j]
        for i = 1:N
            if ex[i] > 0
                t *= xpot[i][ex[i]]
            end
        end
        s += t
    end
    s
end
"""
    expo2ordblock(::Type{<:Polynomial}, a::Vector{Int})

Return `Integer` or tuple of `Integer` representing the monomial ordering.
In the first case, or if the tuple has length one, that is the `:grevlex` order,
otherwise a block order, based on `:grevlex`, including `:lex`, if each variable
block consists of one variable.
"""
function expo2ordblock(
    ::Type{P},
    a::AbstractVector{<:Integer},
) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    expo2ord(a)
end

function expo2ordblock(
    ::Type{P},
    a::AbstractVector{<:Integer},
) where {R,N,X,T,Y<:Tuple{T,Vararg{T}},B,P<:MultivariatePolynomial{R,N,X,Y,B}}

    t = tupcon(B)
    M = length(Y.parameters)
    res = Vector{T}(undef, M)
    j = 0
    for i = 1:M
        d = t[i]
        res[i] = expo2ord(a[j+1:j+d])
        j += d
    end
    tuple(res...)
end

# extract constants from Tuple{1,2,3...}
tupcon(::Type{Tuple{A}}) where A = (A,)
tupcon(::Type{Tuple{A,B}}) where {A,B} = (A, B)
tupcon(A::Type{<:Tuple}) = tuple(A.parameters...)

#= Tuple mappings. See for reference:
https://stackoverflow.com/questions/26932409/compact-storage-coefficients-of-a-multivariate-polynomial
https://en.wikipedia.org/wiki/Combinatorial_number_system

This constructs the degrevlex total ordering of monomials.
=#

"""
    expo2ord(a)

bijective mapping from tuples of non-negative integers to positive integers.

The induced order of tuples is `degrevlex`.
"""
function expo2ord(a::AbstractVector{<:Integer})
    c = similar(a)
    d = length(a)
    d == 0 && return c + 1
    ci = s = sum = a[1]
    for i = 2:d
        s += a[i]
        ci = s + i - 1
        sum += binomial(ci, i)
    end
    sum + 1
end

"""
    ord2expo(n, d)

bijective mapping from integers to `d`-tuples of integers.

The induced order of tuples is `degrevlex`.
"""
function ord2expo(n::T, d::Int) where T<:Integer
    c = Vector{T}(undef, d)
    n < 1 && throw(ArgumentError("index must be positive but is $n"))
    n -= 1
    for i = d:-1:1
        ci, b = cbin(n, i)
        c[i] = ci
        n -= b
    end
    ci = c[d]
    for i = d:-1:2
        cp = c[i-1]
        c[i] = ci - cp - 1
        ci = cp
    end
    c
end

"""
    cbin(n, d)

Calculate the greatest integer `c` such that `binomial(c, d) <= n`
"""
function cbin(n::T, d::Int) where T<:Integer
    d <= 0 && throw(ArgumentError("tuple size > 0 required, but is $d"))
    d == 1 && return n, n
    n == 0 && return d - 1, n
    n == 1 && return d, n
    c = T(floor((n * sqrt(2pi * d))^(1 / d) * d / ℯ + d / 2))
    if c <= d
        c = d
        b = T(1)
    else
        b = binomial(c, d)
    end
    b == n && return c, b
    bp = b
    while b <= n
        bp = b
        c += 1
        b = b * c ÷ (c - d)
    end
    b >= n > bp && return c - 1, bp
    while b > n
        bp = b
        b = b * (c - d) ÷ c
        c -= 1
    end
    return c, b
end

# the isless function for the `degrevlex` ordering of monomial exponents
function degrevlex(a::V, b::V) where V<:AbstractVector{<:Integer}
    length(a) != length(b) && throw(ArgumentError("lengths of vectors must match"))
    dega = Base.sum(a)
    degb = Base.sum(b)
    dega != degb && return dega < degb
    for j = length(a):-1:1
        aj = a[j]
        bj = b[j]
        if aj != bj
            return bj > aj # mind the reversal!
        end
    end
    false
end

# multiplication of monomials
function indexsum(x::T, y::T, d::Int) where T<:Integer
    x > 0 && y > 0 || return 0
    expo2ord(ord2expo(x, d) + ord2expo(y, d))
end

zeroindex(P::Type{<:MultivariatePolynomial}) = fillindex(one, P)
maxindex(P::Type{<:MultivariatePolynomial}) = fillindex(typemax, P)

function fillindex(
    f,
    ::Type{<:P},
) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    f(T)
end
function fillindex(
    f,
    ::Type{<:MultivariatePolynomial{R,N,X,Tuple{T,Vararg{T,M}}}},
) where {R,N,X,M,T}
    ft = f(T)
    ntuple(x -> ft, M + 1)
end

"""
    exposum(a::Polynomial, i, b::Polynomial, j)

Return the sum of variable exponents at `a.ind[i]` and `b.ind[j].
Realizes multiplication of monomials.
If one of the coefficients is undefined, return `maxindex` symbolizing zero.
"""
function exposum(
    pa::P,
    i::Integer,
    pb::P,
    j::Integer,
) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    a = pa.ind
    b = pb.ind
    (isassigned(a, i) && isassigned(b, j)) || return maxindex(P)
    indexsum(a[i], b[j], N)
end

function exposum(
    pa::P,
    i::Integer,
    pb::P,
    j::Integer,
) where {R,N,X,T,B,P<:MultivariatePolynomial{R,N,X,T,B}}
    a = pa.ind
    b = pb.ind
    (isassigned(a, i) && isassigned(b, j)) || return maxindex(P)
    ai = a[i]
    bi = b[j]
    vp = tupcon(B)
    ntuple(k -> indexsum(ai[k], bi[k], vp[k]), length(ai))
end

function mindex(pa::P, i::Integer) where P<:MultivariatePolynomial
    isassigned(pa.ind, i) ? pa.ind[i] : maxindex(P)
end

function Base.getindex(p::P, a::Integer...) where {S,N,P<:MultivariatePolynomial{S,N}}
    length(a) == N || throw(ArgumentError("wrong number of indices"))
    xp = expo2ordblock(P, collect(a))
    i = findfirst(x -> x >= xp, p.ind)
    if i !== nothing && p.ind[i] == xp
        p.coeff[i]
    else
        zero(S)
    end
end

function divides(x::V, y::V) where V<:AbstractVector{<:Integer}
    all(x .<= y)
end

"""
    varnames(P)

Return array of variable names of polynomial or polynomial type `P`.
"""
varnames(::Type{T}) where {R,X,T<:UnivariatePolynomial{R,X}} = Symbol[X]
varnames(::Type{T}) where T<:MultivariatePolynomial = gettypevar(T).varnames
varnames(p::T) where T<:Polynomial = varnames(T)
varnames(::Type{T}, n::Integer) where T<:MultivariatePolynomial = varblocks(T)[n]

function varblocks(::Type{P}) where {R,N,X,T,B,P<:MultivariatePolynomial{R,N,X,T,B}}
    vars = varnames(P)
    t = tupcon(B)
    M = length(t)
    res = Vector{Vector{Symbol}}(undef, M)
    j = 0
    for i = 1:M
        d = t[i]
        res[i] = vars[j+1:j+d]
        j += d
    end
    res
end
function varblocks(::Type{P}) where P<:UnivariatePolynomial
    [varnames(P)]
end

flatten_varblocks(::Type) = Symbol[]
function flatten_varblocks(::Type{P}) where P<:Polynomial
    vcat(varblocks(P), flatten_varblocks(basetype(P)))
end
flatten_basetype(T::Type) = T
flatten_basetype(::Type{P}) where P<:Polynomial = flatten_basetype(basetype(P))

"""
    flat_polynomial(::Type{<:Polynomial})

Construct polynomial type with a basetype, which is not a polynomial.
"""
function flat_polynomial(::Type{P}) where P<:Polynomial
    getindex(flatten_basetype(P), flatten_varblocks(P)...)
end

function showvar(io::IO, var::MultivariatePolynomial{S,N}, n::Integer) where {N,S}
    ex = index2expo(var, n + 1)
    vn = varnames(var)
    start = true
    for i = 1:N
        x = ex[i]
        x <= 0 && continue
        !start && print(io, '*')
        print(io, vn[i])
        x > 1 && print(io, '^', x)
        start = false
    end
end

function isconstterm(p::P, n::Integer) where P<:MultivariatePolynomial
    n < 0 || p.ind[n+1] == zeroindex(P)
end

"""
    prototype(::Type{<:Polynomial}, n1, n2)

Return polynomial of given type as sum of monic monomials.

The degree of each variable is limited by `n1`, the total degree by `n2`.
"""
function prototype(::Type{P}, n1::Integer = 2, n2::Integer = 0) where P<:Polynomial
    N = length(varnames(P))
    s = P(0)
    n1 = n1 == 0 ? n2 : n1
    n2 = n2 == 0 ? N * n1 : n2
    for ex in _exponents(N, 0:n1)
        if Base.sum(ex) <= n2
            s += monom(P, ex)
        end
    end
    s
end
function _exponents(n::Integer, vals::AbstractVector{<:Integer})
    if n <= 1
        ([x] for x in vals)
    else
        ([x; y] for x in vals for y in _exponents(n - 1, vals))
    end
end


divrem(f::P, id::Ideal{P}) where P<:Polynomial = divrem(f, id.base)

function divrem(f::P, g::P) where P<:MultivariatePolynomial
    if 0 == deg(f) == deg(g)
        return P.(divrem(LC(f), LC(g)))
    end
    a, s, d = pdivrem(f, [g])
    isunit(d) ? (a[1] * inv(d), s * inv(d)) : (zero(P), f)
end
function divrem(f::P, g::AbstractVector{P}) where P<:MultivariatePolynomial
    a, s, d = pdivrem(f, g)
    isunit(d) ? (a .* inv(d), s * inv(d)) : (zeros(P, length(g)), f)
end

# division and Gröbner base calculation

function pdivrem(f::P, g::P) where {T,N,P<:MultivariatePolynomial{T,N}}

    lig = multideg(g)
    xif = 0
    lif = lig
    for i = length(f.ind):-1:1
        li = index2expo(f, i)
        if divides(lig, li)
            lif = li
            xif = i
            break
        end
    end
    xif == 0 && return zero(P), f, one(T)
    c = f.coeff[xif]
    d = LC(g)
    q = monom(P, lif .- lig)
    if isone(d)
        k = q * c
        k, f - g * k, one(T)
    elseif isunit(d)
        k = q * (c / d)
        k, f - g * k, one(T)
    else
        x = gcd(c, d)
        h = d / x
        k = q * (c / x)
        k, f * h - g * k, h
    end
end

function pdivrem(f::P, G::AbstractVector{P}) where {T,P<:MultivariatePolynomial{T}}
    f0 = f
    fp = zero(P)
    a = zeros(P, length(G))
    dd = one(T)
    while f !== fp && !iszero(f)
        fp = f
        for (i, g) in enumerate(G)
            ffp = f
            k, f, d = pdivrem(f, g)
            if f !== ffp
                if !isone(d)
                    a .*= d
                    dd *= d
                end
                a[i] += k
            elseif iszero(f)
                break
            end
        end
    end
    a, f, dd
end

"""
    SPOL(f, g)

Calculate the S-polynomial (`SPOL`) of the polynomials `f`, `g`.
"""
function SPOL(f::P, g::P) where P<:MultivariatePolynomial
    lcf = LC(f)
    lcg = LC(g)
    lif = multideg(f)
    lig = multideg(g)

    h = gcd(lcf, lcg)
    af = lcf / h
    ag = lcg / h
    bf = max.(lif - lig, 0)
    bg = max.(lig - lif, 0)
    monom(P, bg) * ag * f - monom(P, bf) * af * g
end

using Base.Iterators

# find all in one
function buchbergerall(f::AbstractVector{P}) where P<:MultivariatePolynomial
    n = length(f)
    C = [(i, j) for i = 1:n for j = i+1:n]
    buchberger(f, C)
end

# incrementally adding vectors
function buchberger(A::AbstractVector{P}) where P<:MultivariatePolynomial
    n = length(A)
    n == 0 && return P[]
    a = A[1:1]
    for i = 2:n
        a = buchberger(a, A[i:i])
    end
    a
end

# assume f is already gröbner base
function buchberger(f::VP, h::VP) where {P<:MultivariatePolynomial,VP<:AbstractVector{P}}
    n = length(f)
    m = length(h)
    g = vcat(f, h)
    C = [(i, n + j) for i = 1:n for j = 1:m]
    buchberger(g, C)
end

# Buchberger's algorithm - C contains the remaining critical pairs (i,j)
function buchberger(
    f::AbstractVector{P},
    C::Vector{Tuple{Int,Int}},
) where P<:MultivariatePolynomial
    n = length(f)
    g = copy(f)
    while !isempty(C)
        k = select_critical_pair(C, g)
        i, j = C[k]
        p, q = g[i], g[j]
        deleteat!(C, k)
        criterion(g, C, i, j) && continue
        pq = SPOL(p, q)
        a, s, d = pdivrem(pq, g)
        if !iszero(s) && isone(d)
            push!(g, s)
            n += 1
            append!(C, [(i, n) for i = 1:n-1])
            cleanup!(C, g)
        end
    end
    g
end

function select_critical_pair(C::AbstractVector{Tuple{Int,Int}}, g::AbstractVector)
    n = length(C)
    kmin = 1
    return kmin
    degp(k) = Base.sum(max.((multideg(g[C[k][1]])), multideg(g[C[k][2]])))
    dmin = degp(1)
    for k = 2:n
        dk = degp(k)
        if dk < dmin
            dmin = dk
            kmin = k
        end
    end
    kmin
end

function criterion(G::AbstractVector{<:Polynomial}, C::AbstractVector, i::Int, k::Int)
    f = G[i]
    g = G[k]
    fx = multideg(f)
    gx = multideg(g)
    Base.sum(fx .* gx) == 0 && return true # product criterion - no powers in common
    for j in eachindex(G)
        (j == i || j == k) && continue
        hx = multideg(G[j])
        if all(hx .<= max.(fx, gx)) && !in(minmax(i, j), C) && !in(minmax(k, j), C)
            return true # chain criterion - already removed
        end
    end
    return false
end

function cleanup!(C::AbstractVector{Tuple{Int,Int}}, g)
    n = length(C)
    for k = 1:n
        i, j = C[k]
        if i > 0 && j > 0 && criterion(g, C, i, j)
            C[k] = (0, 0)
        end
    end
    for k = n:-1:1
        i, j = C[k]
        if i <= 0
            deleteat!(C, k)
        end
    end
end

# eliminiate generators with leading terms spanned by other leading terms
function minimize!(H::AbstractVector{P}) where P<:MultivariatePolynomial
    n = length(H)
    for i = 1:n
        f = H[i]
        if !iszero(f)
            lif = multideg(H[i])
            for g in H
                if !iszero(g) && f != g
                    if all(lif .>= multideg(g))
                        cf = LC(f)
                        cg = LC(g)
                        if iszero(rem(cf, cg))
                            H[i] = zero(P)
                        end
                    end
                end
            end
        end
    end
    j = 0
    for i = 1:n
        f = H[i]
        if !iszero(f)
            j += 1
            if i != j
                H[j] = f
            end
        end
    end
    resize!(H, j)
    for i = 1:j
        f = H[i]
        lcu = inv(lcunit(f))
        if !isone(lcu)
            f = f * lcu
        end
        H[i] = f
    end
    H
end

# reduced Gröbner base
function reduce!(H::AbstractVector{P}) where P<:Polynomial
    n = length(H)
    for i = 1:n
        f = H[i]
        a, g, c = pdivrem(f, [g for g in H if g != f && !iszero(g)])
        if g !== f && isone(c)
            H[i] = g
        end
    end
    sort_unique!(H; rev = true)
    j = findlast(iszero, H)
    if j !== nothing
        resize!(H, j - 1)
    end
    H
end

"""
    groebnerbase(H::AbstractVector{<:Polynomial})

Calculate the reduced groebner base from a set of generators of an ideal `<H>`.

see for example:
https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis
http://www.crypto.rub.de/imperia/md/content/may/12/ws1213/kryptanal12/13_buchberger.pdf
"""
function groebnerbase(H::AbstractVector{P}) where P<:Polynomial
    buchberger(H) |> minimize! |> reduce!
end

# utility functions
"""
    positionsin(va, vb)

Return integer array of the same size as va. Element `i` is the index of first `va[i]`
in `vb` or zero, if missing.
"""
function positionsin(va::T, vb::T) where T<:AbstractVector
    n = length(va)
    res = Vector{Int}(undef, n)
    for i = 1:n
        p = findfirst(isequal(va[i]), vb)
        res[i] = ifelse(p === nothing, 0, p)
    end
    res
end

"""
    reindex2(values, pos, n)

Return an array of integers of size `n` such that `result[pos] = val`.
Default values in `result` are zero.
The indices with `pos[i] == 0` are silently ignored.
"""
function reindex2(xa::AbstractVector, pos::AbstractVector{<:Integer}, n::Integer)
    res = zeros(Int, n)
    for i in eachindex(pos)
        posi = pos[i]
        if posi != 0
            res[posi] = xa[i]
        end
    end
    res
end

function checkpositions(pos::AbstractVector{<:Integer}, xa::AbstractVector, va, vp)
    findfirst(iszero, pos) === nothing && return pos
    i = findfirst(i -> iszero(pos[i]) && !iszero(xa[i]), eachindex(pos))
    if i !== nothing
        throw(ArgumentError("Variable :$(va[i]) not contained in $vp."))
    end
end

struct SymIter
    n::Int
    m::Int
end

"""
    elementary_symmetric(::Type{Polynomial}, β::Integer)

Return the elementary symmetric function `Eᵦ` of degree `0 <= β <= N`.
Return zero polynomial for other `β`.
"""
function elementary_symmetric(
    ::Type{P},
    m::Integer,
) where {S,N,P<:MultivariatePolynomial{S,N}}
    Base.sum(monom.(P, collect(SymIter(N, m))))
end

function elementary_symmetric(::Type{P}, m::Integer) where P<:UnivariatePolynomial
    0 <= m <= 1 ? monom(P, m) : zero(P)
end


Base.length(a::SymIter) = binomial(a.n, a.m)
Base.iterate(a::SymIter) =
    a.n >= a.m >= 0 ? (s = collect(1:a.m); (vset(a.n, s), s)) : nothing
function Base.iterate(a::SymIter, s::Vector)
    t = copy(s)
    m, n = a.m, a.n
    for i = 0:m-1
        ti = t[m-i]
        if ti < n - i
            for j = m-i:m
                t[j] = (ti += 1)
            end
            return vset(n, t), t
        end
    end
    return nothing
end
function vset(n::Integer, v)
    z = zeros(Int, n)
    for i in v
        z[i] = 1
    end
    z
end

"""
    newton_symmetric(p::Polynomial)

For a multivariate polynomial which is symmetric in all variables
(the polynomial does not change if you apply any permutation to the variables)
represent the polynomial by a polynomial of the elementary symmetric functions.
The result is a polynomial of the same element type as the input, but the variables
have the meaning of E₁, E₂, ... and lexical ordering is applied.

If the input is not symmetric, throw an `ArgumentError`.

The algorithm is due to Newton's Theorem on Symmetric Polynomials.
"""
function newton_symmetric(p::P) where {S,P<:MultivariatePolynomial{S}}
    G = generators(P)
    n = size(G, 1)
    vars = ([Symbol("E(", i, ")")] for i = 1:n)
    Q = S[vars...]
    z = zero(Q)
    while !iszero(p)
        v = sort!(multideg(p); rev = true)
        expo = [[v[i] - v[i+1] for i = 1:n-1]; v[n]]
        iszero(z[expo...]) || throw(ArgumentError("input polynomial is not symmetric"))
        lc = p[v...]
        z += monom(Q, expo) * lc
        p -= prod(elementary_symmetric(P, i)^expo[i] for i = 1:n) * lc
    end
    z
end
