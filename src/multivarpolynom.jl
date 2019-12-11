
# class constructors
# convenience type constructor:
# enable `R[:x,:y,:z,...]` as short for `MultivariatePolynomial{R,N,Id}`
function getindex(R::Type{<:Ring}, s::Symbol, t::Symbol...)
    vs = collect((s, t...))
    N = length(vs)
    Id = sintern(vs)
    new_class(MultivariatePolynomial{R,N,Id,Int,Tuple{N}}, vs)
end
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
    N = length(vs)
    Id = sintern(vs)
    n = length(blocks)
    T = n == 1 ? Int : NTuple{n,Int}
    B = Tuple{[length(x) for x in blocks]...}
    new_class(MultivariatePolynomial{R,N,Id,T,B}, vs)
end

import Base: copy, convert, promote_rule
import Base: +, -, *, zero, one, ==, hash, isless, iszero, isone

(::Type{P})(a) where {N,T,P<:MultivariatePolynomial{T,N}} = convert(P, a)
copy(a::MultivariatePolynomial) = a
basetype(::Type{<:MultivariatePolynomial{T}}) where T = T

# promotion and conversion
_promote_rule(::Type{<:MultivariatePolynomial{R,M,X}}, ::Type{<:Polynomial}) where {X,M,R} = Base.Bottom
_promote_rule(::Type{MultivariatePolynomial{R,N,X,T,B}}, ::Type{MultivariatePolynomial{S,N,X,T,B}}) where {X,N,R,S,T,B} = MultivariatePolynomial{promote_type(R,S),N,X,T,B}
_promote_rule(::Type{P}, ::Type{S}) where {R,N,X,B,T,S<:Ring,P<:MultivariatePolynomial{R,N,X,T,B}} = MultivariatePolynomial{promote_type(R,S),N,X,T,B}
promote_rule(::Type{P}, ::Type{S}) where {R,N,X,T,B,S<:Union{Integer,Rational},P<:MultivariatePolynomial{R,N,X,T,B}} = MultivariatePolynomial{promote_type(R,S),N,X,T,B}

function convert(P::Type{MultivariatePolynomial{R,N,X,T,B}}, a::MultivariatePolynomial{S,N,X,T,B}) where {R,N,X,T,B,S}
    P(a.ind, convert.(R, a.coeff))
end
function convert(P::Type{<:MultivariatePolynomial{R,N,X,T}}, a::MultivariatePolynomial{S}) where {R,N,X,T,S}

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
function convert(P::Type{<:MultivariatePolynomial{R,N,X,T}}, a::UnivariatePolynomial{S}) where {R,N,X,T,S}

    deg(a) <= 0 && return P(LC(a))
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
        aci = ac[i]
        if !iszero(aci)
            j += 1
            xa = [i-1]
            perm[j] = i
            xp = reindex2(xa, pos, N)
            pind[j] = expo2ordblock(P, xp)
        end
    end
    resize!(perm, j)
    resize!(pind, j)
    P(pind, ac[perm])
end

function convert(P::Type{<:MultivariatePolynomial{S}}, a::S) where S
    iszero(a) ? zero(P) : P(one(P).ind, [a])
end
function convert(P::Type{<:MultivariatePolynomial{S}}, a::T) where {S,T}
    iszero(a) ? zero(P) : P(one(P).ind, [convert(S, a)])
end

deg(p::MultivariatePolynomial) = isempty(p.ind) ? -1 : sum(multideg(p))
isunit(a::MultivariatePolynomial) = deg(a) == 0 && isunit(a.coeff[1])
ismonom(p::MultivariatePolynomial) = length(p.ind) <= 1

"""
    monom(<:MultivariatePolynomial, expos::Vector{Int})

Return monic monomial with given exponents. (`[1,0,...]` corresponds to first variable). 
"""
function monom(P::Type{<:MultivariatePolynomial{S,N}}, xv::Vector{<:Integer}) where {N,S}
    n = length(xv)
    n == 0 && return zero(P)
    length(xv) != N && throw(ArgumentError("multivariate monom needs exponents for all $N variables"))
    P([expo2ordblock(P, xv)], [1])
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

function LM(p::P) where {S,N,P<:MultivariatePolynomial{S,N}}
    n = length(p.ind)
    n == 0 && return zero(P)
    P([p.ind[n]], S[1])
end

function LT(p::P) where {S,N,P<:MultivariatePolynomial{S,N}}
    n = length(p.ind)
    n == 0 && return zero(P)
    P([p.ind[n]], [p.coeff[n]])
end

"""
    index2expo(p::Polynomial, i::Integer)

Return the tuple of variable exponents stored at this index (of `p.ind`.
"""
function index2expo(p::MultivariatePolynomial{S,N,X,<:Integer}, i::Integer) where {S,N,X}
    ord2expo(p.ind[i], N)
end

function index2expo(p::MultivariatePolynomial{S,N,X,<:Tuple,B}, i::Integer) where {S,N,X,B<:Tuple}
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

iszero(p::MultivariatePolynomial) = length(p.ind) == 0
isone(p::MultivariatePolynomial) = iszero(multideg(p)) && isone(LC(p))

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
==(a::T, b::T) where T<:MultivariatePolynomial = a.ind == b.ind && a.coeff == a.coeff
function hash(a::MultivariatePolynomial, h::UInt)
    n = deg(a)
    n < 0 ? hash(0, h) : n == 0 ? hash(LC(a), h) : hash(a.ind, hash(a.coeff, h))
end
function isless(a::T, b::T) where T<:MultivariatePolynomial
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

function +(a::T...) where T<:MultivariatePolynomial
    n = length(a)
    n >  0 || throw(ArgumentError("+ requires at least one argument"))
    n == 1 && return a[1]
    c = similar(a[1].coeff)
    d = similar(a[1].ind)
    j = 0
    p = ones(Int, n)
    pm = [getindex(x, 1) for x in a]
    bound = maxindex(T)
    
    while true
        m, imin = findmin(pm)
        m == bound && break
        cj = a[imin].coeff[p[imin]]
        p[imin] += 1
        pm[imin] = getindex(a[imin], p[imin])
        for i = imin+1:n
            if pm[i] == m
                cj += a[i].coeff[p[i]]
                p[i] += 1
                pm[i] = getindex(a[i], p[i])
            end
        end
        if !iszero(cj)
            j += 1
            if j > length(d)
                resize!(d, 2*j)
                resize!(c, 2*j)
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
    pm = [exposum(a, 1, b, j) for j in 1:n]
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
                resize!(d, 2*j)
                resize!(c, 2*j)
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
function evaluate(p::T, a::Union{Ring,Int,Rational}...) where {N,S,T<:MultivariatePolynomial{S,N}}
    length(a) != N && throw(ArgumentError("wrong number of arguments of polynomial with $N variables"))
    n = length(p.ind)
    R = promote_type(S, typeof.(a)...)
    deg(p) < 0 && return zero(R)
    deg(p) == 0 && return R(p.coeff[1])
    vdeg = maximum(hcat(index2expo.(p, 1:n)...), dims=2)
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
function expo2ordblock(::Type{P}, a::AbstractVector{<:Integer}) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    expo2ord(a)
end

function expo2ordblock(::Type{P}, a::AbstractVector{<:Integer}) where {R,N,X,T,M,B,P<:MultivariatePolynomial{R,N,X,NTuple{M,T},B}}

    t = tupcon(B)
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
    n == 0 && return d-1, n
    n == 1 && return d, n
    c = T(floor((n * sqrt(2pi*d))^(1/d) * d / ℯ + d/2))
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
        b = b * c ÷ (c-d)
    end
    b >= n > bp && return c-1, bp
    while b > n
        bp = b
        b = b * (c-d) ÷ c
        c -= 1
    end
    return c, b
end

# the isless function for the `degrevlex` ordering of monomial exponents
function degrevlex(a::V, b::V) where V<:AbstractVector{<:Integer}
    length(a) != length(b) && throw(ArgumentError("lengths of vectors must match"))
    dega = sum(a)
    degb = sum(b)
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

function fillindex(f, ::Type{<:P}) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    f(T)
end
function fillindex(f, ::Type{<:P}) where {R,N,X,T,M,P<:MultivariatePolynomial{R,N,X,NTuple{M,T}}}
    ft = f(T)
    ntuple(x->ft, M)
end

"""
    exposum(a::Polynomial, i, b::Polynomial, j)

Return the sum of variable exonents at `a.ind[i]` and `b.ind[j].
Realizes multiplication of monomials.
If one of the coefficients is indefined, return `maxindex` symbolizing zero.
"""
function exposum(pa::P, i::Integer, pb::P, j::Integer) where {R,N,X,T,P<:MultivariatePolynomial{R,N,X,T,Tuple{N}}}
    a = pa.ind
    b = pb.ind
    (isassigned(a, i) && isassigned(b, j)) || return maxindex(P)
    indexsum(a[i], b[j], N)
end

function exposum(pa::P, i::Integer, pb::P, j::Integer) where {R,N,X,T,B,P<:MultivariatePolynomial{R,N,X,T,B}}
    a = pa.ind
    b = pb.ind
    (isassigned(a, i) && isassigned(b, j)) || return maxindex(P)
    ai = a[i]
    bi = b[j]
    vp = tupcon(B)
    ntuple(k->indexsum(ai[k], bi[k], vp[k]), length(ai))
end

function getindex(pa::P, i::Integer) where P<:MultivariatePolynomial
    isassigned(pa.ind, i) ? pa.ind[i] : maxindex(P)
end

function divides(x::V, y::V) where V<:AbstractVector{<:Integer}
    all(x .<= y)
end

"""
    varnames(P)

Return array of variabel names of polynomial or polynomial type `P`.
"""
varnames(::Type{T}) where {R,X,T<:UnivariatePolynomial{R,X}} = Symbol[X]
varnames(::Type{T}) where T<:MultivariatePolynomial = gettypevar(T).varnames
varnames(p::T) where T<:Polynomial = varnames(T)

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

function showvar(io::IO, var::MultivariatePolynomial{S,N}, n::Integer) where {N,S}
    ex = index2expo(var, n)
    vn = varnames(var)
    start = true
    for i = 1:N
        x = ex[i]
        x <= 0 && continue
        !start && print(io, '⋅')
        print(io, vn[i])
        x > 1 && print(io, '^', x)
        start = false
    end
end

function isconstterm(p::P, n::Integer) where P<:MultivariatePolynomial
    n <= 0 || p.ind[n] == zeroindex(P)
end

divrem(f::P, id::Ideal{P}) where P<:Polynomial = divrem(f, id.base)

function divrem(f::P, g::Union{AbstractVector{P},P}) where P<:MultivariatePolynomial
    a, s, d = pdivrem(f, g)
    isone(d) ? (a, s) : (zero(P), f)
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

# find initial Gröbner base using Buchberger's algorithm
function buchberger(f::AbstractVector{P}) where P<:MultivariatePolynomial
    n = length(f)
    C = [(i,j) for i=1:n for j = i+1:n]
    buchberger(f, C)
end

# assume f and h are already gröbner base
function buchberger(f::VP, h::VP) where {P<:MultivariatePolynomial,VP<:AbstractVector{P}}
    n = length(f)
    m = length(h)
    g = vcat(f, h)
    C = [(i,n+j) for i = 1:n for j = 1:m]
    buchberger(g, C)
end

function buchberger(f::AbstractVector{P}, C::Vector{Tuple{Int,Int}}) where P<:MultivariatePolynomial
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
            cleanup!(C, g)
            n += 1
            append!(C, [(i,n) for i = 1:n-1 if !criterion(g, C, i, n)])
        end
    end
    g
end

function select_critical_pair(C::AbstractVector{Tuple{Int,Int}}, g::AbstractVector)
    n = length(C)
    kmin = 1
    return kmin
    degp(k) = sum(max.((multideg(g[C[k][1]])), multideg(g[C[k][2]])))
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
    sum(fx .* gx) == 0 && return true # product criterion - no powers in common
    for j = 1:length(G)
        (j == i || j == k) && continue
        hx = multideg(G[j])
        if all(hx .<= max.(fx, gx)) && !in(minmax(i, j), C) && !in(minmax(k,j), C)    
            return true # chain criterion - already removed
        end
    end
    return false
end

function cleanup!(C::AbstractVector{Tuple{Int,Int}}, g)
    for k = 1:length(C)
        i, j = C[k]
        if i > 0 && j > 0 && criterion(g, C, i, j)
            C[k] = (0, 0)
        end
    end
    for k = length(C):-1:1
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
    sort_unique!(H, rev=true)
    j = findlast(iszero, H)
    if j !== nothing
        resize!(H, j-1)
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
    for i = 1:length(pos)
        posi = pos[i]
        if posi != 0
            res[posi] = xa[i]
        end
    end
    res
end

function checkpositions(pos::AbstractVector{<:Integer}, xa::AbstractVector, va, vp)
    findfirst(iszero, pos) == nothing && return pos
    i = findfirst(i->iszero(pos[i]) && !iszero(xa[i]), 1:length(pos))
    if i != nothing
        throw(ArgumentError("Variable :$(va[i]) not contained in $vp."))
    end
end
