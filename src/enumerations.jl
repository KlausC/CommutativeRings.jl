
import Base: length, iterate, eltype
export Monic

struct Monic{T<:QuotientRing,X}
    n::Int
    Monic(::Type{P}, n) where {X,T,P<:UnivariatePolynomial{T,X}} = new{T,X}(n)
end
eltype(::Type{Z}) where Z<:Ring = Z
length(::Type{Z}) where Z<:Ring = order(Z)

function iterate(::Type{Z}) where Z<:QuotientRing
    z = zero(Z)
    (z, z)
end
function iterate(::Type{Z}, s) where Z<:ZZmod
    v = Z(s.val + 1)
    iszero(v) ? nothing : (v, v)
end
function iterate(::Type{Q}, s) where {Z<:ZZmod,P<:UnivariatePolynomial{Z},Q<:Quotient{P}}
    c = copy(s.val.coeff)
    m = length(c)
    n = deg(modulus(Q))
    for i = 1:m
        ci = next(c[i])
        if ci !== nothing
            c[i] = ci
            z = Q(c)
            return (z, z)
        else
            c[i] = zero(Z)
        end
    end
    if m < n
        resize!(c, m+1)
        c[m+1] = one(Z)
        m >= 1 && (c[m] = zero(Z))
        z = Q(c)
        return (z, z)
    end
    nothing
end

function next(c)
    cs = iterate(typeof(c), c)
    cs === nothing ? nothing : cs[1]
end

function iterate(::Type{G}) where G<:GaloisField
    G[0], 0
end

function iterate(::Type{G}, s::Integer) where G<:GaloisField
    s += 1
    s >= order(G) && return nothing
    G[s], s
end

function next(g::G) where G<:GaloisField
    s = gettypevar(G).exptable[g.val+1] + 1
    s >= order(G) ? nothing : G[s]
end

Base.length(mo::Monic{Z,X}) where {X,Z<:Ring} = length(Z)^mo.n
Base.eltype(::Monic{Z,X}) where {X,Z<:Ring} = Z[X]
function Base.iterate(mo::Monic{Z,X}) where {X,Z<:Ring}
    p0 = monom(Z[X], mo.n)
    p0, p0
end
function Base.iterate(mo::Monic{Z,X}, s) where {X,Z<:Ring}
    c = copy(s.coeff)
    n = deg(s)
    for i = 1:n
        ci = next(c[i])
        if ci !== nothing
            c[i] = ci
            z = Z[X](c)
            return (z, z)
        else
            c[i] = zero(Z)
        end
    end
    nothing
end
    

isqrt2(i::T) where T<:Integer = T(floor(sqrt(8*i+1) - 1)) ÷ 2
function ipair(i::Integer)
    m = isqrt2(i)
    c = m * (m + 1) ÷ 2
    m - i + c, i - c
end

# assume n1 == 0, n2 == 0 means no limitation
function index(i::T, n1::T, n2::T) where T<:Integer
    (n1 >= 0 && n2 >= 0) || throw(ArgumentError("(n1, n2) = $((n1, n2)) >= 0 required"))
    0 <= i || throw(ArgumentError("no negative index: $i"))
    if n1 > 0 && n2 > 0
        i = n1 * n2 <= 0 ? i : mod(i, n1 * n2)
    end
    m1, m2 = (n2 == 0) || (0 < n1 <= n2) ? (n1, n2) : (n2, n1)
    m = (m1 + 1) * m1 ÷ 2
    if m1 == 0 || i < m
        ipair(i)
    else
        j = i - m
        if m2 == 0 || j < (m2 - m1) * m1
            j1, j2 = fldmod(j, m1)
            s = n1 == m1 ? n1 - j2 - 1 : j1 + m1 - j2
            t = j1 + m1 - s
            s, t
        else
            s, t = index(n1 * n2 - 1 - i, n1, n2)
            n1 - s - 1, n2 - t - 1
        end
    end
end

function indexv(i::T, nn::Vector{T}) where T<:Integer
    m = length(nn)
    m == 0 && return T[]
    n1 = nn[1]
    m == 1 && return [n1 == 0 ? i : mod(i, n1)]
    m == 2 && return [index(i, n1, nn[2])...]
    m2 = m >> 1
    n1 = prod(nn[1:m2])
    n2 = prod(nn[m2+1:m])
    s, t = index(i, n1, n2)
    vcat(indexv(s, nn[1:m2]), indexv(t, nn[m2+1:m]))
end

len(::Type, d...) = 0
len(T::Type{<:ZZmod}, d...) = modulus(T)
function len(T::Type{<:FractionRing{S}}, d...) where S
    n = len(S, d...)
    n == 0 ? 0 : (n-1)^2 + 1
end
len(T::Type{UnivariatePolynomial{S}}, d::Integer) where S = intpower(len(S), d)
len(T::Type{<:QuotientRing{S}}) where S<:UnivariatePolynomial = len(S, deg(modulus(T)-1))
len(T::Type{<:GaloisField}) = order(T)

ofindex(a::Integer, T::Type{<:Unsigned}) = T(a)
ofindex(a::Integer, T::Type{<:Signed}) = iseven(a) ? -(T(a) >> 1) : T(a+1) >> 1
ofindex(a::Integer, T::Type{ZZ{S}}) where S = T(ofindex(a, S))
ofindex(a::Integer, T::Type{<:ZZmod{m,S}}) where {m,S} = T(ofindex(a, unsigned(S)))
function ofindex(a::Integer, T::Type{<:QuotientRing{S}}) where {S<:UnivariatePolynomial}
    d = deg(modulus(T))
    T(ofindex(a, S, d) - monom(S,d))
end

function ofindex(a::Integer, T::Type{<:FractionRing{S}}) where S
    a == 0 && return zero(T)
    s, t = index(a - 1, len(T), len(T))
    T(ofindex(t+1, S), S(ofindex(s + 1, unsigned(S))))
end
function ofindex(a::Integer, P::Type{<:UnivariatePolynomial{S}}, d::Integer) where S
    P([ofindex.(indexv(a, fill(oftype(a, len(S)), d)), S); 1])
end
function ofindex(a::Integer, G::Type{<:GaloisField})
    G[mod(a, order(G))]
end

struct Factors{T<:Integer,P}
   f::P
   Factors(x::V) where {T,V<:AbstractVector{<:Pair{T}}} = new{T,V}(x)
end
Base.length(fi::Factors) = isempty(fi.f) ? 1 : prod(x+1 for x in _values(fi.f))

_values(d::AbstractDict) = values(d)
_values(d::Vector{<:Pair}) = (last(x) for x in d)

Base.iterate(fi::Factors) = (1, zeros(Int,length(fi.f)))
function Base.iterate(fi::Factors, s::Array{Int})
    f = fi.f
    n = length(f)
    n == 0 && return nothing
    for i = 1:n
        si = s[i]
        if si < last(f[i])
            s[i] = si + 1
            break
        else
            i == n && return nothing
            s[i] = 0
        end
    end
    p = prod(first(f[i])^s[i] for i = 1:n)
    p, s
end
"""
    factors(n)
    factors(Primes.factor(n))

Return an iterator generating all factors of integer `n`.
"""
factors(f::Primes.Factorization) = Factors(f.pe)
factors(f::AbstractVector) = Factors(f)
factors(n::Integer) = factors(factor(n).pe)

