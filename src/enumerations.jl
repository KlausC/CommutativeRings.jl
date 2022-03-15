
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

"""
    select_k_from_n(x, n, k)

For `x` in the range `1:binomial(n,k)` find subset of size `k` from `1:n` with number `x`.
Each suset is represented by an ordered vector of integers.
The order given to the subsets is by reverse tuple order (last element most significant).
"""
function select_k_from_n(x::T, n::Integer, k::Integer) where T<:Integer
    # @assert 0 < x <= binomial(n, k) && 0 <= k <= n && 0 <= n
    if n <= 0 || k <= 0
        T[]
    elseif k == 1
        [x]
    elseif n == 1
        T[1]
    else
        t = binomial(T(n-1), T(k))
        if x <= t
            select_k_from_n(x, n - 1, k)
        else
            push!(select_k_from_n(x - t, n - 1, k - 1), n)
        end
    end
end

"""
    hypercube(x, n)

Return the `x`-th `n`-tuple of integers. Start with zero-tuple for `x` == 0.
The tuples `0:(2k+1)^n-1` are contained in n-dimensional hypercube `[-k:k]^n`.
Tuple number `(2k+1)^n-1` is always `-k*ones(n)`.
The implied order is no way canonical. 
"""
function hypercube(x::T, n::Integer, half::Val{P} = Val(false)) where {T<:Integer,P}
    if n <= 0 || x <= 0
        return zeros(T, n)
    end
    sides = ifelse(P, 1, 2)
    #=
    k = one(T)
    while k ^ n < x
        k += 2
    end
    k -= 2
    =#
    #@assert k == ((iroot(x - 1, n) + 1 ) ÷ 2) * 2 - 1 "$k == $(((iroot(x - 1, n) + 1 ) ÷ 2) * 2 - 1)"
    km = (iroot(x, n) + sides - 1) ÷ sides
    k = sides * (km - 1) + 1
    kn = k ^ n
    x -= kn
    mi = T(1)
    ei = T(1)
    ki = kn
    for i = 1:n
        mi *= sides # sides^i
        ei = ei * (n - i + 1) ÷ i # binomial(n, i)
        ki ÷= k # k ^ (n - i)
        t = mi * ei * ki
        if x < t
            m, e, x = linear2triple(x, mi, ei, ki)
            return selecttuple(x, e, m, n, km, i, half)
        else
            x -= t
        end
    end
    throw(ErrorException("should not be reachable"))
end
function linear2triple(x, aa, bb, cc)
    x, a = fldmod(x, aa)
    x, b = fldmod(x, bb)
    c = x
    @assert c < cc
    (a, b, c)
end
function selecttuple(x, e, m, n, km, i, half)
    # on a n - i dimensional edge (i ∈ 1:n)
    ne = select_k_from_n(e + 1, n, i) # i edge coordinate numbers
    p = perm(n, ne) # permutation of the coordinate numbers - edge coordinates first
    q = hypercube(x, n-i, half) # values for n-i inner coordinates
    r = similar(q, n)
    for j = 1:i
        r[p[j]] = bincoord(m, j-1) * km
    end
    for j = i+1:n
        r[p[j]] = q[j-i]
    end
    r
end 

function perm(n::Integer, ne::AbstractVector{<:Integer})
    @assert all(0 .< ne .<= n)
    p = copyto!(similar(ne, n), 1:n)
    q = copy(p)
    for i = 1:length(ne)
        nei = ne[i]
        b = p[i]
        a = q[nei]
        p[i], p[a] = p[a], b
        q[nei] = i
        q[b] = a  
    end
    p
end

function bincoord(x::Integer, k::Integer)
    ifelse(iseven(x >> k), 1, -1)
end

"""
    iroot(a::Integer, n::Integer)

Integer root: the largest integer `m` such that `m^n <= a`.
"""
function iroot(s::Integer, n::Integer)
    iszero(s) && return s
	x0 = oftype(s, ceil(s ^ (1/(n))))
    up(x) = ( s ÷ x ^ (n - 1) + x * (n - 1) ) ÷ n
    x0 = up(x0)
    x1 = up(x0)
	while x1 < x0
	    x0 = x1
		x1 = up(x0)
    end
    x0
end
 
""" 
    ilog2(a::Integer)::Int 
 
For nonzero integers `a` return Int(floor(log2(abs(a)))) exact arithmethic.
For zero return `-1` 
""" 
function ilog2(a::Integer) 
    ndigits(a, base=2, pad=0) - 1 
end
function ilog2(a::Base.BitInteger) 
    bpl = sizeof(a) * 8 
    bpl - 1 - leading_zeros(abs(a)) 
end 

#=
Assuming there is a zero-based enumeration of all elements of degree `d`
for all degrees `>= 0`,
provide an enumeration of elements of any degree.
:w
The elements may be thought positioned in a sequence of rows of increasing length.
All elements of degree `d` are in position `d` of a row.
The enumeration is by travelling one row after the other.

The row lengths are set to `ilog2(r+1) + 1`. This way higher degree elements are
pushed back in the enumeration.
=#
"""
    index2indexdegree(x) -> (dx, degree)

Return the degree-relative index and the degree of the element
at position `x`.
"""
function index2indexdegree(x::Integer)
    n = index2row(x)
    d = x - row2index(n)
    n - degree2row(d), d
end

"""
    indexdegree2index(dx, d) -> index

Return the index of the element , which is identified by
its degree-relative index and its degree.
"""
function indexdegree2index(x::Integer, d::Integer)
    row2index(degree2row(d) + x) + d
end

"""
    row2index(r)

For row id `r` return index of degree `0` element of that row.
Rows are zero-based.
"""
function row2index(r)
    xl = row2degree(r) + 1
    xl * widen(r) + xl - one(widen(r))<<xl + 1
end

"""
    index2row(x)

For the zero based index `x` return the row id, in which the
element number `x` is located.
"""
function index2row(y)
    function _index2row(x, y0, y1)
        xl = row2degree(x)
        d, r = fldmod(y0 + one(x)<<(xl-1), xl + 1)
        (r<<2 + y1 + xl) ÷ (xl + one(x)) + d<<2 - 2one(x)
    end
    iszero(y) && return y
    y0, y1 = fldmod(y, 1<<2)
    x0 = y
    x1 = _index2row(x0, y0, y1)
    while x0 > x1
        x0 = x1
        x1 = _index2row(x0, y0, y1)
    end
    x0
end

"""
    degree2index(d)

For degree `d` return the index of the first element
of that degree.
"""
function degree2index(n)
    big(2)^n  * (n - 1) + n + 1
end

"""
    row2degree(r)

Return the maximal degree of elements in row number `r`.
This is the fundamantal definition of the shape of the table.
"""
function row2degree(r)
    r <= 0 && return zero(r) 
    ilog2((r - 1) >> 1 + 1) + 1
end

"""
    degree2row(d)

For degree `d` return the row of the first element
of that degree.
Inverse of `row2degree`.
"""
function degree2row(n)
    big(2)^n - 1
end
