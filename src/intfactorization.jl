
function factor(p::P) where P<:UnivariatePolynomial{<:ZZ}
    c = content(p)
    q = primpart(p)
    r = yun(q)
    s = zassenhaus(r)
    isone(c) ? s : [P(c) => 1; s]
end

function yun(p)
    p
end

function zassenhaus(p)
    [p => 1]
end

"""
    coeffbounds(u::Polygon, m)::Vector{<:Integer}

Assuming `u` is a univariate polygon with integer coefficients and `LC(u) != 0 != u(0)`.
If `u` has a integer factor polynom `v` with `deg(v) == m`,
calculate array of bounds `b` with `abs(v[i]) <= b[i+1] for i = 0:m`.
Algorithm see TAoCP 2.Ed 4.6.2 Exercise 20.
"""
function coeffbounds(u::UnivariatePolynomial{ZZ{T},X}, m::Integer) where {T<:Integer,X}
    I = widen(T)
    n = deg(u)
    0 <= m <= n || throw(ArgumentError("required m ∈ [0,deg(u)] but $m ∉ [0,$n]"))
    accuracy = 100
    un = abs(value(LC(u)))
    u0 = abs(value(u[0]))
    iszero(u0) && throw(ArgumentError("required u(0) != 0"))
    rua = norm(value.(u.coeff)) * accuracy
    ua = Integer(ceil(rua))
    v = zeros(I, m+1)
    if m > 0
        v[m+1], v[1] = un, u0
    else
        v[1] = min(u0, un) # abs(content(u)) would be possible but not worth the effort
    end
    u0 *= accuracy
    un *= accuracy
    bk = I(1)
    for j = m-1:-1:1
        bj = bk
        bk = bk * j ÷ (m - j)
        v[j+1] = min(bj * ua + bk * un, bk * ua + bj * u0) ÷ accuracy
    end
    v
end

"""
    hensel_lift()

Algorithm see TAoCP 2.Ed 4.6.2 Exercise 22.
"""
function hensel_lift(u::P, v::P1, w::P1, a::P1, b::P1, p::Integer, q::Integer, r::Integer, c::Integer) where {P<:Polynomial,P1<:Polynomial}
#= The following assumptions are made, but not verified here:
    r = gcd(p, q) - p and q need not be prime!
    u == v * w (modulo q)
    a * v + b * w == 1 (modulo p) with deg(a) < deg(w) and deg(b) < deg(v)
    c * LC(v) == 1 (modulo r)
    deg(u) == deg(v) + deg(w)

    The algorithm constructs polynomials V == v (modulo q) and W == w (modulo q)
    such that u == V * W ( modulo q*r) and
    LC(V) == LC(v) and LC(W) == lc(w) and deg(V) == deg(v) and deg(W) == deg(w)

    If r is prime, the results are unique modulo q*r.
=#
    X = varnames(P)[1]
    Pqr = (ZZ/(q*r))[X]
    Pr = (ZZ/r)[X]
    u, v, w, a, b = convert.(Pqr, (u, v, w, a, b))
    f = convertmod(Pqr, u - v * w, ÷, q)
    t, vv = divrem(f * b, v)
    V = convertmod(Pqr, vv, %, r)
    W = convertmod(Pqr, f * a + t * w, %, r)
    V * q + v, W * q + w
end

"""
    hensel_start(u, ZZ-type, p)

Given an integer polynomial `u`, and a prime number `p`, find the factorization of
`u` modulo `p`.
Give a hint, if this is not square-free. 
"""
function hensel_start(u::UnivariatePolynomial, p::Integer)
    Pp = (ZZ/p)[varname(u)]
    up = convert(Pp, u)
    fac = factor(up)
    square_free = maximum(last.(fac)) == 1
    square_free, first.(fac)
end

function hensel_lift(u::P, vv, mask::Integer, p::Integer, q::Integer, r::Integer) where P<:UnivariatePolynomial{<:ZZ{<:Integer}}
    # Assume u is a primitive, square-free polynomial over integers.
    # For given prime number `p` find a factorization of `u` modulo `p`.
    # For all combinations of factors `v`
    #    calculate coefficient bounds `B` for the degree of `v`.
    #    lift `v` to `V` in a way that `V` is a factor of `u` modulo `p^e > B`
    #    adjust coeffients of `V` to be in `-p^e/2:p^e/2`.
    #    check if `v` divides `u` over the integers.
    #    
    X = varname(u)
    Pq = (ZZ/q)[X]
    vv = factor(Pq(u))
    for (n, v, w) in smallfactors(vv, u, mask)
        d = deg(v)
        B = maximum(coeffbounds(u, d))
        pe = p
        while pe < B
            g, a, b = gcdx(v, w)
            pe, v, w, a, b, c = hensel_lift(u, v, w, a, b, c)
        end
        vp = P(v)
        if divides_maybe(vp, u)
            u, r = divrem(u, vp)
            if iszero(r)
                return n, vp, u
            end
        end
    end
    return 0, one(P), u
end

function convertmod(::Type{P}, u::UnivariatePolynomial, op, q::Integer) where P<:UnivariatePolynomial
    P(op.(value.(u.coeff), q))
end

function convertmod(::Type{P}, u::Q) where {P,Q}
    m = modulus(basetype(P))
    n = modulus(basetype(Q))
    convertmod(P, u, %, div(n, m))
end

"""
    prod(v::Vector, n::{Integer,BitVector})

Product of elements of `v`, with corresponding bit in `n` is set.
(lsb corresponds to index 1).
"""
function pprod(vv::AbstractVector, n::Integer)
    r = length(vv)
    j = iszero(n) ? r : trailing_zeros(n)
    j >= r && return oneunit(eltype(vv))
    n >>= j
    j += 1
    p = vv[j]
    while j < r
        j += 1
        n >>= 1
        if isodd(n)
            p *= vv[j]
        end
    end
    p
end
function pprod(vv::AbstractVector, n::BitVector)
    p = oneunit(eltype(vv))
    for j = 1:length(vv)
        if n[j]
            p *= vv[j]
        end
    end
    p
end

function deg_prod(vv::AbstractVector, n::Integer)
    r = length(vv)
    j = trailing_zeros(n)
    n >>= j
    p = 0
    while j < r
        j += 1
        if isodd(n)
            p += deg(vv[j])
        end
        n >>= 1
    end
    p
end   

"""
    smallfactors(vv::Vector{Polynomial{ZZ/p}}, u::Polynomial{ZZ{Integer}})::w

Assuming `vv` is an array of `r` factors of integer polynomial `u` modulo `p`,
return an iterator over products of factors from `vv`.
The iterator elements are tuples `(n, w)`, where n is an integer in `0:2^r-1` and `w = pprod(vv, n)`.
The elements `w` have the property
`deg(w) < deg(u)/2` or `deg(w) == deg(u)/2 && ( count_ones(n) < r/2 || count_ones(n) == r/2 && isodd(n) )`.
"""
function smallfactors(vv, u::P, mask = typemax(Int)) where P<:UnivariatePolynomial{<:ZZ{<:Integer}}
    r = length(vv)
    mask &= (1<<r - 1)
    rm = count_ones(mask)
    up = eltype(vv)(u)
    smaller(n, v, w) = deg(v) <= deg(w) ? (n, v, w) : (mask & ~n, w, v)
    sm1 = Iterators.filter(x -> x & mask == x && (2count_ones(x) < rm || 2count_ones(x) == rm && isodd(x)), 1:2^r-1)
    sm2 = Iterators.map(n -> smaller(n, pprod(vv, n), pprod(vv, mask & ~n)), sm1)
    sm2
    # Iterators.filter(x -> divides_maybe(P(x[2]), u), sm3)
end

"""
    divides_maybe(v, u)

Check the two least significant coefficients of `v` and `u`.
Return `false` if polynomial `v` does definitely not divide `u`.
If return value is `true`, `v` possibly does.
"""
function divides_maybe(v::UnivariatePolynomial, u::UnivariatePolynomial)
    n = deg(u)
    m = deg(v)
    m > n && return false
    v0 = v[0]
    iszero(v0) && return false
    isone(abs(v0)) && return true
    u0 = u[0]
    q0, r0 = divrem(u0, v0)
    iszero(r0) || return false
    m < 1 && return true
    if basetype(v0) <: Integer
        Z = ZZ/abs(value(v0))
        Z(u[1]) == Z(q0) * Z(v[1])
    else
        r0 = u[1] - q0 * v[1]
        iszero(rem(r0, v0))
    end
end

function partsums(s::Vector{<:Integer})
    m = length(s)
    n = sum(s) + 1
    if n > 64
        a = falses(n)
        a[1] = true
    else
        a = UInt64(1)
    end
    pa = partsums!(a, s)
    pv = zeros(Int, n)
    pv[1] = 1
    pv = partsums!(pv, s)
    if m > 64
        ps = fill(BitVector[], n)
        ps[1] = [falses(m)]
    else
        ps = fill(UInt64[], m)
        ps[1] = [0]
    end
    ps = partsums!(ps, s)
    pa, pv, ps
end

function partsums!(a::BitVector, s::Vector)
    for d in s
        map!(|, a, a, a >> d)
    end
    a
end
function partsums!(a::Integer, s::Vector)
    for d in s
        a |= a << d
    end
    a
end

function partsums!(a::Vector{<:Integer}, s::Vector)
    n = length(a)
    for d in s
        for k = n-d:-1:1
            ak = a[k]
            if ak > 0
                a[k+d] += ak
            end
        end
    end
    a
end

function partsums!(a::Vector{<:Vector{BitVector}}, s::Vector)
    n = length(a)
    for (i, d) in enumerate(s)
        for k = n-d:-1:1
            ak = a[k]
            if length(ak) > 0
                bk = map(copy, ak)
                for x in bk
                    x[i] = true
                end
                if length(a[k+d]) > 0
                    append!(a[k+d], bk)
                else
                    a[k+d] = bk
                end
            end
        end
    end
    a
end
function partsums!(a::Vector{<:Vector{<:Integer}}, s::Vector)
    n = length(a)
    for (i, d) in enumerate(s)
        for k = n-d:-1:1
            ak = a[k]
            if length(ak) > 0
                bk = copy(ak)
                bk .|= 1 << (i - 1)
                if length(a[k+d]) > 0
                    append!(a[k+d], bk)
                else
                    a[k+d] = bk
                end
            end
        end
    end
    a
end
