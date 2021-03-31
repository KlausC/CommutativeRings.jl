
function factor_must_try_all_factors_of_e(p::P) where P<:UnivariatePolynomial{<:ZZ}
    q, e = tominexp(p)
    res = factor_minexp(q)
    if e == 1
        res
    else
        x = monom(P)
        [first(res[i])(x^e) => last(res[i]) for i = 1:length(res)]
    end
end

function factor(p::P) where P<:UnivariatePolynomial{<:ZZ}
    X = varname(P)
    Z = ZZ{BigInt}[X]
    u = convert(Z, p)
    x = monom(Z)
    e = 0
    while deg(p) >= 0 && iszero(p[0])
        e += 1
        p = p / x
    end
    c = content(p)
    q = primpart(p)
    res = Pair{Z,Int}[]
    isone(c) || push!(res, Z(c) => 1)
    iszero(e) || push!(res, x => e)
    if deg(q) > 0
        r = yun(q)
        for (e, u) in enumerate(r)
            if !isone(u)
                s = zassenhaus(u)
                append!(res, first.(s) .=> e)
            end
        end
    end
    res
end

"""
    yun(u::UnivariatePolynomial)::Vector

Split integer polynomial `p` into coprime factors `u_i for i = 1:e`
such that `p = u_1^1 * u_2^2 * ... * u_e^e`.  
"""
function yun(u::UnivariatePolynomial{<:ZZ})
    t, v, w = GCD(u, derive(u))
    res = typeof(u)[]
    if isone(t)
        push!(res, u)
    else
        while ( wv = w - derive(v) )  |> !iszero
            u, v, w = GCD(v, wv)
            push!(res, u)
        end
        push!(res, v)
    end
    res
end

"""
    GCD(u::P, v::P) where P<:UnivariatePolynomial

Calculate `g = gcd(u, v) and 
return `gcd(u, v), u / g, v / g`.
"""
function GCD(u, v)
    t = pgcd(u, v)
    isone(t) ? (t, u, v) : (t, u/t, v/t)
end

function zassenhaus_unused_tomonic_etc(u)
    un = LC(u)
    v = tomonic(u)
    vv = zassenhaus_monic(v)
    if isone(un)
        vv
    else
        primpart.(frommonic.(vv, un))
    end
end

function zassenhaus(u)
    p = prevprime(typemax(UInt8))
    fac = []
    while isempty(fac)
        fac = factormod(u, p)
        p = prevprime(p, 2)
    end
    res = []
    for i = 1:length(fac)
        u, vv = fac[i]
        append!(res, checked_irreducible(u, p, vv))
    end
    res
end

function checked_irreducible(u, p, vv)
    n2 = deg(u) ÷ 2
    B = maximum(coeffbounds(u, n2))
    if length(vv) > 1 && 2 * B > p
        @warn "irreducibility of $u cannot be proved - p = $p"
    end
    [(u, vv)]
end

"""
    factormod(u, p::Integer)

Given integer polynomial `u` and `p`, which is a power of a prime number and coprime to `LC(u)`,
factorize `u modulo p`.
Return vector of integer polynomial factors of `u` and `u / product(factors)`.
If their degree sums up to the degree of `u`, the factorization was successfull.
If not, the returned factors are not complete, and the procedure has to be repeated with increased `p`.
If the vector is empty, `p` was one of those rare "unlucky" primes, which are not useful for this polynomial.  
"""
function factormod(u::P, p::Integer) where P<:UnivariatePolynomial{<:ZZ}
    fl = leftfactor(u)
    fr = rightfactor(u)
    u = rightop!(leftop!(copy(u), ÷, fl), ÷, fr)
    res = factormod0(u, p)
    for (u, vv) in res
        rightop!(leftop!(u, *, fl), *, fr)
    end
    res
end
function factormod0(u::P, p::Integer) where P<:UnivariatePolynomial{<:ZZ}
    X = varname(u)
    Zp = (ZZ/p)
    Z = ZZ{BigInt}[X]
    res = Pair{Z, Any}[]
    u = convert(Z, u)
    un = LC(u)
    isunit(gcd(p, un)) || return res
    unp = Zp(un)
    up = Zp[X](u) / unp
    uu = u * un

    fac = factor(up) # modulo p
    vv = first.(fac)
    maximum(last.(fac)) <= 1 || return res
    r0 = 0
    levels = zeros(Int, 2)
    while (r = length(vv)) > 0 && r != r0
        n = deg(uu)
        tr = max((one(p))<<(r-1) - 1, 1)
        for i = 1:tr
            d = enumx(i, r)
            nv = deg_prod(vv, d)
            if 2*nv > n || ( 2*nv == n && (d & 1 == 1) )
                # println("before d = $(bitstring(d)) nv = $nv n = $n r = $r")
                d = (1 << r - 1) & ~d
                nv = n - nv
                # println("after  d = $(bitstring(d)) nv = $nv n = $n r = $r")
            end
            if dividecheck(uu, unp, vv, d)
                v = Z(pprod(vv, d) * unp)
                qd, rd = divrem(uu, v)
                if iszero(rd)
                    co = content(v)
                    v = v / co
                    !isone(v) && push!(res, v => subset(vv, d))
                    unc = un / co
                    un = LC(qd) / unc
                    unp = Zp(un)
                    # println("($qd) * $un / $unc")
                    uu = qd * un / unc
                    remove_subset!(vv, d)
                    levels .= 0
                    # println("reset levels: n = $n nv = $nv")
                    break
                end
            end
            if nv > levels[1]
                levels[1] = nv
                B = maximum(coeffbounds(uu, nv))
                if B * 2 >= p
                    # println("log2(B) = $(log2(B)) n = $n nv = $nv")
                    levels[2] = nv
                end
            end
        end
        r0 = r
    end
    uu = uu / un
    !isone(uu) && push!(res, uu => subset(vv, -1))
    res
end

function dividecheck(u::P, unp, vv, d) where {T,P<:UnivariatePolynomial{T}}
    S = basetype(T)
    l0 = S(l0prod(vv, d) * unp)
    u0 = value(u[0])
    !iszero(l0) && iszero(rem(u0, l0))
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
    hensel_lift(u, v, a) -> V

Algorithm see TAoCP 2.Ed 4.6.2 Exercise 22.
Assumptions fo the input

u = prod(v) mod q
sum( a .* prod(v) ./ v) = 1 mod p
In the case of u is not monic, the factor lc(u) has to be multiplied into v[1]. lc(v[1]) = lc(u) mod p and lc(v[i]) = 1 for i > 1.

The output vector V contains polynomials of same degree as corresponding v.
"""
function hensel_lift(u::P, v::AbstractVector{Pq}, a::AbstractVector{Pp}) where {P<:Polynomial,Pq<:Polynomial,Pp<:Polynomial}
    X = varname(Pq)
    Zp = basetype(Pp)
    Zq = basetype(Pq)
    p = modulus(Zp)
    q = modulus(Zq)
    Zqp = ZZ/(widen(q)*widen(p))
    Pqp = Zqp[X]
    V = liftmod.(Pqp, v)
    V[1].coeff[end] = value(LC(u))
    f = liftmod(Pqp, u) - prod(V)
    fp = map(x -> Zp(value(x) ÷ q), f)
    fi = rem.(a .* fp, v)
    V .+= liftmod.(Pqp, fi) * q
    V, f, fp, fi
end




function hensel_lift(u::P, v::P1, w::P1, a::P1, b::P1, p::Integer, q::Integer, r::Integer, c::Integer) where {P<:Polynomial,P1<:Polynomial}
#= The following assumptions are made, but not verified here:
    r = gcd(p, q), p and q need not be prime!
    u == v * w (modulo q)
    a * v + b * w == 1 (modulo p) with deg(a) < deg(w) and deg(b) < deg(v)
    c * LC(v) == 1 (modulo r)
    deg(u) == deg(v) + deg(w)

    The algorithm constructs polynomials V == v (modulo q) and W == w (modulo q)
    such that u == V * W ( modulo q*r) and
    LC(V) == LC(v) and LC(W) == lc(w) and deg(V) == deg(v) and deg(W) == deg(w)

    If r is prime, the results are unique modulo q*r.
=#
    X = varname(P)
    Pqr = (ZZ/(q*r))[X]
    Pr = (ZZ/r)[X]
    u, v, w, a, b = convert.(Pqr, (u, v, w, a, b))
    f = convertmod(Pqr, u - v * w, ÷, q)
    t, vv = divrem(f * b, v)
    V = convertmod(Pqr, vv, %, r)
    W = convertmod(Pqr, f * a + t * w, %, r)
    V * q + v, W * q + w
end

function liftmod(::Type{Z}, a::ZZmod) where {X,T,Z<:ZZ{T}}
    Z(signed(T)(value(a)))
end
function liftmod(::Type{Z}, a::ZZ) where {X,T,Z<:ZZmod{X,T}}
Z(signed(T)(value(a)))
end
function liftmod(::Type{Z}, a::ZZmod) where {X,T,Z<:ZZmod{X,T}}
    Z(signed(T)(a))
end
function liftmod(::Type{P}, a::Polynomial) where {Z, P<:Polynomial{Z}}
    c = liftmod.(Z, a.coeff)
    P(c)
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
    map(f, p::Polynomial)

Apply `f` to all coefficients of `p` and form new polynomial.
The dgree is adapted.    
"""
function Base.map(f, p::P) where {X,T,P<:UnivariatePolynomial{T,X}}
    c = map(f, p.coeff)
    UnivariatePolynomial{eltype(c),X}(c)
end

"""
    pprod(v::Vector, n::{Integer,BitVector})

Product of elements of `v`, with corresponding bit in `n` is set.
(lsb corresponds to index 1).
"""
pprod(vv, n) = preduce(*, oneunit(eltype(vv)), vv, n)

"""
    deg_prod(v, d)

Calculate and return `deg(pprod(v, n))` efficiently.
"""
deg_prod(vv, d) = preduce((p, v) -> p + deg(v), 0, vv, d)

"""
    l0prod(v, n)

Return `pprod(v, n)[0]` efficiently.
"""
function l0prod(vv, n)
    start = oneunit(basetype(eltype(vv)))
    preduce((p, v) -> p * v[0], start, vv, n)
end

"""
    l1prod(v, n)

Return `pprod(v, n)[0:1]` efficiently.
"""
function l1prod(vv, n)
    T = basetype(eltype(vv))
    start = (oneunit(T), zero(T))
    preduce((p, v) -> (p[1]*v[0], p[2] * v[0] + p[1] * v[1]), start, vv, n)
end

function preduce(op, start, vv::AbstractVector, n::Integer)
    r = length(vv)
    j = iszero(n) ? r : trailing_zeros(n)
    p = start
    j >= r && return p
    n >>= j
    j += 1
    p = op(p, vv[j])
    while j < r
        j += 1
        n >>= 1
        if isodd(n)
            p = op(p, vv[j])
        end
    end
    p
end
function preduce(op, start, vv::AbstractVector, n::BitVector)
    p = start
    for j = 1:length(vv)
        if n[j]
            p = op(p, vv[j])
        end
    end
    p
end

function subset(vv::AbstractVector, d)
    vv[preduce(push!, Int[], 1:length(vv), d)]
end

function remove_subset!(vv::AbstractVector, d)
    deleteat!(vv, preduce(push!, Int[], 1:length(vv), d))
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
    n = sum(s) ÷ 2 + 1
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
        ps = fill(UInt64[], n)
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

# to be moved to test, once productive implementation is stable - used to verify results
function enumx_slow(n::Integer, bits::Int)
    nm = (oftype(n, 1)<<bits) - 1
    nm >= n >= 0 || throw(ArgumentError("n is not in range [0, 2^$bits - 1]"))
    bits == 0 && return zero(n)
    if n >> (bits - 1) == 1
        return nm - enumx(nm - n, bits)
    end
    s = zero(n)
    d = s
    for k = 0:bits
        t = s + binomial(bits, k)
        mm = binomial(bits - 1, k-1)
        if n < t || t <= 0
            m = n - s
            return (enumx(m + d, bits - 1) << 1) + (m < mm)
        end
        s = t
        d += mm
    end
    s
end

"""
    enumx(n::Integer, bits)::Integer

For each `bits >= 0, n -> enumx(n, bits)` is a bijection of `0:2^bits-1`
in a way that `enumx.(0:2^bits-1, bits)` is sorted by number of ones
in two's complement representation. 
"""
function enumx(n::Integer, bits::Int)
    mask = (oftype(n, 1)<<bits) - 1
    nm = mask
    nm >= n >= 0 || throw(ArgumentError("n is not in range [0, 2^$bits - 1]"))
    a = zero(n)
    b = one(n)
    while bits > 0
        if n > nm - n
            n = nm - n
            a = a ⊻ (~(b - 1) & mask)
        end
        u0 = v0 = w0 = one(n)
        u1 = v1 = w1 = d = zero(n)
        for k = 0:bits
            if n < w0 || w0 <= 0
                if n - w1 < u1
                    a ⊻= b
                end
                break
            end
            d += u1
            u1, u0 = u0, u0 * (bits-k-1) ÷ (k+1)
            v1, v0 = v0, u0 + v0
            w1, w0 = w0, v0 + v1
        end
        n += d - w1
        bits -= 1
        b <<= 1
        nm >>= 1
    end
    a
end

# From here experimental to simplify cases with: 1. p(x) = q(x^e) 2. p(x) = q(f*x)

function tomonic(u::P) where P<:UnivariatePolynomial
    un = LC(u)
    isone(un) && return u
    c = copy(u.coeff)
    n = deg(u)
    c[n+1] = one(un)
    s = un
    for i = n-1:-1:1
        c[i] *= s
        s *= un
    end
    P(c)
end

function frommonic(u::P, un) where P<:UnivariatePolynomial
    isone(un) && return u
    c = copy(u.coeff)
    n = deg(u)
    s = un
    for i = 2:n+1
        c[i] *= s
        s *= un
    end
    P(c)
end

function common_exp(u::UnivariatePolynomial)
    gcd(filter(i -> !iszero(u[i]), 0:deg(u)))
end

function tominexp(u::P) where P<:UnivariatePolynomial
    e = common_exp(u)
    e == 1 && return u, e
    n = deg(u) ÷ e
    c = [u[i*e] for i = 0:n]
    P(c), e
end

# x -> k * x
function leftop!(u::UnivariatePolynomial, op, v)
    c = u.coeff
    p = eltype(c)(v)
    for i = 2:length(c)
        c[i] = op(c[i], p)
        p *= v
    end
    u
end
function rightop!(u::UnivariatePolynomial, op, v)
    c = u.coeff
    p = eltype(c)(v)
    for i = length(c)-1:-1:1
        c[i] = op(c[i], p)
        p *= v
    end
    u
end

"""
    leftfactor(u)

Find greatest integer `g` such that `g^k` divides `u[k]` for all `k = 1:deg(u)`
"""
leftfactor(u) = polyfactor(u, true)

"""
    rightfactor(u)

Find greatest integer `g` such that `g^k` divides `u[deg(u)-k]` for all `k = 1:deg(u)`
"""
rightfactor(u) = polyfactor(u, false)

function polyfactor(u::UnivariatePolynomial{ZZ{T}}, left::Bool) where T<:Integer
    c = u.coeff
    n = deg(u)
    g = Vector{T}(undef, n)
    gk = zero(T)
    cc(k) = left ? c[k+1] : c[n - k + 1]

    for k = n:-1:1
        gk = gcd(gk, value(cc(k)))
        g[k] = gk
        isone(gk) && return gk
    end
    for a in factors(gk)
        a = gk ÷ a
        b = a
        isone(b) && break
        ok = true
        for k = 2:n
            b *= a
            if !iszero(rem(g[k], b))
                ok = false
                break
            end
        end
        ok && return a
    end
    one(gk)
end

"""
    allgcdx(v)

Given vector `v` of mutual coprime elements.
Calculate vector `a` with  `sum(div.(a .* prod(v), v)) == 1 and abs.(a) .< abs.(v)`.
If element type is polynomial, read `abs` as `degree`. 
"""
function allgcdx(v::AbstractVector{T}) where T
    b = one(T)
    p = prod(v)
    n = length(v)
    w = Vector{T}(undef, n)
    for k = 1:n
        vk = v[k]
        p = div(p, vk)
        g, a, c = gcdx(p, vk)
        isone(g) || throw(ArgumentError("factors must be coprime"))
        a *= b
        c *= b
        t, w[k] = divrem(a, vk)
        b = c + t * p
    end
    w
end
