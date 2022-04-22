
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

function isirreducible(p::P; p0=3) where P<:UnivariatePolynomial{<:ZZ}
    deg(p) > 1 || return true
    iszero(p[0]) && return false
    X = varname(P)
    Z = ZZ{BigInt}[X]
    q = convert(Z, p)
    isone(pgcd(q, derive(q))) || return false
    zassenhaus_irr(q; p0)
end

function factor(p::P; p0=3) where P<:UnivariatePolynomial{<:ZZ}
    X = varname(P)
    c = content(p)
    Z = ZZ{BigInt}[X]
    q = Z(isone(c) ? copy(p) : p / c)
    x = monom(Z)
    q, e = stripzeros!(q)
    res = Pair{Z,Int}[]
    isone(c) || push!(res, Z(c) => 1)
    iszero(e) || push!(res, x => e)
    if deg(q) > 0
        r = yun(q)
        for (e, u) in enumerate(r)
            if !isone(u)
                s = zassenhaus(u; p0)
                append!(res, s .=> e)
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
        wv = w - derive(v) 
        while !iszero(wv)
            u, v, w = GCD(v, wv)
            push!(res, u)
            wv = w - derive(v)
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

function zassenhaus(u; p0)
    zassenhaus2(u, Val(false); p0)
end

function zassenhaus2(u::UnivariatePolynomial{<:ZZ{<:Integer}}, val::Val{BO}; p0) where BO
    Z = ZZ{BigInt}[varname(u)]
    u = convert(Z, u)
    zassenhaus2(u, val; p0)
end

# D = []

function zassenhaus2(u::UnivariatePolynomial{ZZ{BigInt}}, ::Val{BO}; p0) where BO
    v, p = best_prime(u, p0)
    a = allgcdx(v)
    #println(" initial v/$p = "); display([v a])
    #empty!(D)
    #push!(D, u)
    #push!(D, deepcopy(v))
    #push!(D, deepcopy(a))
    fac = combinefactors(u, v, a)
    printfac(fac)
    #push!(D, "combinefactors called")
    #push!(D, deepcopy(fac))
    res = typeof(u)[]
    q = p
    while !all_factors_irreducible!(res, fac, q)
        #push!(D, "all_factors_irreducible! called")
        #push!(D, deepcopy(fac))
        if BO && length(res) >= 1 && deg(res[1]) < deg(u)
            break
        end
        for i = 1:length(fac)
            fac, q = lift!(fac, i)
            
            printfac(fac)
            #push!(D, "lifted $i")
            #push!(D, deepcopy(fac))
        end
    end
    res
end

"""
    zassenhaus_irr(u)

Returns true iff the squarefree polynomial `u` is irreducible.
"""
function zassenhaus_irr(u; p0=3)
    res = zassenhaus2(u, Val(true); p0)
    isempty(res) || deg(res[1]) >= deg(u)
end

# find small prime number >= p0 for which number of 
# factors modulo p is smallest
function best_prime(u, p0=3, kmax=10, vmin=1, vmax=15)

    kbreak(vl) = min(vl <= vmin ? 0 : vl > vmax ? vmax : vl, kmax)

    un = LC(u)
    v, p = factormod(u, p0)
    q = p
    k = 0
    vl = length(v)
    println("find p = $p length(v) = $vl $(deg.(v))")
    while k < kbreak(vl)
        w, q = factormod(u, q)
        wl = length(w)
        println("find p = $q length(v) = $wl $(deg.(w))")
        if wl < vl
            vl = wl
            v = w
            p = q
        end
        k += 1
    end
    v, p
end

# find next prime number > p, for which factorization of u mod p
# is has degree of u and is square free
function factormod(u, p::Integer)
    X = varname(u)
    un = LC(u)
    v = []
    while isempty(v)
        p = nextprime(p + 1)
        compatible_with(p, un) || continue
        Zp = ZZ/p
        unp = Zp(un)
        up = Zp[X](u) / unp
        fac = factor(up) # modulo p
        maximum(last.(fac)) <= 1 || continue
        v = first.(fac)
    end
    v, p
end

"""
    factor(u::UnivariatePolynomial, a::Integer)

factorize `u(x^a)`. `u` squarefree and `content(u) == 1`
"""
function factor(u::P, a::Integer) where P<:UnivariatePolynomial
    #println("factor1($u, $a)")
    res = Pair{P,Int}[]
    x = monom(P)
    for ab in sort(collect(factors(a)))
        r = factor(u(x^ab))
        ab == a && return r
        if length(r) > 1        
            for (v, e) ∈ r
                b = a ÷ ab
                s = factor(v, b)
                for (p, x) in s
                    push!(res, p => x * e)
                end
            end
            break
        end
    end
    res
end

# check if p is coprime with leading coefficient
function compatible_with(p::Integer, u::ZZ)
    u = abs(value(u))
    gcd(p, u) == 1
end

"""
    all_factors_irreducible!(res, fac, p)

Move factors, that are proved irreducible, from `fac` to `res`.
Factors ar proved irreducible with respect to integer `p`, if either
they cannot be reduced modulo `p`, or the absolute values of the coefficients
are less than `p / 2`. `B` is an upper bound on the coefficients.
Return `true` iff `fac` becomes empty.
"""
function all_factors_irreducible!(res, fac, p)
    del = Int[]
    for i = 1:length(fac)
        u, vv = fac[i]
        n2 = deg(u) ÷ 2
        domessage = n2 >= 50
        B = maximum(coeffbounds(u, n2))
        if length(vv) > 1 && 2 * B > p
            domessage && @warn "irreducibility of $u cannot be proved - p = $p B = $B"
        else
            domessage && @info "irreducibility of $u proved - p = $p B = $B"
            push!(del, i)
            push!(res, u)
        end
    end
    deleteat!(fac, del)
    isempty(fac)
end

"""
    lift!(fac, i)

Replace `(u, v, a) = fac[i]` with a list of lifted `(U, V, A)`.
This list `fac` contains one entry for each factor of `u`, which could be found, but none of the U needs to be irreducible.
"""
function lift!(fac, i)
    u, v, a = fac[i]

    bs = bezout_sum(v, a)
    @assert bs == 1
    # @assert a == allgcdx(v)
    V, A, p = hensel_lift(u, v, a)
    fac2 = combinefactors(u, V, A)
    splice!(fac, i, fac2)
    fac, p
end

"""
    factormod(u::Polynomial[; p0])

The procedure may be repeated with increased `p`.
If the vector is empty, `p` was one of those rare "unlucky" primes, which are not useful for this polynomial.
""" 
function factormod(u::P; p0=3) where P<:UnivariatePolynomial{<:ZZ}
    fl = leftfactor(u)
    fr = rightfactor(u)
    u = rightop!(leftop!(copy(u), ÷, fl), ÷, fr)
    res = zassenhaus(u; p0)
    for (u, vv) in res
        rightop!(leftop!(u, *, fl), *, fr)
    end
    res
end

"""
    combinefactors(u, v::Vector{<:UnivariatePolynomial{ZZ/p}}, a::Vector{<:UnivariatePolynomial{ZZ/q}})

Given integer polynomial `u` and `v` a monic squarefree factorization of `u modulo p` (vector of polynomials over ZZ/p).  
Return vector of tuples containing integer polynomial factors `U`, `V` vector with corresponding factorization, and
`A` corresponding factors.
If degrees of `V` sums up to the degree of `U`, that indicates the factorization was successful.
It is also possible, that only one factor is found.
The factors are not proved to be irreducible.
"""
function combinefactors(u::Z, vv::AbstractVector{<:UnivariatePolynomial{Zp}}, aa::AbstractVector) where {Z<:UnivariatePolynomial{<:ZZ},Zp}
    res = Tuple{Z, Any, Any}[]
    un = LC(u)
    unp = Zp(un)
    uu = u * un

    r0 = 0
    while (r = length(vv)) > 0 && r != r0
        n = deg(uu)
        tr = max(UInt64(1)<<(r-1) - 1, 1)
        for i = 1:tr
            d = enumx(i, r)
            nv = deg_prod(vv, d)
            if 2*nv > n || ( 2*nv == n && (d & 1 == 1) )
                #println("before d = $(bitstring(d)) nv = $nv n = $n r = $r")
                d = (1 << r - 1) & ~d
                nv = n - nv
                #println("after  d = $(bitstring(d)) nv = $nv n = $n r = $r")
            end
            if dividecheck(uu, unp, vv, d)
                w = pprod(vv, d)
                v = Z(w * unp)
                # println("pprod = $v  inv = $(Z(pprod(vv, ~d) * unp))")
                qd, rd = divrem(uu, v)
                if iszero(rd)
                    co = content(v)
                    v = v / co
                    if !isone(v)
                        vs, as = subset_with_a(vv, d, aa)
                        ww = pprod(vv, ~d)
                        as .= rem.(as .* ww, vs)
                        push!(res, (v, vs, as))
                    end
                    unc = un / co
                    un = LC(qd) / unc
                    unp = Zp(un)
                    # println("($qd) * $un / $unc")
                    uu = qd * un / unc
                    remove_subset!(vv, d)
                    remove_subset!(aa, d)
                    aa .= rem.(aa .* w, vv)
                    #push!(D, "removed $v")
                    #push!(D, deepcopy(vv))
                    #push!(D, deepcopy(aa))
                    # println("reset levels: n = $n nv = $nv")
                    break # restart loop for new uu
                end
            end
        end
        r0 = r
    end
    uu = uu / un
    !isone(uu) && push!(res, (uu, subset_with_a(vv, -1, aa)...))
    res
end

function subset_with_a(v, d, a)
    vs = subset(v, d)
    as = isempty(a) ? allgcdx(vs) : subset(a, d)
    vs, as
end

function dividecheck(u::P, unp, vv, d) where {T,P<:UnivariatePolynomial{T}}
    S = basetype(T)
    l0 = S(l0prod(vv, d) * unp)
    u0 = value(u[0])
    !iszero(l0) && iszero(rem(u0, l0))
end

"""
    coeffbounds(u::Polygon, m)::Vector{<:Integer}

Assuming `u` is a univariate polynomial with integer coefficients and `LC(u) != 0 != u(0)`.
If `u` has an integer factor polynom `v` with `deg(v) == m`,
calculate array of bounds `b` with `abs(v[i]) <= b[i+1] for i = 0:m`.
Algorithm see TAoCP 2.Ed 4.6.2 Exercise 20.
"""
function coeffbounds(u::UnivariatePolynomial{ZZ{T},X}, m::Integer) where {T<:Integer,X}
    I = widen(T)
    n = deg(u)
    0 <= m <= n || throw(ArgumentError("required m ∈ [0,deg(u)] but $m ∉ [0,$n]"))
    accuracy = 100 # use fixed point decimal arithmetic with accuracy 0.01 for the norm
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

Algorithm see "D. Knuth - TAoCP 2.Ed 4.6.2 Exercise 22" and "E. Kaltofen - Factorization of Polynomials"

Assumptions fo the input
u = prod(v) mod q
sum( a .* prod(v) ./ v) = 1 mod p
In the case u is not monic, the factor lc(u) has to be multiplied into v[1]. lc(v[1]) = lc(u) mod p and lc(v[i]) = 1 for i > 1.

The output vector V contains polynomials of same degree as corresponding v.
"""
function hensel_lift(u::P, v::AbstractVector{Pq}, a::AbstractVector{Pp}) where {P<:Polynomial,Pq<:Polynomial,Pp<:Polynomial}
    X = varname(Pq)
    Zp = basetype(Pp)
    Zq = basetype(Pq)
    p = modulus(Zp)
    q = modulus(Zq)
    Zqp = ZZ/(widemul(q, p))
    qp = modulus(Zqp)
    Pqp = Zqp[X]
    lc = LC(u)
    lci = inv(Zq(lc))

    V = liftmod.(Pqp, v)
    f = liftmod(Pqp, u) - prod(V) * Pqp(lc)
    fp = downmod(Zp, f, p) * lci
    fi = rem.(a .* fp , v)
    V .+= liftmod.(Pqp, fi) * p

    A = liftmod.(Pqp, a)
    f = bezout_sum(V, A) - 1
    fp = downmod(Zp, f, q)
    fi = rem.(a .* fp, v)
    A .-= liftmod.(Pqp, fi) * q

    @assert bezout_sum(V, A) == 1
    #println("lifted V ="); display([V A])
    @assert prod(V) * Pqp(lc) == Pqp(u)
    V, A, qp
end

function downmod(::Type{Zp}, f::P, q::Integer) where {Zp,X,T,P<:UnivariatePolynomial{T,X}}
    c = map(x->Zp(value(x) ÷ q), f.coeff)
    UnivariatePolynomial{Zp,X}(c)
end


function liftmod(::Type{Z}, a::ZZmod) where {T,Z<:ZZ{T}}
    Z(signed(T)(value(a)))
end
function liftmod(::Type{Z}, a::ZZ) where {X,T,Z<:ZZmod{X,T}}
    Z(value(a))
end
function liftmod(::Type{Z}, a::ZZmod) where {X,T,Z<:ZZmod{X,T}}
    Z(signed(T)(a))
end
function liftmod(::Type{P}, a::Polynomial) where {Z, P<:Polynomial{Z}}
    c = liftmod.(Z, a.coeff)
    P(c)
end

"""
    stripzeros!(q)

count and remove trailing zero coefficients.
"""
function stripzeros!(p)
    c = p.coeff
    n = length(c)
    e = 1
    while e <= n && iszero(c[e])
        e += 1
    end
    e -= 1
    if e > 0
        deleteat!(c, 1:e)
    end 
    p, e
end

"""
    reverse(p::UnivariatePolynomial)

Revert the order of coefficients. decrease degree if `p(0) == 0`. 
"""
Base.reverse(p::P) where P<:UnivariatePolynomial = reverse!(copy(p))
function Base.reverse!(p::P) where P<:UnivariatePolynomial
    c = p.coeff
    n = length(c)
    reverse!(c)
    while n > 0 && iszero(c[n])
        n -= 1
    end
    resize!(c, n)
    p
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

"""
    remove_subset(v::Vector, bitmask::BitVector)

Delete vector element `v[i]` for all `i` with `bitmask[i] == 1`.
"""
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
        return nm - enumx_slow(nm - n, bits)
    end
    s = zero(n)
    d = s
    for k = 0:bits
        t = s + binomial(bits, k)
        mm = binomial(bits - 1, k-1)
        if n < t || t <= 0
            m = n - s
            return (enumx_slow(m + d, bits - 1) << 1) + (m < mm)
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
In other words, `enumx.(0:n, bits)` is sorted by the bitcount.
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

Given vector `v` of mutual coprime elements modulo `p`.
Calculate vector `a` with  `sum(div.(a .* prod(v), v)) == 1 modulo p` and `deg.(a) .< deg.(v)`.
If element type is not a polynomial over `ZZ/p`, read `deg` as `abs`. 
"""
function allgcdx(v::AbstractVector{T}) where T
    # check_mutual_coprime(v)
    #println("allgcdx")
    c = one(T)
    s = prod(v)
    n = length(v)
    w = Vector{T}(undef, n)
    for k = 1:n
        vk = v[k]
        #println("$k n=$n $(basetype(vk)) $vk")
        s = div(s, vk)
        g, a, aa = gcdx(s, vk)
        @assert isone(g)
        #println("g = $g, a = $a, aa = $aa, c = $c, s = $s, vk = $vk f = $f")
#       isone(g) || throw(ArgumentError("factors must be coprime"))
        r, w[k] = divrem(a * c / g, vk)
        c = aa * c / g + r * s
    end
    w
end

function check_mutual_coprime(v)
    n = length(v)
    for i = 1:n
        for k = i+1:n
            g = gcd(v[i], v[k])
            if !isone(g)
                println("not coprime: v[i], v[k], $g = gcd($(v[i]), $(v[k]))")
            end
        end
    end
    nothing
end

"""
    bezout_sum(u, a)

Calculate the sum of products `a[i] * (prod(u) / u[i])`. Should be 1 if `a` are bezout factors of `u`.
"""
function bezout_sum(u::AbstractVector{T}, a::AbstractVector{T}) where T
    n = length(a)
    @assert n == length(u)
    left = Vector{T}(undef, n)
    right = Vector{T}(undef, n)
    left[1] = one(T)
    for i = 1:n-1
        left[i+1] = left[i] * u[i]
    end
    right[n] = one(T)
    for i = n:-1:2
        right[i-1] = right[i] * u[i]
    end
    if n > 1
        sum = zero(T)
        for i = 1:n
            sum += left[i] * right[i] * a[i]
        end
        sum
    else
        one(T)
    end
end

function printfac(fac)
    function comp(t::Tuple{U,V,A}) where {U<:Polynomial,Z<:ZZmod,P<:UnivariatePolynomial{Z},V<:AbstractVector{P},A}
        (LT(t[1]), length(t[2]), modulus(Z))
    end
    println(length(fac))
    display(comp.(fac))
end
