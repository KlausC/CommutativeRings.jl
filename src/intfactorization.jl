"""
    MINPRIME constant for default of first prime to try irreducibility
"""
const MINPRIME =  2147483646 # prevprime(typemax(Int32), 1) - 1

function isirreducible(p::P; p0 = MINPRIME) where {T<:ZI, P<:UnivariatePolynomial{T}}
    (iszero(p) || isunit(p)) && return false
    deg(p) <= 1 && return true
    iszero(p[0]) && return false
    X = varname(P)
    Z = wide_type(T)[X]
    q = convert(Z, p)
    isone(pgcd(q, derive(q))) || return false
    v, e, k = stripzeroscompress(q)
    e > 0 && return false
    k > 1 && !isirreducible(v; p0) && return false
    zassenhaus_irr(q, p0)
end

function isirreducible(p::P; p0 = MINPRIME) where P<:UnivariatePolynomial{<:QQ}
    (iszero(p) || isunit(p)) && return false
    c, pp = content_primpart(p)
    isirreducible(pp; p0)
end

function factor(p::P, a::Integer=1; p0 = MINPRIME) where {T<:ZI,P<:UnivariatePolynomial{T}}
    #println("factor($p)")
    X = varname(P)
    c = content(p)
    Z = wide_type(T)[X]
    q = Z(isone(c) ? copy(p) : p / c)
    x = monom(Z)
    q, e, k = stripzeroscompress(q)
    res = Pair{Z,Int}[]
    isone(c) || push!(res, Z(c) => 1)
    iszero(e) || push!(res, x => e)
    if a > 1 || k > 1
        append!(res, factor_exp(q, k * a, p0))
    else
        factor!(res, q, p0)
    end
    res
end

function factor!(res, q, p0)
    if deg(q) > 0
        r = yun(q)
        for (k, u) in enumerate(r)
            if !isone(u)
                s = zassenhaus(u; p0)
                append!(res, s .=> k)
            end
        end
    end
    res
end

function factor(p::P; p0 = MINPRIME) where P<:UnivariatePolynomial{<:QQ}
    c, pp = content_primpart(p)
    fz = factor(pp; p0)
    fq = Vector{Pair{P,Int}}(undef, length(fz) + 1)
    i = 1
    for (u, k) in fz
        i += 1
        lc = LC(u)
        if isone(lc)
            fq[i] = P(u) => k
        else
            fq[i] = P(u) / lc => k
            c *= lc^k
        end
    end
    if isone(c)
        deleteat!(fq, 1)
    else
        fq[1] = c => 1
    end
    fq
end

"""
    yun(u::UnivariatePolynomial)::Vector

Split integer polynomial `p` into coprime factors `u_i for i = 1:e`
such that `p = u_1^1 * u_2^2 * ... * u_e^e`.
"""
function yun(u::P) where P<:UnivariatePolynomial
    t, v, w = GCD(u, derive(u))
    if isone(t)
        [u]
    else
        res = P[]
        wv = w - derive(v)
        while !iszero(wv)
            u, v, w = GCD(v, wv)
            push!(res, u)
            wv = w - derive(v)
        end
        push!(res, v)
    end
end

function yun(u::P) where P<:UnivariatePolynomial{<:QQ}
    c, q = content_primpart(u) # q is ZZ!
    y = yun(q)
    c *= LC(q)
    z = [P(y[1])*c; [P(y[i])/LC(y[i]) for i in 2:length(y)]]
end

"""
    GCD(u::P, v::P) where P<:UnivariatePolynomial

Calculate `g = gcd(u, v) and
return `gcd(u, v), u / g, v / g`.
"""
function GCD(u, v)
    t = pgcd(u, v)
    isone(t) ? (t, u, v) : (t, u / t, v / t)
end

"""
    issquarefree(p)

Return iff the univariate polynomial `p` is squarefree.
"""
function issquarefree(u::P) where P<:UnivariatePolynomial
    deg(u) <= 0 && return true
    v = derive(u)
    iszero(v) && return false
    w = pgcd(u, v)
    return deg(w) <= 0
end

# implementation of squarefree factorization for characteristic 0
function _sff(u::P, ::Val{0}) where P<:UnivariatePolynomial
    v = yun(u)
    [Pair(v[i], i) for i = axes(v, 1) if deg(v[i]) > 0]
end

function zassenhaus(u; p0)
    zassenhaus2(u, Val(false), p0)
end

function zassenhaus2(u::UnivariatePolynomial{<:ZZ{<:Integer}}, val::Val{BO}, p0) where BO
    Z = ZZ{BigInt}[varname(u)]
    u = convert(Z, u)
    zassenhaus2(u, val, p0)
end

# D = []
function zassenhaus2(u::P, ::Val{BO}, p0) where {BO,T<:Union{ZZ{BigInt},ZZZ},P<:UnivariatePolynomial{T}}
    v, p = best_prime(u, p0)
    a = allgcdx(v)
    #println(" initial v/$p = "); display([v a])
    #empty!(D)
    #push!(D, u)
    #push!(D, deepcopy(v))
    #push!(D, deepcopy(a))
    fac = combinefactors(u, v, a)
    #push!(D, "combinefactors called")
    #push!(D, deepcopy(fac))
    res = P[]
    q = p
    while !all_factors_irreducible!(res, fac, q)
        #push!(D, "all_factors_irreducible! called")
        #push!(D, deepcopy(fac))
        if BO && length(res) >= 1 && deg(res[1]) < deg(u)
            break
        end
        for i = 1:length(fac)
            fac, q = lift!(fac, i)
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
function zassenhaus_irr(u, p0)
    res = zassenhaus2(u, Val(true), p0)
    isempty(res) || deg(res[1]) >= deg(u)
end

# find small prime number >= p0 for which number of
# factors modulo p is smallest
function best_prime(u, p0 = 3, kmax = 5, vmin = 10, vmax = 15)

    kbreak(vl) = vl <= vmin ? 0 : vl > vmax ? vl : kmax

    un = LC(u)
    v, p = factormod(u, p0)
    q = p
    k = 0
    vl = length(v)
    #println("find p = $p length(v) = $vl")
    while k < kbreak(vl)
        w, q = factormod(u, q)
        wl = length(w)
        #println("find p = $q length(v) = $wl")
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
    pfun = p < typemax(Int32) ? x -> nextprime(x+1) : x -> prevprime(x-1)
    X = varname(u)
    un = LC(u)
    v = []
    while isempty(v)
        p = pfun(p)
        compatible_with(p, un) || continue
        Zp = ZZ / p
        unp = Zp(un)
        up = Zp[X](u) / unp
        fac = factor(up) # modulo p
        maximum(last.(fac)) <= 1 || continue
        v = first.(fac)
    end
    v, p
end

"""
    exponents(u::UnivariatePolynomial)

Return the list of exponents with non-zero coefficient.
"""
function exponents(u::UnivariatePolynomial)
    filter(k -> !iszero(u[k]), ord(u):deg(u))
end

"""
    factor(u::UnivariatePolynomial, a::Integer; p0 = MINPRIME)

factorize polynomial `u(x^a)` over `ZZ`.
"""
function factor_exp(u::P, a::Integer, p0) where P<:UnivariatePolynomial
    #println("factor1($u, $a)")
    PP = Pair{P,Int}
    res = PP[]

    for ab in sort(collect(factors(a))) # TODO open question, if fewer factors sufficient
        r = factor!(PP[], u(monom(P, ab)), p0)
        ab == a && return r
        if length(r) > 1
            for (v, e) ∈ r
                b = a ÷ ab
                s = factor_exp(v, b, p0)
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
function compatible_with(p::Integer, u::ZI)
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
    combinefactors(u, v::Vector{<:UnivariatePolynomial{ZZ/p}}, a::Vector{<:UnivariatePolynomial{ZZ/q}})

Given integer polynomial `u` and `v` a monic squarefree factorization of `u modulo p`
(vector of polynomials over ZZ/p), and `a` a vector of corresponding Bezout factors.
Return vector of tuples containing integer polynomial factors `U`, `V` vector with corresponding factorization, and
`A` corresponding Bezout factors modulo `q`.
The vector is build by a brute-force search of all products of subsets of `v`, until a
product divides `u`.

If degrees of `V` sums up to the degree of `U`, that indicates the factorization was successful.
It is also possible, that only one factor is found.
The factors are not proved to be irreducible.
"""
function combinefactors(
    u::Z,
    vv::AbstractVector{<:UnivariatePolynomial{Zp}},
    aa::AbstractVector,
) where {Z<:UnivariatePolynomial{<:ZI},Zp}
    res = Tuple{Z,Any,Any}[]
    un = LC(u)
    unp = Zp(un)
    uu = u * un

    r0 = 0
    while (r = length(vv)) > 0 && r != r0
        n = deg(uu)
        tr = max(UInt64(1) << (r - 1) - 1, 1)
        for i = 1:tr
            d = enumx(i, r)
            nv = deg_prod(vv, d)
            if 2 * nv > n || (2 * nv == n && (d & 1 == 1))
                #println("before d = $(bitstring(d)) nv = $nv n = $n r = $r")
                d = (1 << r - 1) & ~d
                nv = n - nv
                #println("after  d = $(bitstring(d)) nv = $nv n = $n r = $r")
            end
            if dividecheck(uu, unp, vv, d)
                w = pprod(vv, d)
                v = stripmod(Z, w * unp)
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

function stripmod(
    ::Type{P},
    a::UnivariatePolynomial{<:ZZmod},
) where {Z<:ZI,P<:UnivariatePolynomial{Z}}
    P(stripmod.(Z, a.coeff), ord(a))
end
stripmod(::Type{Z}, a::ZZmod) where Z<:ZI = Z(value(a))


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
    coeffbounds(u::UnivariatePolynomial, m)::Vector{<:Integer}

Assuming `u` is a univariate polynomial with integer coefficients and `LC(u) != 0 != u(0)`.
If `u` has an integer factor polynom `v` with `deg(v) == m`,
calculate array of bounds `b` with `abs(v[i]) <= b[i+1] for i = 0:m`.
Algorithm see TAoCP 2.Ed 4.6.2 Exercise 20.
"""
function coeffbounds(u::UnivariatePolynomial{T,X}, m::Integer) where {T<:ZI,X}
    W = widen(basetype(T))
    n = deg(u)
    0 <= m <= n || throw(ArgumentError("required m ∈ [0,deg(u)] but $m ∉ [0,$n]"))
    accuracy = 100 # use fixed point decimal arithmetic with accuracy 0.01 for the norm
    un = abs(value(LC(u)))
    u0 = abs(value(u[0]))
    iszero(u0) && throw(ArgumentError("required u(0) != 0"))
    rua = norm(value.(u.coeff)) * accuracy
    ua = Integer(ceil(rua))
    v = zeros(W, m + 1)
    if m > 0
        v[m+1], v[1] = un, u0
    else
        v[1] = min(u0, un) # abs(content(u)) would be possible but not worth the effort
    end
    u0 *= accuracy
    un *= accuracy
    bk = W(1)
    for j = m-1:-1:1
        bj = bk
        bk = bk * j ÷ (m - j)
        v[j+1] = min(bj * ua + bk * un, bk * ua + bj * u0) ÷ accuracy
    end
    v
end

"""
    hensel_lift(u, v::Vector, a::Vector) -> V, A

Given integer polynomial `u` to be factorized, a vector `v` of polynomials over `Z/q`
and a corresponding vector of Bezout factors `a` over `Z/p`. `q` is an integer power of `p`.

Create output vector `V` of polynomials over `Z/(p*q)`


Algorithm see "D. Knuth - TAoCP 2.Ed 4.6.2 Exercise 22" and
"E. Kaltofen - Factorization of Polynomials"

Assumptions fo the input
* `u = LC(u) * prod(v) mod q`
* `sum( a .* prod(v) ./ v) = 1 mod p` - `(bezout_sum(a, v) == 1)`.

In the case u is not monic, the factor lc(u) has been multiplied into `v[1]`:
`lc(v[1]) == lc(u) mod p` and `lc(v[i]) = 1 for i > 1`.

The output vector V contains polynomials of same degree as corresponding v.
The input relations are propagated to the output `V` and `A` modulo `p * q`.
"""
function hensel_lift(
    u::UnivariatePolynomial{Z},
    v::AbstractVector{Pq},
    a::AbstractVector{Pp},
) where {
    Z<:ZI,
    Zq<:ZZmod,
    Zp<:ZZmod,
    Pq<:UnivariatePolynomial{Zq},
    Pp<:UnivariatePolynomial{Zp},
}

    X = varname(Pq)
    p = modulus(Zp)
    q = modulus(Zq)
    qp = (widemul(q, p))
    Zqp = ZZ / qp
    Pqp = Zqp[X]
    lc = LC(u)
    lci = inv(Zq(lc))

    @assert Pq(u) == prod(v) * lc
    #@assert sum( a.* (prod(v) ./ v)) == 1

    V = liftmod.(Pqp, v)
    f = liftmod(Pqp, u) - prod(V) * Pqp(lc)
    fp = downmod(Zp, f, p) * lci
    fi = rem.(a .* fp, v)
    V .+= liftmod.(Pqp, fi) * p

    A = liftmod.(Pqp, a)
    f = bezout_sum(V, A) - 1
    fp = downmod(Zp, f, q)
    fi = rem.(a .* fp, v)
    A .-= liftmod.(Pqp, fi) * q

    #@assert bezout_sum(V, A) == 1
    #@assert prod(V) * Pqp(lc) == Pqp(u)
    V, A, qp
end

function downmod(::Type{Zp}, f::P, q::Integer) where {Zp,X,T,P<:UnivariatePolynomial{T,X}}
    c = map(x -> Zp(value(x) ÷ q), f.coeff)
    UnivariatePolynomial{Zp,X}(c, ord(f))
end


function _liftmod(::Type{Z}, a::ZZmod) where {Z<:ZI}
    Z(signed(basetype(Z))(value(a)))
end
function _liftmod(::Type{Z}, a::ZI) where {X,T,Z<:ZZmod{X,T}}
    Z(value(a))
end
function _liftmod(::Type{Z}, a::ZZmod) where {X,T,Z<:ZZmod{X,T}}
    Z(signed(T)(a))
end
function liftmod(::Type{P}, a::UnivariatePolynomial) where {Z,P<:UnivariatePolynomial{Z}}
    c = _liftmod.(Z, a.coeff)
    P(c, ord(a))
end

"""
    stripzeros(q)

count and remove trailing zero coefficients.
"""
function stripzeroscompress(p::P) where P<:UnivariatePolynomial
    m = ord(p)
    q = P(p.coeff)
    g = gcd(exponents(q))
    if g > 1
        n = deg(q) ÷ g
        q = P([q[k*g] for k = 0:n])
    end
    q, m, g
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
    preduce((p, v) -> (p[1] * v[0], p[2] * v[0] + p[1] * v[1]), start, vv, n)
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
function smallfactors(
    vv,
    u::P,
    mask = typemax(Int),
) where P<:UnivariatePolynomial{<:ZZ{<:Integer}}
    r = length(vv)
    mask &= (1 << r - 1)
    rm = count_ones(mask)
    up = eltype(vv)(u)
    smaller(n, v, w) = deg(v) <= deg(w) ? (n, v, w) : (mask & ~n, w, v)
    sm1 = Iterators.filter(
        x -> x & mask == x && (2count_ones(x) < rm || 2count_ones(x) == rm && isodd(x)),
        1:2^r-1,
    )
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
        Z = ZZ / abs(value(v0))
        Z(u[1]) == Z(q0) * Z(v[1])
    else
        r0 = u[1] - q0 * v[1]
        iszero(rem(r0, v0))
    end
end

"""
    enumx(n::Integer, bits)::Integer

For each `bits >= 0, n -> enumx(n, bits)` is a bijection of `0:2^bits-1`
in a way that `enumx.(0:2^bits-1, bits)` is sorted by number of ones
in two's complement representation.
In other words, `enumx.(0:n, bits)` is sorted by the bitcount.
"""
function enumx(n::Integer, bits::Int)
    mask = (oftype(n, 1) << bits) - 1
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
            u1, u0 = u0, u0 * (bits - k - 1) ÷ (k + 1)
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

"""
    bezout_sum(u, a)

Calculate the sum of products `a[i] * (prod(u) / u[i])`.
Should be 1 if `a` are bezout factors of `u`.
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

"""
    reduction(p::Polynomial)

Return polynomial `q` and integers `nord`, `g`, `nex` with `p == q * x^ord`
and `q(x) == qq(x^g)` for some `qq`. `nex` is the number of nonzero coefficients of `q`.
"""
function reduction(p::P) where P<:UnivariatePolynomial
    expos = findall(!iszero, p.coeff) .- 1
    nex = length(expos)
    nex <= 1 && return P(LC(p)), ord(p), 1, nex
    best = gcd(expos)
    kbest = ord(p)
    P(p.coeff, 0), kbest, best, nex
end

function ffactor(p::P) where P<:UnivariatePolynomial{<:ZZ}
    #println("ffactor($p)")
    q, nord, n, nex = reduction(p)
    n == 1 && return factor(p)
    ff = Pair{P,Int}[]
    nord != 0 && push!(ff, monom(P) => nord)
    if nex == 2 && iszero(CC(q) + LC(q))
        cyc = cyclotomic(P, deg(q))
        pushmemo!(mfactor, cyc, [cyc => 1])
        append!(ff, mfactor(q / cyc))
        push!(ff, cyc => 1)
        return ff
    end
    for kk ∈ primefactors(n)
        if 1 < kk < n
            k = n ÷ kk
            r = compress(q, k)
            fr = mfactor(r)
            if !(length(fr) == 1 && last(fr[1]) == 1)
                return cfactors!(ff, uncompress.(first.(fr), k) .=> last.(fr))
            end
        end
    end
    return append!(ff, factor(q))
end

function cfactors!(ff::V, f::V) where {P,V<:Vector{<:Pair{P}}}
    for (p, ex) in f
        fp = mfactor(p)
        append!(ff, first.(fp) .=> last.(fp) .* ex)
    end
    ff
end

"""
    memoize(f)

Return a memoized version of one-arg function `f`.

If used recursively make sure that the new function is called.
It can be stored in a global constant to keep the data accessible.
"""
function memoize(f)
    MEMORY = Dict()
    p -> get!(MEMORY, p) do
        f(p)
    end
end

"""
    mfactor(p::UnivariatePolynomial)

Like [`factor`](@ref). Memoize all intermediate results.

Memory is reset using `killmemo!(mfactor)`.
"""
const mfactor = memoize(ffactor)

"""
    killmemo!(mf::Function)

Empty memory of memoized function `mf`.
"""
function killmemo!(f::Function)
    empty!(f.MEMORY)
end

"""
    pushmemo!(f::Function, v)

Push `v` to memory of memoized function.
"""
function pushmemo!(f::Function, k::Any, v::Any)
    get!(f.MEMORY, k) do
        v
    end
    nothing
end
