
"""
pgcd(a, b)

Pseudo gcd of univariate polynomials `a` and `b`.
Uses subresultant sequence to accomplish non-field coeffient types.
"""
function pgcd(a::T, b::T) where {S,T<:UnivariatePolynomial{S}}
    iszero(b) && return a
    iszero(a) && return b
    a, cc = presultant_seq(a, b, Val(false))
    a = primpart(a)
    T(a / lcunit(a)) * cc
end

"""
resultant(a, b)

Calculate resultant of two univariate polynomials of general coeffient types.
"""
function resultant(a::T, b::T) where {S,T<:UnivariatePolynomial{S}}
    _resultant(a, b, category_trait(S))
end
function _resultant(
    a::T,
    b::T,
    ::Type{<:EuclidianDomainTrait},
) where {S,T<:UnivariatePolynomial{S}}
    _, _, r = presultant_seq(a, b, Val(true))
    r(0)
end

function _resultant(
    a::T,
    b::T,
    ::Type{<:CommutativeRingTrait},
) where {S,T<:UnivariatePolynomial{S}}
    resultant_naive(a, b)
end

resultant(a::T, b::T) where T = iszero(a) || iszero(b) ? zero(T) : oneunit(T)
resultant(a, b) = resultant(promote(a, b)...)

"""
discriminant(a)

Calculate discriminant of a univariate polynomial `a`.
"""
function discriminant(a::UnivariatePolynomial)
    la = LC(a)
    s = iseven(deg(a) >> 1) ? la : -la
    resultant(a, derive(a)) / s
end

"""
presultant_seq(a, b)

Modification of Euclid's algorithm to produce `subresultant sequence of pseudo-remainders`.
The next to last calculated remainder is a scalar multiple of the gcd.
Another interpretation of this remainder yields the resultant of `a` and `b`.
See: [`WIKI: Subresultant`](https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Subresultant_pseudo-remainder_sequence)
and TAoCP 2nd Ed. 4.6.1.
"""
function presultant_seq(
    a::T,
    b::T,
    ::Val{Usedet},
) where {Usedet,S,T<:UnivariatePolynomial{S}}
    E = one(S)
    da = deg(a)
    db = deg(b)
    d = da - db
    s = E
    if d < 0
        a, b, da, db, d = b, a, db, da, -d
        if isodd(da) && isodd(db)
            s = -s
        end
    end
    cc, a, b = normgcd(a, b)
    iszero(b) && return b, cc, b
    s *= cc^(da + db)
    ψ = -E
    β = iseven(d) ? -E : E
    det = isodd(da) && isodd(db) ? -E : E
    while true
        γ = LC(b)
        δ = γ^(d + 1)
        a = a * δ
        c = rem(a, b)
        iszero(c) && break
        dc = deg(c)
        c /= β
        # prepare for next turn
        if Usedet
            det = det * δ^db / γ^(da - dc) / β^db
        end
        if isodd(db) && isodd(dc)
            det = -det
        end
        ψ = iszero(d) ? ψ : (-γ)^d / ψ^(d - 1)
        a, b = b, c
        da, db = db, dc
        d = da - db
        β = -γ * ψ^d
    end
    r = db > 0 ? zero(b) : d < 1 ? one(b) : d == 1 ? b : LC(b)^(d - 1) * b
    b, cc, r * s / det
end

"""
signed_subresultant_polynomials(P::T, Q::T) where {S,T<:UnivariatePolynomial{S}}

This code is taken from "Algorithm 8.21 (Signed Subresultant Polynomials)"
"Algorithms in Real Algebraic Geometry" by Basu, Pollak, Roy - 2006.
Its use is restricted to the case of `S` is an integral domain
(there is no non-trivial divisor of zero). Effort is `O(deg(p)*deg(q))`.
"""
function signed_subresultant_polynomials(P::T, Q::T) where {S,T<:UnivariatePolynomial{S}}
    # epsi(n) = (-1) ^ (n*(n-1)÷2)
    epsi(n::Int) = iseven(n >> 1) ? 1 : -1
    p, q = deg(P), deg(Q)
    p > q || throw(ArgumentError("degree of polynomials: $p is not > $q"))
    sresp = zeros(T, p + 1)
    s = zeros(S, p + 1)
    t = zeros(S, p + 1)
    sresp[p+1] = P
    s[p+1] = t[p+1] = 1 # (sign(LC(P))
    sresp[p] = Q
    bq = LC(Q)
    sq = bq
    t[p] = bq
    if p > q - 1
        bqp = bq^(p - q - 1)
        sq = bqp * epsi(p - q)
        sresp[q+1] = sq * Q
        sq *= bq
    end
    s[q+1] = sq
    i = p + 1
    j = p
    while j > 0 && !iszero(sresp[j])
        k = deg(sresp[j])
        if k == j - 1
            s[j] = t[j]
            if k > 0
                sresp[k] = -rem(s[j]^2 * sresp[i], sresp[j]) / (s[j+1] * t[i])
            end
        elseif k < j - 1
            s[j] = 0
            sig = -1
            for d = 1:j-k-1
                t[j-d] = (t[j] * t[j-d+1]) / s[j+1] * sig
                sig = -sig
                s[k+1] = t[k+1]
                sresp[k+1] = s[k+1] * sresp[j] / t[j]
            end
            for l = j-2:-1:k+1
                sresp[l+1] = 0
                s[l+1] = 0
            end
            if k > 0
                sresp[k] = -rem((t[j] * s[k+1]) * sresp[i], sresp[j]) / (s[j+1] * t[i])
            end
        end
        if k > 0
            t[k] = LC(sresp[k])
        end
        i, j = j, k
    end
    for l = 0:j-2
        sresp[l+1] = 0
        s[l+1] = 0
    end
    sresp, s
end

"""
g, u, v, f = pgcdx(a, b)

Extended pseudo GCD algorithm.
Return `g == pgcd(a, b)` and `u, v, f` with `a * u + b * v == g * f`.
"""
function pgcdx(a::T, b::T) where {S,T<:UnivariatePolynomial{S}}
    E = one(S)
    iszero(b) && return a, E, zero(S), a
    iszero(a) && return b, zero(S), E, b
    da = deg(a)
    db = deg(b)
    d = da - db
    if d < 0
        g, u, v, f = pgcdx(b, a)
        return g, v, u, f
    end
    cc, a, b = normgcd(a, b)
    ψ = -E
    β = iseven(d) ? E : -E
    EE = one(T)
    ZZ = zero(T)
    s1, s2, t1, t2 = EE, ZZ, ZZ, EE
    while true
        γ = LC(b)
        γd = γ^(d + 1)
        a = a * γd
        q, c, h = pdivrem(a, b)
        c /= β
        a, b = b, c
        iszero(b) && break
        s1, s2 = s2, (s1 * γd - s2 * q) / β
        t1, t2 = t2, (t1 * γd - t2 * q) / β
        # prepare for next turn
        da = db
        db = deg(c)
        ψ = d == 0 ? ψ : (-γ)^d / ψ^(d - 1)
        d = da - db
        β = -γ * ψ^d
    end
    cs = gcd(content(s2), content(t2))
    a = a / cs
    f = content(a)
    a / (f / cc), s2 / cs, t2 / cs, f
end

"""
sylvester_matrix(u::P, v::P) where P<:UnivariatePolynomial

Return sylvester matrix of polynomials `u` and `v`.
"""
function sylvester_matrix(v::P, u::P) where {Z,P<:UnivariatePolynomial{Z}}
    nu = deg(u)
    nv = deg(v)
    n = max(nu, 0) + max(nv, 0)
    S = zeros(Z, n, n)
    if nv >= 0
        for k = 1:nu
            S[k:k+nv, k] .= reverse(v.coeff)
        end
    end
    if nu >= 0
        for k = 1:nv
            S[k:k+nu, k+nu] .= reverse(u.coeff)
        end
    end
    S
end

"""
resultant_naive(u, v)

Reference implementation of resultant (determinant of sylvester matrix)
"""
function resultant_naive(u::P, v::P) where {Z,P<:UnivariatePolynomial{Z}}
    S = sylvester_matrix(u, v)
    det(S)
end

"""
g, ag, bg = normgcd(a, b)

Divided `a` and `b` by the gcd of their contents.
"""
function normgcd(a, b)
    ca = content(a)
    cb = content(b)
    g = gcd(ca, cb)
    isunit(g) ? (one(g), a, b) : (g, a / g, b / g)
end
