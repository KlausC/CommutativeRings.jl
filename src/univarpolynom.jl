
# class constructors
# convenience type constructor:
# enable `R[:x]` as short for `UnivariatePolynomial{R,:x}`
getindex(R::Type{<:Ring}, X::Symbol) = UnivariatePolynomial{R,X}

### Constructors
basetype(::Type{<:Polynomial{T}}) where T = T
depth(::Type{T}) where T<:Polynomial = depth(basetype(T)) + 1
function lcunit(a::Polynomial)
    lco = LC(a)
    isunit(lco) ? lco : one(lco)
end

### access to polynomial coefficients
function getindex(u::UnivariatePolynomial, i::Integer)
    0 <= i <= deg(u) ? u.coeff[i+1] : zero(basetype(u)) 
end

"""
    varname(P)

Return variable name of univariate polynomial or polynomial type `P` as a symbol.
"""
varname(::Type{T}) where {R,X,T<:UnivariatePolynomial{R,X}} = X
varname(::T) where T<:Polynomial = varname(T)

"""
    iscoprime(a, b)

Return if there is a common non-unit divisor of `a` and `b`.
"""
function iscoprime(a::T, b::T) where T<:UnivariatePolynomial
    g, u, v, f = pgcdx(a, b)
    isunit(g) || !isunit(f)
end
"""
    isinvertible(a, b)

Return if there is an inverse of `a` mod ` b`.
"""
function isinvertible(a::T, b::T) where T<:UnivariatePolynomial
    g, u, v, f = pgcdx(a, b)
    isunit(g) && isunit(f)
end

function issimpler(a::T, b::T) where T<:Polynomial
    da, db = deg(a), deg(b)
    da < db || da == db && issimpler(LC(a), LC(b))
end

# promotion and conversion
_promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{UnivariatePolynomial{S,Y}}) where {X,Y,R,S} = Base.Bottom # throw(DomainError((X,Y), "cannot promote univariate polynomials with differnet variables"))
_promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{UnivariatePolynomial{S,X}}) where {X,R,S} = UnivariatePolynomial{promote_type(R,S),X}
_promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Ring} = UnivariatePolynomial{promote_type(R,S),X}
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Integer} = UnivariatePolynomial{promote_type(R,S),X}
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Rational} = UnivariatePolynomial{promote_type(R,S),X}


(P::Type{<:UnivariatePolynomial{S}})(a::S) where {S} = P([a])
(P::Type{<:UnivariatePolynomial{S}})(a::T) where {S,T} = P([S(a)])

# convert coefficient vector to polynomial
function UnivariatePolynomial{T,X}(v::Vector{S}) where {X,T<:Ring,S<:T}
    x = Symbol(X)
    n = length(v)
    while n > 0 && iszero(v[n])
        n -= 1
    end
    if n < length(v)
        v = copyto!(similar(v, n), 1, v, 1, n)
    end
    UnivariatePolynomial{S,x}(v, NOCHECK)
end
# convert coefficient vector to polynomial, element type of vector determines class 
UnivariatePolynomial(x::Symbol, v::Vector{S}) where {S} = UnivariatePolynomial{S,x}(v)
UnivariatePolynomial(x::Symbol, v::S) where {S} = UnivariatePolynomial{S,x}([v])
# convert polynomial with same symbol and type aliasing original
UnivariatePolynomial{S,X}(p::UnivariatePolynomial{S,X}) where {X,S<:Ring} = p
# convert polynomial with different coefficient type
function UnivariatePolynomial{S,X}(p::UnivariatePolynomial{T,Y}) where {X,Y,S,T}
    if X == Y
        co = [S(c) for c in p.coeff]
        UnivariatePolynomial{S,X}(co)
    elseif S <: UnivariatePolynomial
        co = [S(p)]
        UnivariatePolynomial{S,X}(co)
    else
        throw(DomainError((X,Y), "cannot convert polynomials with differing variable names"))
    end 
end

function monom(P::Type{<:UnivariatePolynomial}, xv::Vector{<:Integer})
    length(xv) > 1 && throw(ArgumentError("univariate monom has only one variable"))
    monom(P, xv...)
end

function monom(P::Type{<:UnivariatePolynomial{S}}, k::Integer=1) where S
    k = max(k, -1)
    v = zeros(S,k+1)
    v[k+1] = one(S)
    P(v)
end

"""
    UnivariatePolynomials{X,S}(vector)

Construct a new polynomial Ring-element.
Allow all coefficient classes, which can be mapped to S, that means
the canonical homomorphism is used.
"""
function UnivariatePolynomial{S,X}(v::AbstractVector) where {X,S}
    isempty(v) ? UnivariatePolynomial{S,X}(S[]) : UnivariatePolynomial{S,X}([S(x) for x = v])
end

# canonical embedding homomorphism from base ring
UnivariatePolynomial(r::R) where {R<:Ring} = UnivariatePolynomial{R,:x}([r])

# make new copy
copy(p::UnivariatePolynomial) = typeof(p)(copy(p.coeff))


### Arithmetic
function +(p::T, q::T) where T<:UnivariatePolynomial
    vp = p.coeff
    vq = q.coeff
    np = length(vp)
    nq = length(vq)
    np >= nq || return +(q, p)
    v = copyto!(similar(vp, np), 1, vp, 1, np)
    for i = 1:nq
        v[i] += vq[i]
    end
    while np > 0 && iszero(v[np])
        np -= 1
    end
    if np < length(v)
        resize!(v, np)
    end
    T(v, NOCHECK)
end
+(p::T, q::Integer) where {S,T<:UnivariatePolynomial{S}} = p + T([S(q)])
+(q::Integer, p::T) where {S,T<:UnivariatePolynomial{S}} = +(p, q)
+(q::S, p::T) where {S<:Ring,T<:UnivariatePolynomial{S}} = +(p, q)

function -(p::T) where T<:UnivariatePolynomial
    vp = p.coeff
    np = length(vp)
    v = similar(vp)
    for i = 1:np
        v[i] = -vp[i]
    end
    T(v, NOCHECK)
end
-(p::T, q::T) where T<:UnivariatePolynomial = +(p, -q)
-(p::T, q::Ring) where T<:UnivariatePolynomial = +(p, -q)
-(p::T, q::Integer) where T<:UnivariatePolynomial = +(p, -q)
-(q::Integer, p::T) where T<:UnivariatePolynomial = +(-p, q)
-(q::S, p::T) where {S<:Ring,T<:UnivariatePolynomial{S}} = +(-p, q)

function *(p::T, q::T) where T<:UnivariatePolynomial
    vp = p.coeff
    vq = q.coeff
    np = length(p.coeff)
    nq = length(q.coeff)
    np <= nq || return *(q, p)
    nv = np + nq - 1
    if np == 0 || nq == 0
        return zero(T)
    elseif ismonom(p)
        v = multmono(p, np, vp, q, nq, vq)
    elseif ismonom(q)
        v = multmono(q, nq, vq, p, np, vp)
    else
        v = similar(vp, nv)
        for k = 1:nv
            i1 = max(k+1-np,1)
            i2 = min(k,nq)
            vk = vp[k-i1+1] * vq[i1]
            for j = i1+1:i2
                vk += vp[k-j+1] * vq[j]
            end
            v[k] = vk
        end
    end
    v === vp ? p : v === vq ? q : T(v, NOCHECK)
end

function *(p::UnivariatePolynomial{R}, q::R) where R<:Ring
    if iszero(q)
        zero(p)
    else
        T = typeof(p)
        S = basetype(T)
        # make broadcast recognize q as scalar
        T(p.coeff .* Ref(q), NOCHECK)
    end
end
*(p::UnivariatePolynomial{S}, q::Integer) where {S} = *(p, S(q))
*(q::Integer, p::UnivariatePolynomial) = *(p, q)
*(q::R, p::UnivariatePolynomial{R}) where R<:Ring = *(p, q)

function /(p::T, q::T) where {S,T<:UnivariatePolynomial{S}}
    d, r = divrem(p, q)
    iszero(r) ? d : throw(DomainError((p, q), "cannot divide a / b"))
end
function /(p::T, q::Ring) where {S,T<:UnivariatePolynomial{S}}
    T(p.coeff ./ S(q), NOCHECK)
end
/(p::UnivariatePolynomial{S}, q::Integer) where S = /(p, S(q))

function ^(p::P, k::Integer) where P<:Polynomial
    n = deg(p)
    if n == 0
        P(LC(p)^k)
    elseif k < 0
        throw(DomainError((p,k), "polynom power negative exponent"))
    elseif k == 0
        one(p)
    elseif k == 1 || n < 0
        p
    elseif n > 0 && ismonom(p)
        indv = multideg(p)
        lco = LC(p)
        mon = monom(P, k * indv)
        if !isone(lco) && !isempty(indv)
            mon.coeff[end] = lco^k
        end
        mon
    else
        Base.power_by_squaring(p, k)
    end
end

"""
    multideg(p::Polynomial)

Return vector of variable exponents of the leading monomial of `p`.
"""
multideg(p::UnivariatePolynomial) = [deg(p)]

function smul!(v::Vector{S}, r, m::S) where S
    for i in r
        v[i] *= m
    end
    v
end

# division and remainder algorithm. d, r = divrem(p, q) => d * q + r == p.
# if the third argument is true, perform `pseudo-division` by multiplying
# the divident by Ring element in order to allow division.
# In the other case, divide by leading term of q. If remainder is not zero
# the degree of d is not reduced (lower than that of q).
# Attempt to divide by null polynomial throws DomainError.
function divrem(vp::Vector{S}, vq::Vector{S}, ::Val{F}) where {S<:Ring,F}
    np = length(vp)
    nq = length(vq)
    nq > 0 || throw(DomainError(vq, "Cannot divide by zero polynomial."))
    f = one(S)
    if np < nq
        return S[], vp, f
    end
    divi = vq[nq]
    fac = F && !isunit(divi)
    n = fac ? nq - 1 : np
    if nq == 1
        isone(divi) && return vp, S[], f
        vf = copy(vp)
        if fac
            f = divi / gcd(divi, gcd(vp))
            !isone(f) && smul!(vf, 1:np, f)
        end
        vr = similar(vf)
        for i = 1:np
            vf[i], vr[i] = divrem(vf[i], divi)
        end
    else
        vf = similar(vp, np - nq + 1)
        vr = copy(vp)
        for i = np:-1:nq
            vri = vr[i]
            multi, r = divrem(vri, divi)
            if fac && !iszero(r) 
                g = divi / gcd(divi, r)
                f *= g
                vri *= g
                smul!(vr, 1:i-1, g)
                smul!(vf, i-nq+2:np-nq+1, g)
                multi = vri / divi
            end
            vr[i] = r
            for j = 1:nq-1
                vr[j+i-nq] -= vq[j] * multi
            end
            vf[i-nq+1] = multi
        end
    end
    while n > 0 && iszero(vr[n])
        n -= 1
    end
    resize!(vr, n)
    n = length(vf)
    while n > 0 && iszero(vf[n])
        n -= 1
    end
    resize!(vf, n)
    vf, vr, f
end

function rem(p::T, q::T) where T<:UnivariatePolynomial
    m = deg(p)
    n = deg(q)
    m < n && return p
    uc = LC(q)
    isunit(uc) || return divrem(p, q)[2]
    n > 0 || return zero(typeof(q))
    c = p.coeff[m-n+2:m+1]
    cp = p.coeff
    cq = q.coeff
    for i = m-n+1:-1:1
        fc = c[n] / uc
        for k = n:-1:2
            c[k] = c[k-1] - cq[k] * fc
        end
        c[1] = cp[i] - cq[1] * fc
    end
    typeof(q)(c)
end

function divrem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    d, r = divrem(cp, cq, Val(false))
    tweak(d, cp, p), tweak(r, cp, p)
end

function tweak(d, cp, p::T) where T<:UnivariatePolynomial
    d === cp ? p : T(d, NOCHECK)
end

function div(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    d = divrem(cp, cq, Val(false))[1]
    tweak(d, cp, p)
end

function divrem(f::T, g::AbstractVector{T}) where T<:UnivariatePolynomial
    n = length(g)
    a = zeros(T, n)
    r = copy(f.coeff)
    nf = length(r)
    while nf > 0
        modi = false
        for i = 1:n
            gi = g[i].coeff
            ni = length(gi)
            if ni <= nf
                lcgi = gi[ni]
                d = div(r[nf], lcgi)
                if !iszero(d)
                    modi = true
                    a[i] += d * monom(T, nf-ni)
                    nj = nf - ni
                    for j = nf-ni+1:nf
                        rj = r[j] - gi[j-nf+ni] * d
                        r[j] = rj
                        if !iszero(rj)
                            nj = j
                        end
                    end
                    nf = nj
                end
            end
        end
        if !modi
            nf -= 1
        end
        while nf > 0 && iszero(r[nf])
            nf -= 1
        end
    end
    a, T(r)
end

"""
    q, r, f = pdivrem(a::T, b::T) where T<:UnivariatePolynomial{R}

A variant of divrem, if leading term of divisor is not a unit.
The polynomial `a` is multiplied by a minimal factor `f ∈ R` with
`f * a = q * b + r`.  
"""
function pdivrem(p::T, q::T) where {S,T<:UnivariatePolynomial{S}}
    cp = p.coeff; cq = q.coeff
    vd, vr, f = divrem(cp, cq, Val(true))
    tweak(vd, cp, p), tweak(vr, cp, p), f
end

"""
    content(p::Polynomial)

Return the content of the polynomial p, i.e. the `gcd` of its coefficients,
negated if leading coefficient is negative.
"""
function content(p::Polynomial)
    g = gcd(p.coeff)
    isnegative(LC(p)) ? -g : g
end
function content(q::Polynomial{Q}) where Q<:Union{QQ,Quotient}
    c = lcm(getfield.(q.coeff, :den))
    g = gcd(getfield.(q.coeff, :num) .* ( div.(c, getfield.(q.coeff, :den))))
    g = isnegative(LC(q)) ? -g : g
    Q(g, c)
end
"""
    isnegative(a::Ring)

Check if a < 0.
"""
function isnegative(a::RingInt)
    a < zero(a)
end

"""
    primpart(p::Polynomial)

The primitive part of the polynomial p, that means the `gcd` of its coefficients is `1`,
"""
primpart(p::Polynomial) = p / content(p)

#=
Return the degree of the polynomial p, i.e. the highest exponent in the polynomial that has a
nonzero coefficient. The degree of the zero polynomial is defined to be -1.
=#
deg(p::UnivariatePolynomial) = length(p.coeff) - 1

function inv(p::T) where T<:Polynomial
    if isunit(p)
        return T(inv(p[0]))
    else
        throw(DomainError(p, "Only unit polynomials can be inverted"))
    end
end

isunit(p::Polynomial) = deg(p) == 0 && isunit(LC(p))
isone(p::Polynomial) = deg(p) == 0 && isone(LC(p))
iszero(p::Polynomial) = deg(p) < 0
zero(::Type{T}) where {S,T<:UnivariatePolynomial{S}} = T(S[])
one(::Type{T}) where {S,T<:UnivariatePolynomial{S}} = T([one(S)])
==(p::T, q::T) where {T<:UnivariatePolynomial} = p.coeff == q.coeff
function ==(p::S, q::T) where {S<:UnivariatePolynomial,T<:UnivariatePolynomial}
    (varname(S) == varname(T) || deg(p) == 0) && p.coeff == q.coeff
end
==(p::Polynomial, q::Polynomial) = false
function hash(p::UnivariatePolynomial{S,X}, h::UInt) where {X,S}
    n = length(p.coeff)
    n == 0 ? hash(0, h) : n == 1 ? hash(p[0]) : hash(X, hash(p.coeff, h))
end

"""
    ismonom(p::Polynomial)

Return iff polynomial `p` consists is identical to its leading term.
"""
ismonom(p::UnivariatePolynomial) = all(iszero.(view(p.coeff, 1:deg(p))))
"""
    ismonic(p::Polynomial)

Return iff leading coefficient of polynomial `p` is one. 
"""
ismonic(p::Polynomial) = isone(LC(p))

# induced homomorphism
function (h::Hom{F,R,S})(p::UnivariatePolynomial{<:R,X}) where {X,F,R,S}
    UnivariatePolynomial{S,X}((h.f).(p.coeff))
end

# auxiliary functions

"""
    LC(p::Polynomial)

Return the leading coefficient of a non-zero polynomial. This coefficient
cannot be zero. Return zero for zero polynomial.
"""
function LC(p::Polynomial)
    c = p.coeff
    n = length(c)
    n == 0 ? zero(basetype(p)) : c[n]
end

function LM(p::P) where {S,P<:UnivariatePolynomial{S}}
    n = length(p.coeff)
    n == 0 && return zero(P)
    coeff = zeros(S, n)
    coeff[n] = one(S)
    P(coeff)
end

"""
    LT(p::Polynomial)

Return leading term of polynomial `p`. Coefficient is taken from `p`.
"""
function LT(p::P) where {S,P<:UnivariatePolynomial{S}}
    n = length(p.coeff)
    n == 0 && return zero(P)
    coeff = zeros(S, n)
    coeff[n] = p.coeff[n]
    P(coeff)
end

"""
    pgcd(a, b)

Pseudo gcd of univariate polynomials gcd`a` and `b`.
Uses subresultant sequence to accomplish non-field coeffient types.
"""
function pgcd(a::T, b::T) where {S,T<:UnivariatePolynomial{S}}
    iszero(b) && return a
    iszero(a) && return b
    a, cc = presultant_seq(a, b, Val(false))
    a = primpart(a)
    a / lcunit(a) * cc
end

"""
    resultant(a, b)

Calculate resultant of two univariate polynomials of general coeffient types.
"""
function resultant(a::T, b::T) where {S,T<:UnivariatePolynomial{S}}
    _, _, r = presultant_seq(a, b, Val(true))
    r(0)
end
resultant(a::T, b::T) where T = iszero(a) || iszero(b) ? zero(T) : oneunit(T)
resultant(a, b) = resultant(promote(a,b)...)

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
See: `https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Subresultant_pseudo-remainder_sequence`
and TAoCP 2nd Ed. 4.6.1.
"""
function presultant_seq(a::T, b::T, ::Val{Usedet})  where {Usedet,S,T<:UnivariatePolynomial{S}}
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
    s *= cc^(da+db)
    ψ = -E
    β = iseven(d) ? -E : E
    det = isodd(da) && isodd(db) ? -E : E
    while true
        γ = LC(b)
        δ = γ^(d+1)
        a = a * δ
        c = rem(a, b)
        iszero(c) && break
        dc = deg(c)
        c /= β
        # prepare for next turn
        if Usedet
            det = det * δ ^ db / γ ^ (da - dc) / β ^ db
        
        end
        if isodd(db) && isodd(dc)
            det = -det
        end
        ψ = iszero(d) ? ψ : (-γ)^d / ψ^(d-1)
        a, b = b, c
        da, db = db, dc
        d = da - db
        β = -γ * ψ^d
    end
    r = db > 0 ? zero(b) : d < 1 ? one(b) : d == 1 ? b : LC(b)^(d-1) * b
    b, cc, r * s / det
end

"""
    signed_subresultant_polynomials(P::T, Q::T) where {S,T<:UnivariatePolynomial{S}}

This code is taken from "Algorithm 8.76 (Signed Subresultant Polynomials)"
"Algorithms in Real Algebraic Geometry" by Basu, Pollak, Roy - 2016.
Its use is restricted to the case of `S` is an integral domain (there is no non-trivial divisor of zero).
"""
function signed_subresultant_polynomials(P::T, Q::T)  where {S,T<:UnivariatePolynomial{S}}
    # epsi(n) = (-1) ^ (n*(n-1)÷2)
    epsi(n::Int) = iseven(n >> 1) ? 1 : -1
    p, q = deg(P), deg(Q)
    p > q || throw(ArgumentError("degree of polynomials: $p is not > $q"))
    sresp = zeros(T, p+1)
    s = zeros(S, p+1)
    t = zeros(S, p+1)
    sresp[p+1] = P
    s[p+1] = t[p+1] = 1
    sresp[p] = Q
    bq = LC(Q)
    t[p] = bq
    if p > q - 1
        bqp = bq ^ (p - q - 1)
        sresp[q+1] = (epsi(p-q) * bqp) * Q
    end
    s[q+1] = LC(sresp[q+1])
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
                t[j-d] = (t[j]*t[j-d+1]) / s[j+1] * sig
                sig = -sig
            end
            s[k+1] = t[k+1]
            sresp[k+1] = s[k+1] * sresp[j] / t[j]
            if k > 0
                sresp[k] = -rem((t[j] * s[k+1]) * sresp[i], sresp[j]) / (s[j+1] * t[i])
            end
        end
        if k > 0
            t[k] = LC(sresp[k])
        end
        i, j = j, k
    end
    sresp
end

"""
    g, u, v, f = pgcdx(a, b)

Extended pseudo GCD algorithm.
Return `g == pgcd(a, b)` and `u, v, f` with `a * u + b * v == g * f`.
"""
function pgcdx(a::T, b::T) where {X,S,T<:UnivariatePolynomial{S}}
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
        γd = γ^(d+1)
        a = a * γd
        q, c = divrem(a, b)
        c /= β
        a, b = b, c
        iszero(b) && break
        s1, s2 = s2, (s1 * γd - s2 * q) / β    
        t1, t2 = t2, (t1 * γd - t2 * q) / β    
        # prepare for next turn
        da = db
        db = deg(c)
        ψ = d == 0 ? ψ : (-γ)^d / ψ^(d-1)
        d = da - db
        β = -γ * ψ^d
    end
    cs = gcd(content(s2), content(t2))
    a = a / cs
    f = content(a)
    a / (f / cc), s2 / cs, t2 / cs, f
end

"""
    sylvester(u::P, v::P) where P<:UnivariatePolynomial

Return sylvester matrix of polynomials `u` and `v`.
"""
function LinearAlgebra.sylvester(v::P, u::P) where {Z,P<:UnivariatePolynomial{Z}}
    nu = deg(u)
    nv = deg(v)
    n = max(nu, 0) + max(nv, 0)
    S = zeros(Z, n, n)
    if nv >= 0
        for k = 1:nu
            S[k:k+nv,k] .= reverse(v.coeff)
        end
    end
    if nu >= 0
        for k = 1:nv
            S[k:k+nu,k+nu] .= reverse(u.coeff)
        end
    end
    S
end

"""
    resultant_naive(u, v)

Reference implementation of resultant (determinant of sylvester matrix)
"""
function resultant_naive(u::P, v::P) where {Z,P<:UnivariatePolynomial{Z}}
    S = sylvester(u, v)
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

"""
    invert(p, q)

Inverse of `p` modulo `q`, where both are polynomials of the same type.
If the base type is not a field, typically no inverse exists.
"""
function invert(p::T, q::T) where T <: UnivariatePolynomial
    g, u, v, f = pgcdx(p, q)
    if isunit(g) && isunit(f)
        u / g / f
    else
        throw(DomainError((p, q), "p is not invertible modulo q"))
    end
end

# multiply p * q with a monom p
function multmono(p, np, vp, q, nq, vq)
    fact = vp[np]
    if isone(fact) && np == 1
        return vq
    end
    v = similar(vq, np + nq - 1)
    z = zero(fact)
    for i = 1:np-1
        v[i] = z
    end
    for i = 1:nq
        v[i+np-1] = vq[i] * fact
    end
    v
end

"""
    evaluate(p, y)

Evaluate polynomial by replacing variable `:x` by `y`. `y` may be an object which
can be converted to `basetype(p)` or another polynomial.
Convenient method ot evaluate is is `p(y)`.
"""
function evaluate(p::UnivariatePolynomial{S}, x::T) where {S,T}
    _evaluate(p, x)
end
function evaluate(p::U, x::V) where {U<:UnivariatePolynomial,Y,T,V<:UnivariatePolynomial{T,Y}}
    if ismonic(x) && ismonom(x)
        spread(p, deg(x), Y, T)
     else
        _evaluate(p, x)
    end
end

function _evaluate(p::UnivariatePolynomial{S}, x::T) where {S,T}
    c = p.coeff
    n = length(c)
    R = promote_type(S,T)
    n == 0 && return zero(R)
    n == 1 && return R(c[1])
    a = convert(R, c[n])
    for k = n-1:-1:1
        a *= x
        a += c[k]
    end
    a
end
(p::UnivariatePolynomial)(a, b...) = evaluate(p, a, b...)

"""
    derive(p::UnivariatePolynomial)

Return formal derivative of polynomial `p`.

For `k in 1:deg(p)` we have `derive(p)[k-1] = k * p[k]`.
If `deg(p) * LC(p) == 0` degree: `deg(derive(p)) < deg(p) - 1`.
"""
function derive(p::P) where P<:UnivariatePolynomial
    n = deg(p)
    n < 0 && return p
    c = similar(p.coeff, n)
    for k = 1:n
        c[k] = p[k] * k
    end
    while n > 0 && iszero(c[n])
        n -= 1
    end
    resize!(c, n)
    P(c, NOCHECK)
end

# efficient implementation of `p(x^m)`. 
function spread(p::P, m::Integer) where {T,P<:UnivariatePolynomial{T}}
    P(_spread(p.coeff, m, T))
end
function spread(p::P, m::Integer, Y, S) where {T,P<:UnivariatePolynomial{T}}
    c = _spread(p.coeff, m, S)
    UnivariatePolynomial(Y, c)
end

function _spread(c::Vector{T}, m::Integer, ::Type{S}) where {T,S}
    n = length(c)
    R = promote_type(S, T)
    v = zeros(R, max(0, (n - 1) * m + 1))
    for k = 1:n
        v[(k-1)*m+1] = c[k]
    end
    v
end

function Base.isless(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff
    cq = q.coeff
    lp = length(cp)
    lq = length(cq)
    lp < lq && return true
    lq < lp && return false 
    for k = lp:-1:1
        isless(cp[k], cq[k]) && return true
        isless(cq[k], cp[k]) && return false
    end
    false
end

### Display functions

import Base: show

issimple(::Union{ZZ,ZZmod,QQ,Number}) = true
issimple(::Quotient{<:UnivariatePolynomial{S,:γ}}) where S = true
issimple(p::Polynomial) = ismonom(p)
issimple(::Any) = false

function showvar(io::IO, ::UnivariatePolynomial{S,X}, n::Integer) where {X,S}
    if n == 2
        print(io, X)
    elseif n != 1
        print(io, string(X, '^', n-1))
    end
end

isconstterm(::UnivariatePolynomial, n::Integer) = n == 1

function show(io::IO, p::Polynomial{T}) where T
    N = length(p.coeff)
    N <= 0 && return show(io, zero(T))
    start = true
    for n = N:-1:1
        el = p.coeff[n]
        iszero(el) && !start && continue
        !start && print(io, ' ')
        if isconstterm(p, n)
            showelem(io, el, start)
        else
            if isone(el)
                !start && print(io, "+ ")
            elseif isone(-el)
                print(io, '-')
                !start && print(io, ' ')
            elseif !isconstterm(p, n)
                if !issimple(el)
                    !start && print(io, "+ ")
                    print(io, '(')
                    show(io, el)
                    print(io, ')')
                else
                    showelem(io, el, start)
                end
                print(io, '*')
            end
        end
        showvar(io, p, n)
        start = false
    end
end

function showelem(io::IO, el, start::Bool)
    v = sprint(show, el, context=io)
    v1 = v[1]
    if v1 == '-'
        print(io, '-')
        !start && print(io, ' ')
        print(io, SubString(v, nextind(v, 1)))
    else
        start || print(io, "+ ")
        print(io, v1 == '+' ? SubString(v, nextind(v, 1)) : v)
    end
end

# This code is taken from "Algorithm 8.36 (Dogdson-Jordan-Bareiss)" of
# "Algorithms in Real Algebraic Geometry" by Basu, Pollak, Roy - 2016.
# Its use is restricted to the case of `D` is an integral domain (there is no non-trivial divisor of zero).
function LinearAlgebra.det(a::Matrix{D}) where D<:Ring
    m, n = size(a)
    m == n || throw(ArgumentError("matrix for determinant is not quadratic"))
    n == 0 && return one(D)
    b = copy(a)
    b00 = one(D)
    s = 1
    for k = 0:n-2
        j0 = 0
        for j = k+1:n
            if !iszero(b[k+1,j])
                j0 = j
                break
            end
        end
        if j0 == 0
            return zero(D)
        end
        if j0 != k+1
            for i = k+1:n
                b[i,j0], b[i,k+1] = b[i,k+1], b[i,j0]
            end
            s = -s
        end
        bkk = b[k+1,k+1]
        for i = k+2:n
            bik = b[i,k+1]
            b[i,k+1] = 0
            for j = k+2:n
                bkj = b[k+1,j]
                bij = b[i,j]
                b[i,j] = (bkk * bij - bik * bkj) / b00
            end
        end
        b00 = bkk
    end
    return b[n,n] * s
end

function det1(a::Matrix{D}) where D<:Ring
    m, n = size(a)
    m == n || throw(ArgumentError("matrix for determinant is not quadratic"))
    n == 0 && return one(D)
    b = copy(a)
    c = zeros(D, n, n)
    b00 = one(D)
    s = 1
    for k = 0:n-2
        j0 = 0
        for j = k+1:n
            if !iszero(b[k+1,j])
                j0 = j
                break
            end
        end
        if j0 == 0
            return zero(D)
        end
        if j0 != k+1
            for i = k+1:n
                b[i,j0], b[i,k+1] = b[i,k+1], b[i,j0]
                c[i,j0], c[i,k+1] = c[i,k+1], c[i,j0]
            end
            s = -s
        end
        bkk = b[k+1,k+1]
        for i = k+2:n
            bik = b[i,k+1] 
            b[i,k+1] = 0
            for j = k+2:n
                bkj = b[k+1,j]
                bij = b[i,j]
                b[i,j] = bij
                c[i,j] = -bik * bkj
            end
        end
        b00 = bkk
    end
    return b[n,n] * s
end

function hamilton_normal_form(a::Matrix{R}) where R<:Union{Ring,Integer}
    m, n = size(a)
    u = Matrix(R.(I(n)))
    hamilton_normal_form!(copy(a), u)
end

function hamilton_normal_form!(a::Matrix, u::Matrix)
    m, n = size(a)

    for i = 1:min(m,n)-1
        for j = 1:i
            ajj = a[j,j]
            aji = a[j,i+1]
            r, p, q = gcdx(ajj, aji)
            pp = -div(aji, r)
            qq = div(ajj, r)
            for k = 1:m
                akj = a[k,j]
                aki = a[k,i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                a[k,j] = bkj
                a[k,i+1] = bki
            end
            for k = 1:n
                akj = u[k,j]
                aki = u[k,i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                u[k,j] = bkj
                u[k,i+1] = bki
            end
            reduce_off_diagonal!(a, u, j)
        end
        reduce_off_diagonal!(a, u, i + 1)
    end
    a, u
end

function reduce_off_diagonal!(a, u, k)
    akk = a[k,k]
    if akk < 0
        akk = -akk
        a[:,k] .= -a[:,k]
        u[:,k] .= -u[:,k]
    end
    for z = 1:k-1
        d = div(-a[k,z], akk)
        a[:,z] .+= a[:,k] .* d
        u[:,z] .+= u[:,k] .* d
    end
end
