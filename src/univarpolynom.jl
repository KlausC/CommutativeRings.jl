
# class constructors
# convenience type constructor:
# enable `R[:X]` as short for `UnivariatePolynomial{:X,R}`
getindex(R::Type{<:Ring}, s::Symbol) = UnivariatePolynomial{s,R}

### Constructors
basetype(::Type{<:UnivariatePolynomial{X,T}}) where {X,T} = T
depth(::Type{<:UnivariatePolynomial{X, T}}) where {X,T} = depth(T) + 1
_lcunit(a::UnivariatePolynomial) = lcunit(lc(a))
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

function issimpler(a::T, b::T) where T<:UnivariatePolynomial
    da, db = deg(a), deg(b)
    da < db || da == db && issimpler(lc(a), lc(b))
end

UnivariatePolynomial{X,S}(a::Ring) where {X,S} = convert(UnivariatePolynomial{X,S}, a)
UnivariatePolynomial{X,S}(a::Integer) where {X,S} = convert(UnivariatePolynomial{X,S}, a)

# promotion and conversion
_promote_rule(::Type{UnivariatePolynomial{X,R}}, ::Type{UnivariatePolynomial{Y,S}}) where {X,Y,R,S} = throw(DomainError((X,Y), "cannot promote univariate polynomials with differnet variables"))
_promote_rule(::Type{UnivariatePolynomial{X,R}}, ::Type{UnivariatePolynomial{X,S}}) where {X,R,S} = UnivariatePolynomial{X,promote_type(R,S)}
_promote_rule(::Type{UnivariatePolynomial{X,R}}, ::Type{S}) where {X,R,S<:Ring} = UnivariatePolynomial{X,promote_type(R,S)}
promote_rule(::Type{UnivariatePolynomial{X,R}}, ::Type{S}) where {X,R,S<:Union{Integer,Rational}} = UnivariatePolynomial{X,promote_type(R,S)}


convert(P::Type{UnivariatePolynomial{X,R}}, a::UnivariatePolynomial{X}) where {X,R} = P(convert.(R, a.coeff))
convert(P::Type{UnivariatePolynomial{X,R}}, a::UnivariatePolynomial{Y}) where {X,Y,R} = P(convert.(R, a.coeff))
convert(P::Type{UnivariatePolynomial{X,S}}, a::S) where {X,S} = P([a])
convert(P::Type{UnivariatePolynomial{X,S}}, a::T) where {X,S,T} = P([convert(S, a)])

# convert coefficient vector to polynomial
function UnivariatePolynomial{X,S}(v::Vector{S}) where {X,S<:Ring}
    x = Symbol(X)
    n = length(v)
    while n > 0 && iszero(v[n])
        n -= 1
    end
    if n < length(v)
        v = copyto!(similar(v, n), 1, v, 1, n)
    end
    UnivariatePolynomial{x,S}(v, NOCHECK)
end
# convert coefficient vector to polynomial, element type of vector determines class 
UnivariatePolynomial{X}(v::Vector{S}) where {X,S} = UnivariatePolynomial{X,S}(v)
# convert polynomial with same symbol and type aliasing original
UnivariatePolynomial{X,S}(p::UnivariatePolynomial{X,S}) where {X,S<:Ring} = p
# convert polynomial with different coefficient type
function UnivariatePolynomial{X,S}(p::UnivariatePolynomial{Y}) where {X,Y,S}
    if X == Y
        UnivariatePolynomial{X,S}(S.(p.coeff), NOCHECK)
    elseif S <: UnivariatePolynomial
        yp = S(p)
        UnivariatePolynomial{X,S}([yp], NOCHECK)
    else
        throw(DomainError((X,Y), "cannot convert different variable names"))
    end 
end

function monom(P::Type{<:UnivariatePolynomial{X,S}}, k::Integer) where {X,S}
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
function UnivariatePolynomial{X,S}(v::AbstractVector) where {X,S}
    isempty(v) ? UnivariatePolynomial{X,S}(S[]) : UnivariatePolynomial{X,S}([S(x) for x = v])
end

# canonical embedding homomorphism from base ring
UnivariatePolynomial{X}(r::R) where {X,R<:Ring} = UnivariatePolynomial{X,R}([r])

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
+(p::T, q::Integer) where {X,S,T<:UnivariatePolynomial{X,S}} = p + T([S(q)])
+(q::Integer, p::T) where {X,S,T<:UnivariatePolynomial{X,S}} = +(p, q)
+(q::S, p::T) where {X,S<:Ring,T<:UnivariatePolynomial{X,S}} = +(p, q)

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
-(p::T, q::Ring) where {X,S,T<:UnivariatePolynomial{X,S}} = +(p, -q)
-(p::T, q::Integer) where {X,S,T<:UnivariatePolynomial{X,S}} = +(p, -q)
-(q::Integer, p::T) where {X,S,T<:UnivariatePolynomial{X,S}} = +(-p, q)
-(q::S, p::T) where {X,S<:Ring,T<:UnivariatePolynomial{X,S}} = +(-p, q)

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

function *(p::UnivariatePolynomial, q::Ring)
    if iszero(q)
        zero(p)
    else
        T = typeof(p)
        S = basetype(T)
        # make broadcast recognize q as scalar
        T(p.coeff .* S(q), NOCHECK)
    end
end
*(p::UnivariatePolynomial{X,S}, q::Integer) where {X,S} = *(p, S(q))
*(q::Integer, p::UnivariatePolynomial) = *(p, q)
*(q::Ring, p::UnivariatePolynomial) = *(p, q)

function /(p::T, q::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    d, r = divrem(p, q)
    iszero(r) ? d : throw(DomainError((p, q), "cannot divide a / b"))
end
function /(p::T, q::Ring) where {X,S,T<:UnivariatePolynomial{X,S}}
    T(p.coeff ./ S(q), NOCHECK)
end
/(p::UnivariatePolynomial{X,S}, q::Integer) where {X,S} = /(p, S(q))

function ^(p::P, k::Integer) where P<:UnivariatePolynomial
    k < 0 && throw(DomainError((p,k), "polynom power negative exponent"))
    n = deg(p)
    if k == 0
        one(p)
    elseif k == 1 || n < 0
        p
    elseif n == 0
        P(lc(p)^k)
    elseif n == 1 && ismonom(p)
        monom(P, k)
    else
        Base.power_by_squaring(p, k)
    end
end

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
    uc = lc(q)
    isunit(uc) || return divrem(p, q)[2]
    n > 0 || return zero(typeof(q))
    uc = inv(uc)
    c = p.coeff[m-n+2:m+1]
    cp = p.coeff
    cq = q.coeff
    for i = m-n+1:-1:1
        fc = c[n] * uc
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
    q, r, f = pdivrem(a::T, b::T) where T<:UnivariatePolynomial{X,R}

A variant of divrem, if leading term of divisor is not a unit.
The polynomial `a` is multiplied by a minimal factor `f ∈ R` with
`f * a = q * b + r`.  
"""
function pdivrem(p::T, q::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    cp = p.coeff; cq = q.coeff
    vd, vr, f = divrem(cp, cq, Val(true))
    tweak(vd, cp, p), tweak(vr, cp, p), f
end

"""
    content(p::UnivariatePolynomial)

Return the degree of the polynimial p, i.e. the `gcd` of its coefficients.
"""
content(p::UnivariatePolynomial) = gcd(p.coeff)
function content(q::UnivariatePolynomial{X,Q}) where {X,Q<:Union{QQ,Quotient}}
    c = lcm(getfield.(q.coeff, :den))
    g = gcd(getfield.(q.coeff, :num) .* ( div.(c, getfield.(q.coeff, :den))))
    Q(g , c)
end

"""
    primpart(p::UnivariatePolynomial)

The primitive part of the polynomial p, that means the `gcd` of its coefficients is `1`,
"""
primpart(p::UnivariatePolynomial) = p / content(p)

"""
    deg(p::UnivariatePolynomial)

Return the degree of the polynomial p, i.e. the highest exponent in the polynomial that has a
nonzero coefficient. The degree of the zero polynomial is defined to be -1.
"""
deg(p::UnivariatePolynomial) = length(p.coeff) - 1

function inv(p::T) where T<:UnivariatePolynomial
    if isunit(p)
        return T([inv(p.coeff[1])])
    else
        throw(DomainError(p, "Only unit polynomials can be inverted"))
    end
end

isunit(p::UnivariatePolynomial) = length(p.coeff) == 1 && isunit(p.coeff[1])
isone(p::UnivariatePolynomial) = length(p.coeff) == 1 && isone(p.coeff[1])
iszero(p::UnivariatePolynomial) = length(p.coeff) == 0
zero(::Type{T}) where {X,S,T<:UnivariatePolynomial{X,S}} = T(S[])
one(::Type{T}) where {X,S,T<:UnivariatePolynomial{X,S}} = T([one(S)])
==(p::T, q::T) where T<:UnivariatePolynomial = p.coeff == q.coeff 
==(p::UnivariatePolynomial{X}, q::UnivariatePolynomial{Y}) where {X, Y} = false
function hash(p::UnivariatePolynomial{X}, h::UInt) where X
    n = length(p.coeff)
    n == 0 ? hash(0, h) : n == 1 ? hash(p.coeff[1]) : hash(X, hash(p.coeff, h))
end

ismonom(p::UnivariatePolynomial) = all(iszero.(view(p.coeff, 1:deg(p))))
ismonic(p::UnivariatePolynomial) = isone(lc(p))

# induced homomorphism
function (h::Hom{F,R,S})(p::UnivariatePolynomial{X,<:R}) where {X,F,R,S}
    UnivariatePolynomial{X}(F.(p.coeff))
end

# auxiliary functions

"""
    lc(p::UnivariatePolynomial)

Return the leading coefficient of a non-zero polynomial. This coefficient
cannot be zero. Return zero for zero polynomial.
"""
function lc(p::UnivariatePolynomial{X,S}) where {X,S}
    c = p.coeff
    n = length(c)
    n == 0 ? zero(S) : c[n]
end

# pseudo-division to calculate gcd of polynomial using subresultant pseudo-remainders.

"""
    pgcd(a, b)

Modification of Euclid's algorithm to produce `subresultant sequence of pseudo-remainders`.
The next to last calculated remainder is a scalar multiple of the gcd. 
See: `https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Subresultant_pseudo-remainder_sequence`
"""
function pgcd(a::T, b::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    
    iszero(b) && return a
    da = deg(a)
    db = deg(b)
    d = da - db
    d < 0 && return pgcd(b, a)
    E = one(S)
    ψ = -E
    β = iseven(d) ? E : -E
    while true
        γ = lc(b)
        a = a * γ^(d+1)
        c = rem(a, b) / β
        a, b = b, c
        iszero(b) && break
        # prepare for next turn
        da = db
        db = deg(c)
        ψ = (-γ)^d / ψ^(d-1)
        d = da - db
        β = -γ * ψ^d
    end
    a = primpart(a)
    a / lcunit(a)
end
"""
    g, u, v = pgcdx(a, b)

Extended pseudo GCD algorithm.
Return `g == pgcd(a, b)` and `u, v` with `p * u + q * v == g`.
"""
function pgcdx(a::T, b::T) where {X,S,T<:UnivariatePolynomial{X,S}}
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
    ψ = -E
    β = iseven(d) ? E : -E
    EE = one(T)
    ZZ = zero(T)
    s1, s2, t1, t2 = EE, ZZ, ZZ, EE
    while true
        γ = lc(b)
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
    a/f, s2/cs, t2/cs, f
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
function evaluate(p::UnivariatePolynomial{X,S}, x::T) where {X,S,T}
    _evaluate(p, x)
end
function evaluate(p::U, x::V) where {U<:UnivariatePolynomial,Y,T,V<:UnivariatePolynomial{Y,T}}
    if ismonic(x) && ismonom(x)
        spread(p, deg(x), Y, T)
     else
        _evaluate(p, x)
    end
end

function _evaluate(p::UnivariatePolynomial{X,S}, x::T) where {X,S,T}
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
(p::UnivariatePolynomial)(a) = evaluate(p, a)

"""
    derive(p::UnivariatePolynomial)

Return formal derivative of polynomial `p`.

For `k in 1:deg(p)` we have `derive(p).coeff[k] = k * p.coeff[k+1]`.
If `deg(p) * lc(p) == 0` degree: `deg(derive(p)) < deg(p) - 1`.
"""
function derive(p::P) where P<:UnivariatePolynomial
    n = deg(p)
    c = similar(p.coeff, n)
    for k = 1:n
        c[k] = p.coeff[k+1] * k
    end
    while n > 0 && iszero(c[n])
        n -= 1
    end
    resize!(c, n)
    P(c, NOCHECK)
end

# efficient implementation of `p(x^m)`. 
function spread(p::P, m::Integer) where {X,T,P<:UnivariatePolynomial{X,T}}
    P(_spread(p.coeff, m, T))
end
function spread(p::P, m::Integer, Y, S) where {X,T,P<:UnivariatePolynomial{X,T}}
    c = _spread(p.coeff, m, S)
    UnivariatePolynomial{Y}(c)
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

issimple(::Union{ZZ,ZZmod,QQ,Number}) = true
issimple(::Quotient{X,<:UnivariatePolynomial{:γ}}) where X = true
issimple(::Any) = false

function showvar(io::IO, var, n::Integer)
    if n == 1
        print(io, var)
    elseif n != 0
        print(io, string(var, '^', n))
    end
end
    
function Base.show(io::IO, p::UnivariatePolynomial{X}) where X
    var = X
    N = length(p.coeff)-1
    N < 0 && print(io, '0')
    for n = N:-1:0
        el = p.coeff[n+1]
        bra = !issimple(el)
        if !iszero(el)
            # bra && n != N && print(io, " + ")
            if !isone(el) || n == 0
                io2 = IOBuffer()
                show(io2, el)
                es = String(take!((io2)))
                bra && print(io, '(')
                if !bra && n < N
                    print(io, ' ')
                    if isempty(es) || (es[1] != '-' && es[1] != '+')
                        print(io, '+')
                        print(io, ' ')
                        print(io, es)
                    else
                        print(io, es[1], ' ', es[2:end])
                    end
                else
                  print(io, es)
                end
                bra && print(io, ')')
                if n != 0
                    print(io, '⋅')
                end
            elseif n != N
                print(io, " + ")
            end  
            showvar(io, var, n)
        end
    end
end

