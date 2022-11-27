
# class constructors
# convenience type constructor:
# enable `R[:x]` as short for `UnivariatePolynomial{R,:x}`
getindex(R::Type{<:Ring}, X::Symbol) = UnivariatePolynomial{R,X}

### Constructors
category_trait(P::Type{<:Polynomial}) = category_trait_poly(P, category_trait(basetype(P)))
category_trait_poly(::Type{<:UnivariatePolynomial}, Z::Type{<:FieldTrait}) =
    EuclidianDomainTrait
category_trait_poly(::Type{<:Polynomial}, Z::Type{<:UniqueFactorizationDomainTrait}) =
    UniqueFactorizationDomainTrait
category_trait_poly(::Type, Z::Type{<:IntegralDomainTrait}) = IntegralDomainTrait
category_trait_poly(::Type, ::Type) = CommutativeRingTrait
category_trait_fraction(::Type{<:IntegralDomainTrait}) = FieldTrait
category_trait_fraction(::Type) = CommutativeRingTrait

basetype(::Type{<:Polynomial{T}}) where T = T

"""
    lcunit(p::Polynomial)

Returns iff the leading coefficient is a unit.
"""
function lcunit(a::Polynomial)
    lco = LC(a)
    isunit(lco) ? lco : one(lco)
end

### access to polynomial coefficients
function getindex(u::UnivariatePolynomial{T}, i::Integer) where T
    f = ord(u)
    f <= i <= deg(u) ? u.coeff[i+1-f] : zero(T)
end
getindex(u::UnivariatePolynomial, v::AbstractVector{<:Integer}) = [u[i] for i in v]

"""
    deg(p::Polynomial)

Return the degree of the polynomial p, i.e. the highest exponent in the polynomial that has a
nonzero coefficient. The degree of the zero polynomial is defined to be -1.
"""
deg(p::UnivariatePolynomial) = size(p.coeff, 1) + ord(p) - 1

"""
    ord(p::UnivariatePolynomial)

Return the multiplicity of `0` as a root of `p`. For `p == 0` return `0`.
"""
ord(p::UnivariatePolynomial) = p.first

"""
    varname(P)

Return variable name of univariate polynomial or polynomial type `P` as a symbol.
"""
varname(::Type{<:UnivariatePolynomial{R,X}}) where {R,X} = X
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

# simpler representation?
function issimpler(a::T, b::T) where T<:Polynomial
    da, db = deg(a), deg(b)
    da < db || da == db && issimpler(LC(a), LC(b))
end

# promotion and conversion
_promote_rule(
    ::Type{UnivariatePolynomial{R,X}},
    ::Type{UnivariatePolynomial{S,Y}},
) where {X,Y,R,S} = Base.Bottom # throw(DomainError((X,Y), "cannot promote univariate polynomials with differnet variables"))
_promote_rule(
    ::Type{UnivariatePolynomial{R,X}},
    ::Type{UnivariatePolynomial{S,X}},
) where {X,R,S} = UnivariatePolynomial{promote_type(R, S),X}
_promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Ring} =
    UnivariatePolynomial{promote_type(R, S),X}
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Integer} =
    UnivariatePolynomial{promote_type(R, S),X}
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Rational} =
    UnivariatePolynomial{promote_type(R, S),X}

(P::Type{<:UnivariatePolynomial{S}})(a::S) where {S} = P([a])
(P::Type{<:UnivariatePolynomial{S}})(a::T) where {S,T<:RingInt} = P([S(a)])

# convert coefficient vector to polynomial
function UnivariatePolynomial{T,X}(v::Vector{S}, g::Integer = 0) where {X,T<:Ring,S<:T}
    x = Symbol(X)
    ff = findlast(!iszero, v)
    if ff === nothing
        w = S[]
        f = 0
        g = 0
    else
        f = findfirst(!iszero, v) - 1
        n = length(v)
        w = f != 0 ? v[f+1:ff] : ff < n ? resize!(v, ff) : v
    end
    UnivariatePolynomial{S,x}(f + g, w, NOCHECK)
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
        UnivariatePolynomial{S,X}(co, ord(p))
    elseif S <: UnivariatePolynomial
        co = [S(p)]
        UnivariatePolynomial{S,X}(co)
    else
        throw(
            DomainError((X, Y), "cannot convert polynomials with differing variable names"),
        )
    end
end

function monom(P::Type{<:UnivariatePolynomial}, xv::AbstractVector{<:Integer})
    length(xv) > 1 && throw(ArgumentError("univariate monom has only one variable"))
    monom(P, xv...)
end

function monom(P::Type{<:UnivariatePolynomial{S,X}}, k::Integer = 1) where {S,X}
    v = [one(S)]
    P(v, k)
end

"""
    UnivariatePolynomials{X,S}(vector)

Construct a new polynomial Ring-element.
Allow all coefficient classes, which can be mapped to S, that means
the canonical homomorphism is used.
"""
function UnivariatePolynomial{S,X}(v::AbstractVector, g::Integer = 0) where {X,S}
    isempty(v) ? UnivariatePolynomial{S,X}(S[]) :
    UnivariatePolynomial{S,X}([S(x) for x in v], g)
end

# canonical embedding homomorphism from base ring
UnivariatePolynomial(r::R) where {R<:Ring} = UnivariatePolynomial{R,:x}([r])

# make new copy
copy(p::UnivariatePolynomial) = typeof(p)(copy(p.coeff), ord(p))

"""
    coeffs(p::UnivariatePolynomial)

Return vector of length `deg(p)+1` with all coefficients of polynomial.
First vector element is constant term of polynomial.
"""
coeffs(p::UnivariatePolynomial) = shiftleft(p.coeff, ord(p))

"""
    shiftleft(vector, integer)

Increase size of vector by `s`, copy content and fill lower indices with zeros.
"""
function shiftleft(vp::AbstractVector, s::Integer)
    n = size(vp, 1)
    v = copyto!(similar(vp, n + s), 1 + s, vp, 1, n)
    for i = 1:s
        v[i] = 0
    end
    v
end

### Arithmetic
function +(p::T, q::T) where T<:UnivariatePolynomial
    if deg(p) < deg(q)
        p, q = q, p
    end
    nmin = min(ord(p), ord(q))
    nmax = deg(p) + 1
    vp = p.coeff
    vq = q.coeff
    np = length(vp)
    nq = length(vq)
    v = shiftleft(vp, nmax - np - nmin)
    k = ord(q) - nmin
    for i = 1:nq
        v[i+k] += vq[i]
    end
    T(v, nmin)
end
+(p::T, q::Integer) where {S,T<:UnivariatePolynomial{S}} = p + T([S(q)])
+(q::Integer, p::T) where {S,T<:UnivariatePolynomial{S}} = +(p, q)
+(q::S, p::T) where {S<:Ring,T<:UnivariatePolynomial{S}} = +(p, q)

function -(p::T) where T<:UnivariatePolynomial
    T(ord(p), map(-, p.coeff), NOCHECK)
end
-(p::T, q::T) where T<:UnivariatePolynomial = +(p, -q)
-(p::T, q::Ring) where T<:UnivariatePolynomial = +(p, -q)
-(p::T, q::Integer) where T<:UnivariatePolynomial = +(p, -q)
-(q::Integer, p::T) where T<:UnivariatePolynomial = +(-p, q)
-(q::S, p::T) where {S<:Ring,T<:UnivariatePolynomial{S}} = +(-p, q)

function *(p::T, q::T) where T<:UnivariatePolynomial
    multiply(p, q, deg(p) + deg(q) + 1)
end
function multiply(p::T, q::T, m::Integer) where T<:UnivariatePolynomial
    vp = p.coeff
    vq = q.coeff
    np = length(p.coeff)
    nq = length(q.coeff)
    np <= nq || return multiply(q, p, m)
    nw = np + nq - 1
    nv = min(nw, m)
    if np == 0 || nq == 0
        return zero(T)
    elseif ismonom(p)
        v = isone(LC(p)) ? vq : LC(p) .* vq
        v === vq && ord(p) == 0 && nv == nw && return q
        if nv != nw
            v = v === vq ? vq[1:nv] : resize!(vq, nv)
        end
    elseif ismonom(q)
        v = isone(LC(q)) ? vp : vp .* LC[q]
        v === vp && ord(q) == 0 && nv == nw && return p
        if nv != nw
            v = v === vp ? vp[1:nv] : resize!(vp, nv)
        end
    else
        v = similar(vp, nv)
        @inbounds for k = 1:nv
            i1 = max(k + 1 - np, 1)
            i2 = min(k, nq)
            vk = vp[k-i1+1] * vq[i1]
            for j = i1+1:i2
                vk += vp[k-j+1] * vq[j]
            end
            v[k] = vk
        end
    end
    T(v, ord(p) + ord(q))
end

function *(p::T, q::R) where {R<:Ring,T<:UnivariatePolynomial{R}}
    if iszero(q)
        zero(T)
    else
        # make broadcast recognize q as scalar
        T(p.coeff .* Ref(q), ord(p))
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
    T(p.coeff ./ S(q), ord(p))
end
/(p::UnivariatePolynomial{S}, q::Integer) where S = /(p, S(q))

function ^(p::P, k::Integer) where P<:Polynomial
    n = deg(p)
    if n == 0
        P(LC(p)^k)
    elseif k < 0
        throw(DomainError((p, k), "polynom power negative exponent"))
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

"""
    _divremv(cp::Vector, fp::Int, cq::Vector, fq::Int, F::Val{Bool})

Perform "long division" of polynamials over a ring, represented by `p = cp(x) * x^fp` etc.

Division and remainder algorithm. `d, r = divrem(p, q) => d * q + r == p`.

If the boolean argument is true, perform `pseudo-division` by multiplying
the divident by Ring element in order to allow division.

In the other case, divide by leading term of q. If remainder is not zero
the degree of d is not reduced (lower than that of q).

Attempt to divide by null polynomial throws DomainError.
"""
function _divrem(vp::Vector{S}, op::Int, vq::Vector{S}, oq::Int, ::Val{F}) where {S<:Ring,F}
    np = length(vp)
    nq = length(vq)
    nmin = min(op, oq)
    fp = op - nmin
    fq = oq - nmin
    dp = np + fp - 1
    dq = nq + fq - 1
    nq > 0 || throw(DomainError(vq, "Cannot divide by zero polynomial."))
    f = one(S)
    if dp < dq
        return S[], 0, vp, op, f
    end
    divi = vq[nq]
    if nq == 1
        if isone(divi)
            if fq == 0
                return vp, fp, S[], 0, f
            elseif fq > 0
                return vp[fq+1:np], fp, vp[1:fq], nmin, f
            end
        elseif isunit(divi)
            multi = inv(divi)
            if fq == 0
                return vp .* multi, fp, S[], 0, f
            elseif fq > 0
                return vp[fq+1:np] ./ divi, fp, vp[1:fq], nmin, f
            end
        end
    end
    nn = fq
    if fp > 0
        vp = shiftleft(vp, fp)
        np += fp
    end
    fac = F && !isunit(divi)
    n = fac ? nq - 1 + nn : np
    if dq == 0
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
        vf = similar(vp, np - nq - nn + 1)
        vr = copy(vp)
        for i = np:-1:nq+nn
            vri = vr[i]
            multi, r = divrem(vri, divi)
            if fac && !iszero(r)
                g = divi / gcd(divi, r)
                f *= g
                vri *= g
                smul!(vr, 1:i-1, g)
                smul!(vf, i-nq+2-nn:np-nq+1-nn, g)
                multi = vri / divi
            end
            vr[i] = r
            for j = 1:nq-1
                vr[j+i-nq] -= vq[j] * multi
            end
            vf[i-nq-nn+1] = multi
        end
    end
    resize!(vr, n)
    vf, 0, vr, nmin, f
end

function div(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff
    cq = q.coeff
    d, fd, = _divrem(cp, ord(p), cq, ord(q), Val(false))
    tweak(d, fd, cp, p)
end

function rem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff
    cq = q.coeff
    _, _, r, fr = _divrem(cp, ord(p), cq, ord(q), Val(false))
    tweak(r, fr, cp, p)
end

function divrem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff
    cq = q.coeff
    d, fd, r, fr = _divrem(cp, ord(p), cq, ord(q), Val(false))
    tweak(d, fd, cp, p), tweak(r, fr, cp, p)
end

function tweak(d, fd, cp, p::T) where T<:UnivariatePolynomial
    d === cp && fd == ord(p) ? p : T(d, fd)
end

"""
    divremv(p::P, v::Vector{T}) where T<:UnivariatePolynomial

Find polynomials `a[i]` and remainder `r` with `p == sum(a[i] * v[i]) + r`
with minimal degree of `r`.
"""
function divremv(f::T, g::AbstractVector{T}) where T<:UnivariatePolynomial
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
                    a[i] += d * monom(T, nf - ni)
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
    cp = p.coeff
    cq = q.coeff
    vd, fd, vr, fr, f = _divrem(cp, ord(p), cq, ord(q), Val(true))
    tweak(vd, fd, cp, p), tweak(vr, fr, cp, p), f
end

"""
    content(p::Polynomial)

Return the content of the polynomial p, i.e. the [`gcd`](@ref) of its coefficients,
negated if leading coefficient is negative. See also [`primpart`](@ref).
"""
function content(p::Polynomial)
    g = gcd(p.coeff)
    isnegative(LC(p)) ? -g : g
end
function content(q::Polynomial{Q}) where Q<:Union{QQ,Frac}
    c = lcm(getfield.(q.coeff, :den))
    g = gcd(getfield.(q.coeff, :num) .* (div.(c, getfield.(q.coeff, :den))))
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

The primitive part of the polynomial `p`, equals [`p / content(p)`](@ref).
If the basetype is `QQ`, returned polynomial has basetype `ZZ`.
"""
primpart(p::Polynomial) = p / content(p)
function primpart(p::UnivariatePolynomial{Q,X}) where {Q<:Union{QQ,Frac},X}
    Z = basetype(Q)
    (Z[X])(Z.(numerator.((p / content(p)).coeff)), ord(p))
end

"""
    content_primpart(p::UnivariatePolynomial{<:QQ})

Return content and primpart of a polynomial.
"""
function content_primpart(p::Polynomial)
    c = content(p)
    c, p / c
end
function content_primpart(p::P) where {T,X,P<:UnivariatePolynomial{QQ{T},X}}
    c = content(p)
    Z = ZZ{T}
    pp = Z[X](Z.(numerator.((p / c).coeff)), ord(p))
    c, pp
end

function inv(p::T) where T<:Polynomial
    if isunit(p)
        return T(inv(CC(p)))
    else
        throw(DomainError(p, "Only unit polynomials can be inverted"))
    end
end

isunit(p::Polynomial) = deg(p) == 0 && ismonom(p) && isunit(CC(p))
isone(p::Polynomial) = deg(p) == 0 && ismonom(p) && isone(CC(p))
iszero(p::Polynomial) = isempty(p.coeff)
zero(::Type{T}) where {S,T<:UnivariatePolynomial{S}} = T(S[])
one(::Type{T}) where {S,T<:UnivariatePolynomial{S}} = T([one(S)])
==(p::T, q::T) where {T<:UnivariatePolynomial} = p.coeff == q.coeff && ord(p) == ord(q)
function ==(p::S, q::T) where {S<:UnivariatePolynomial,T<:UnivariatePolynomial}
    (varname(S) == varname(T) || deg(p) == 0) && ord(p) == ord(q) && p.coeff == q.coeff
end

function hash(p::UnivariatePolynomial{S,X}, h::UInt) where {X,S}
    n = length(p.coeff)
    if n == 0
        hash(zero(S), h)
    elseif n == 1 && deg(p) == 1
        hash(CC(p), h)
    else
        hash(ord(p), hash(X, hash(p.coeff, h)))
    end
end

"""
    ismonom(p::Polynomial)

Return iff polynomial `p` is identical to its leading term ond not `0`.
"""
ismonom(p::UnivariatePolynomial) = length(p.coeff) == 1

"""
    ismonic(p::Polynomial)

Return iff leading coefficient [`LC`](@ref) of polynomial `p` is one.
"""
ismonic(p::Polynomial) = isone(LC(p))

# induced homomorphism
function (h::Hom{F,R,S})(p::UnivariatePolynomial{<:R,X}) where {X,F,R,S}
    UnivariatePolynomial{S,X}((h.f).(p.coeff), ord(p))
end

# auxiliary functions

"""
    LC(p::Polynomial)

Return the leading coefficient of a non-zero polynomial. This coefficient
cannot be zero. Return zero for zero polynomial.
"""
function LC(p::Polynomial{T}) where T
    c = p.coeff
    n = length(c)
    n == 0 ? zero(T) : c[n]
end

function LM(p::P) where {S,P<:UnivariatePolynomial{S}}
    n = length(p.coeff)
    n == 0 && return zero(P)
    P(ones(S, 1), n - 1)
end

"""
    LT(p::Polynomial)

Return leading term of polynomial `p`. Coefficient is taken from `p`.
"""
function LT(p::P) where {S,P<:UnivariatePolynomial{S}}
    n = length(p.coeff)
    n == 0 && return zero(P)
    P([p.coeff[n]], n - 1)
end

"""
    CC(p::UnivariatePolynomial)

Return the constant coefficient of polynomial.
"""
CC(p::UnivariatePolynomial) = p[0]

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
    a / lcunit(a) * cc
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

"""
    invert(p, q)

Inverse of `p` modulo `q`, where both are polynomials of the same type.
If the base type is not a field, typically no inverse exists.
"""
function invert(p::T, q::T) where T<:UnivariatePolynomial
    g, u, v, f = pgcdx(p, q)
    if isunit(g) && isunit(f)
        u / g / f
    else
        throw(DomainError((p, q), "p is not invertible modulo q"))
    end
end

"""
    reverse(p::UnivariatePolynomial)

Revert the order of coefficients. If `n = deg(p)` and `k`` maximal with `x^k` divides `p`,
then `reverse(p) == x^(n + k) * p(1 // x)`. The degree of `p` is not changed.
"""
Base.reverse(p::P) where P<:UnivariatePolynomial = reverse!(copy(p))
function Base.reverse!(p::P) where P<:UnivariatePolynomial
    reverse!(p.coeff)
    p
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
function evaluate(
    p::U,
    x::V,
) where {U<:UnivariatePolynomial,Y,T,V<:UnivariatePolynomial{T,Y}}
    if ismonic(x) && ismonom(x)
        spread(p, deg(x), Y, T)
    else
        _evaluate(p, x)
    end
end

function _evaluate(p::UnivariatePolynomial{S}, x::T) where {S,T}
    c = p.coeff
    n = length(c)
    d = n + ord(p) - 1
    R = promote_type(S, eltype(T))
    d < 0 && return one(x) * zero(R)
    d == 0 && return one(x) * R(c[1])
    iszero(x) && return one(x) * R(p[0])
    a = convert(R, c[n])
    for k = n-1:-1:1
        a *= x
        a += c[k]
    end
    a * x^ord(p)
end
(p::UnivariatePolynomial)(a, b...) = evaluate(p, a, b...)

"""
    derive(p::UnivariatePolynomial)

Return formal derivative of polynomial `p`.

For `k in 1:deg(p)` we have `derive(p)[k-1] = k * p[k]`.
If `deg(p) * LC(p) == 0` degree: `deg(derive(p)) < deg(p) - 1`.
"""
function derive(p::P) where P<:UnivariatePolynomial
    vp = p.coeff
    n = length(vp)
    f = ord(p) - 1
    n <= 0 && return p
    c = similar(vp, n)
    for k = 1:n
        c[k] = vp[k] * (k + f)
    end
    P(c, f)
end

# efficient implementation of `p(x^m)`.
function spread(p::P, m::Integer) where {T,P<:UnivariatePolynomial{T}}
    P(_spread(p.coeff, ord(p), m, T)...)
end
function spread(p::P, m::Integer, Y, S) where {P<:UnivariatePolynomial}
    c, f = _spread(p.coeff, ord(p), m, S)
    UnivariatePolynomial{eltype(typeof(c)),Y}(c, f)
end

function _spread(c::Vector{T}, fc::Int, m::Integer, ::Type{S}) where {T,S}
    n = length(c)
    R = promote_type(S, T)
    v = zeros(R, max(0, (n - 1) * m + 1))
    for k = 1:n
        v[(k-1)*m+1] += c[k]
    end
    v, fc * m
end

function isless(p::T, q::T) where T<:UnivariatePolynomial
    dp = deg(p)
    dq = deg(q)
    dp < dq && return true
    dq < dp && return false
    for k = dp:-1:0
        isless(p[k], q[k]) && return true
        isless(q[k], p[k]) && return false
    end
    false
end

### Display functions

import Base: show

issimple(::Union{ZZ,ZZmod,QQ,Number}) = true
issimple(::Quotient{<:UnivariatePolynomial{S,:γ}}) where S = true
issimple(p::Polynomial) = ismonom(p)
issimple(::Any) = false

function showvar(io::IO, p::UnivariatePolynomial{S,X}, n::Integer) where {X,S}
    n += ord(p)
    if n == 1
        print(io, X)
    elseif n != 0
        print(io, string(X, '^', n))
    end
end

import Base: adjoint
adjoint(p::UnivariatePolynomial) = derive(p)

isconstterm(p::UnivariatePolynomial, n::Integer) = n + ord(p) == 0

show(io::IO, p::Polynomial) = _show(io, p, Val(true))

function _show(io::IO, p::P, ::Val{Z}) where {P<:Polynomial,Z}
    T = basetype(P)
    c = p.coeff
    N = length(p.coeff) - 1
    N < 0 && return show(io, zero(T))
    start = true
    ord = Z ? (N:-1:0) : (0:N)
    for n in ord
        el = c[n+1]
        iszero(el) && (!start || !Z) && continue
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
    v = sprint(show, el; context = io)
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

# TODO determinants to dedicated file
function LinearAlgebra.det(a::AbstractMatrix{D}) where D<:Ring
    checksquare(a)
    det!(copy(a))
end
det!(a::AbstractMatrix{D}) where D<:Union{Ring,Number} = _det(a, category_trait(D))

_det(a::AbstractMatrix, ::Type{<:IntegralDomainTrait}) = det_DJB!(a)
_det(a::AbstractMatrix{D}, ::Type{<:IntegralDomainTrait}) where D<:QuotientRing =
    det_DJB!(a)
_det(a::AbstractMatrix{D}, ::Type{<:CommutativeRingTrait}) where D<:QuotientRing =
    det_QR!(a)
_det(a::AbstractMatrix, ::Type{<:CommutativeRingTrait}) = det_Bird(a)

"""
    det_DJB(a::Matrix{D}) where D<:Union{Ring,Number}

This code is taken from "Algorithm 8.36 (Dogdson-Jordan-Bareiss)" of
"Algorithms in Real Algebraic Geometry" by Basu, Pollak, Roy - 2016.

Its use is restricted to the case of `D` an integral domain.
"""
det_DJB(a::AbstractMatrix{D}) where D<:Union{Ring,Number} = det_DJB!(copy(a))

function det_DJB!(b::AbstractMatrix{D}) where D<:Union{Ring,Number}
    n = checksquare(b)
    @assert category_trait(D) <: IntegralDomainTrait
    b00 = one(D)
    n == 0 && return b00
    s = 1
    for k = 1:n-1
        j0 = 0
        for j = k:n
            if !iszero(b[k, j])
                j0 = j
                break
            end
        end
        if j0 == 0
            return zero(D)
        end
        if j0 != k
            for i = k:n
                b[i, j0], b[i, k] = b[i, k], b[i, j0]
            end
            s = -s
        end
        bkk = b[k, k]
        for i = k+1:n
            bik = b[i, k]
            b[i, k] = 0
            for j = k+1:n
                bkj = b[k, j]
                bij = b[i, j]
                b[i, j] = div(bkk * bij - bik * bkj, b00)
            end
        end
        b00 = bkk
    end
    return b[n, n] * s
end

"""
    det_QR(a::Matrix{D}) where D<:QuotientRing

This code is an extension of det_DJB to certain quotient rings which are domains.
I.e. `ZZ/p` where `p` is not prime and `P[:x]/q` where `q` is the product of polynomials.
"""
det_QR(a::AbstractMatrix{D}) where {Z,D<:QuotientRing{Z}} = det_QR!(copy(a))

function det_QR!(b::AbstractMatrix{D}) where {Z,D<:QuotientRing{Z}}
    n = checksquare(b)
    s = one(D)
    n == 0 && return s

    for k = 1:n-1
        a = view(b, k:n, k:n)
        ij = findfirst(isunit, a)
        if ij !== nothing
            ij += CartesianIndex(k - 1, k - 1)
            s = flipall!(b, ij, k, s)
        else
            for i = k:n
                ij, s = rowdivgcd!(b, i, k, ij, s)
                iszero(s) && return s
            end
            if ij !== nothing
                s = flipall!(b, ij, k, s)
            else
                # now no element of `a` is unit - all have common divisors with `m`
                m = modulus(D)
                ij = findfirst(!iszero, a)
                u = value(a[ij])
                v, w = splitmod(u, m)
                # println("splitmod($u, $m) = $v, $w")
                @assert v != m && w != m
                ZV = Quotient(v, Z)
                dv = det!(ZV.(a))
                isone(w) && return dv
                ZW = Quotient(w, Z)
                dw = det!(ZW.(a))
                return _crt(D(value(dv)), D(value(dw)), v, w) * s
            end
        end
        bkk = one(D)
        for i = k+1:n
            bik = b[i, k]
            for j = k+1:n
                bkj = b[k, j]
                bij = b[i, j]
                b[i, j] = bkk * bij - bik * bkj
            end
        end
    end
    return b[n, n] * s
end

function flipall!(a::AbstractMatrix, ij::CartesianIndex, k, s)
    # println("flipall($ij, $k)")
    # display(a)
    i, j = ij[1], ij[2]
    if i != k
        s = -s
        for u = k:size(a, 2)
            a[i, u], a[k, u] = a[k, u], a[i, u]
        end
    end
    if j != k
        s = -s
        for u = k:size(a, 1)
            a[u, j], a[u, k] = a[u, k], a[u, j]
        end
    end
    akk = a[k, k]
    if isunit(akk)
        for u = k:size(a, 2)
            # println("a[$k,$u] / akk == $(a[k,u]) / $akk = $(a[k,u] / akk)")
            a[k, u] /= akk
        end
        s *= akk
    end
    # println("k = $k:")
    # display(a)
    s
end

"""
    rowdivgcd!(b::Matrix, i, k, ij, s)

Divide row `b[i,k::end]` by the gcd of that row.
Return gcd, index of a now unit element of the row, s * gcd
"""
function rowdivgcd!(b::AbstractMatrix{D}, i, k, ij, s) where {Z,D<:QuotientRing{Z}}
    n = size(b, 2)
    g = gcd_generator(value(b[i, j]) for j = k:n)
    s *= g
    if !isone(g) && !iszero(g)
        for j = k:n
            bij = D(value(b[i, j]) ÷ g)
            b[i, j] = bij
            if ij === nothing && isunit(bij)
                ij = CartesianIndex(i, j)
            end
        end
    end
    ij, s
end

"""
    _crt(x, y, p, q)

Chinese remainder theorem.
"""
function _crt(x, y, p, q)
    g, u, v = gcdx(p, q)
    y * u * p + x * v * q
end
"""
    v = splitmod(a, m)

Find `v` which divides `m` in a way that `gcd(v, m/v) == 1`.
The input `a < m` with `gcd(a, m) != 1 serves as a starting point.
"""
function splitmod(v, m)
    a = gcd(v, m)
    @assert 1 < a < m
    b = m ÷ a
    x = 1

    while !isone(b)
        g = gcd(a, b)
        if !isone(g)
            b ÷= g
            x += 1
        else
            break
        end
        v = g
    end
    a = v^x
    b = m ÷ a
    a, b
end

"""
    det_Bird(a::Matrix{D}) where D

This is a division-free algorithm to calculate the determinant of `a`.
There are no conditions on `D` except it is a non-empty commutative ring with one.
Derived from "Pearls of Functional Algorithm Design, chap. 22" by Richard Bird - 2010
"""
det_Bird(a::AbstractMatrix{D}) where D = det_Bird!(copy(a), a)
function det_Bird!(x::AbstractMatrix{D}, a::AbstractMatrix{D}) where D
    n = checksquare(x)
    n == 0 && return one(D)
    for k = n-1:-1:1
        mutx!(x, k, a)
    end
    isodd(n) ? x[1, 1] : -x[1, 1]
end

function mutx!(x::AbstractMatrix, k::Integer, a::AbstractMatrix{T}) where T
    # assuming size(x) == size(a) == (n, n) && 0 < k < n
    n = size(a, 1)
    for j = 1:n
        for i = j+1:n
            x[i, j] = 0
        end
    end
    s = -x[k+1, k+1]
    x[k+1, k+1] = 0
    for j = k:-1:1
        xjj = x[j, j]
        x[j, j] = s
        s -= xjj
    end
    s = zero(T)
    for l = k:n
        s += x[k, l] * a[l, k]
    end
    x[k, k] = s
    for j = k+1:n
        x[k, j] = 0
    end
    for i = k-1:-1:1
        for j = i:n
            x[j, 1] = x[i, j]
        end
        for j = n:-1:1
            s = zero(T)
            for l = i:n
                s += x[l, 1] * a[l, j]
            end
            x[i, j] = s
        end
        for j = i+1:n
            x[j, 1] = 0
        end
    end
    x
end

"""
    det_MV(a)

Divisionfree combinatoric algorithm to calculate determinant.
"Determinant: Combinatorics, Algorithms, andComplexity" by Mahajan, Vinay
in Chicago Journal of Theoretical Computer Science1997-5
http://cjtcs.cs.uchicago.edu/articles/1997/5/cj97-05.pdf
"""
function det_MV(a::AbstractMatrix{D}) where D<:Union{Ring,Integer}
    n = checksquare(a)
    A1 = zeros(D, n, n)
    A2 = zeros(D, n, n)
    B1 = zeros(D, n, n)
    B2 = zeros(D, n, n)
    p = n & 1 + 1
    for u = 1:n
        (p == 1 ? A1 : A2)[u, u] = one(D)
    end
    for i = 0:n-2
        for u = 1:n
            for v = u:n
                Auvp = A1[u, v]
                if !iszero(Auvp)
                    for w = u+1:n
                        #println("addpush(0, $u, $w, $(Auvp*a[v,w]))")
                        B1[u, w] += Auvp * a[v, w]
                        #println("addpush(1, $w, $w, $(Auvp * a[v,u]))")
                        B2[w, w] += Auvp * a[v, u]
                    end
                end
                Auvp = A2[u, v]
                if !iszero(Auvp)
                    for w = u+1:n
                        #println("addpush(1, $u, $w, $(Auvp*a[v,w]))")
                        B2[u, w] += Auvp * a[v, w]
                        #println("addpush(0, $w, $w, $(Auvp * a[v,u]))")
                        B1[w, w] += Auvp * a[v, u]
                    end
                end
            end
        end
        A1, B1 = B1, A1
        A2, B2 = B2, A2
        fill!(B1, zero(D))
        fill!(B2, zero(D))
        #println("i = $i")
        #display([A1 A2])
    end

    for u = 1:n
        for v = u:n
            avu = a[v, u]
            if !iszero(avu)
                B1[1, 1] += A1[u, v] * avu
                B2[1, 1] += A2[u, v] * avu
            end
        end
    end
    B2[1, 1] - B1[1, 1]
end

#=
TODO fix algorithm. normal forms to dedicated file
"""
    hermite_normal_form(A::AbstractMatrix{R}) where R<:Ring -> H, U

Calculate matrixes `H` in column Hermite normal form and unimodular `U` with `A * U = H`.
Unimodular means `det(U)` is unit element of the ring `R`.

See [Wiki](https://en.wikipedia.org/wiki/Hermite_normal_form)
[Algorithm](https://www.math.tamu.edu/~rojas/kannanbachemhermitesmith79.pdf)
"""
function hermite_normal_form(a::Matrix{R}) where R<:Union{Ring,Integer}
    m, n = size(a)
    u = Matrix(R.(I(n)))
    hermite_normal_form!(copy(a), u)
end

function hermite_normal_form!(a::Matrix{R}, u::Matrix{R}) where R<:Ring
    m, n = size(a)

    for i = 1:min(m, n)-1
        for j = 1:i
            ajj = a[j, j]
            aji = a[j, i+1]
            r, p, q = gcdx(ajj, aji)
            pp = -div(aji, r)
            qq = div(ajj, r)
            for k = 1:m
                akj = a[k, j]
                aki = a[k, i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                a[k, j] = bkj
                a[k, i+1] = bki
            end
            for k = 1:n
                akj = u[k, j]
                aki = u[k, i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                u[k, j] = bkj
                u[k, i+1] = bki
            end
            reduce_off_diagonal!(a, u, j)
        end
        reduce_off_diagonal!(a, u, i + 1)
    end
    a, u
end

function reduce_off_diagonal!(a, u, k)
    akk = a[k, k]
    if akk < 0
        akk = -akk
        a[:, k] .= -a[:, k]
        u[:, k] .= -u[:, k]
    end
    for z = 1:k-1
        d = div(-a[k, z], akk)
        a[:, z] .+= a[:, k] .* d
        u[:, z] .+= u[:, k] .* d
    end
end
=#
