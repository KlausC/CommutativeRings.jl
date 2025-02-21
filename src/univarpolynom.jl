
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

Returns leading coefficient `lco` if that is a unit, otherwise `lcunit(lco)`.
"""
function lcunit(a::Polynomial)
    lco = LC(a)
    isunit(lco) ? lco : lcunit(lco)
end

### access to polynomial coefficients
function getindex(u::UnivariatePolynomial{T}, i::Integer) where T
    f = ord(u)
    f <= i <= deg(u) ? u.coeff[i+1-f] : zero(T)
end
getindex(u::UnivariatePolynomial, v::AbstractVector{<:Integer}) = [u[i] for i in v]
getindex(u::UnivariatePolynomial, ::Colon) = getindex(u, 0:deg(u))

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
) where {X,Y,R,S} = Base.Bottom
#throw(DomainError((X,Y), "cannot promote univariate polynomials with different variables"))
promote_rule(
    ::Type{UnivariatePolynomial{R,X}},
    ::Type{UnivariatePolynomial{S,X}},
) where {X,R,S} = UnivariatePolynomial{promote_type(R, S),X}
function _promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Ring}
    U = promote_type(R, S)
    U <: Ring ? UnivariatePolynomial{U,X} : Base.Bottom
end
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Integer} =
    UnivariatePolynomial{promote_type(R, S),X}
promote_rule(::Type{UnivariatePolynomial{R,X}}, ::Type{S}) where {X,R,S<:Rational} =
    UnivariatePolynomial{promote_type(R, S),X}

(P::Type{<:UnivariatePolynomial{S}})(a::S) where {S} = P([a])
function (P::Type{<:UnivariatePolynomial{S}})(a::UnivariatePolynomial{T,X}) where {S,T,X}
    UnivariatePolynomial{S,X}(a.first, S.(a.coeff), NOCHECK)
end
(P::Type{<:UnivariatePolynomial{S}})(a::T) where {S,T<:RingInt} = P([S(a)])

# convert coefficient vector to polynomial
function UnivariatePolynomial{T,X}(v::Vector{S}, g::Integer = 0) where {X,T<:Ring,S<:T}
    g = Int(g)
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
convert(::Type{P}, p::P) where P<:Polynomial = p
function convert(
    ::Type{P},
    p::UnivariatePolynomial{T,X},
) where {X,S,T,P<:UnivariatePolynomial{S,X}}
    P(p)
end
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

function monom(P::Type{<:UnivariatePolynomial}, xv::AbstractVector{<:Integer}, lc = 1)
    length(xv) > 1 && throw(ArgumentError("univariate monom has only one variable"))
    monom(P, xv..., lc)
end

"""
    monom(::Type{<:UnivariatePolynomial}, n = 1)

Return monic monomial of degree `n`.
"""
function monom(P::Type{<:UnivariatePolynomial{S,X}}, k::Integer = 1, lc = 1) where {S,X}
    v = [S(lc)]
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

# canonical embedding homomorphism from base ring - use default varname `:x`
UnivariatePolynomial(r::R) where {R<:Ring} = UnivariatePolynomial{R,:x}([r])

# make new copy
copy(p::UnivariatePolynomial) = typeof(p)(copy(p.coeff), ord(p))

"""
    mult_by_monom(p, k)

Return a new polynomial with the same coefficient vector, and `ord` increased by `k`.
"""
mult_by_monom(p::UnivariatePolynomial, k::Integer) = typeof(p)(p.coeff, ord(p) + k)

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
# multiply up to given precision `m`
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

# scalar multiplication of part of vector
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
    pp = Z[X]([Z(numerator(x/c)) for x in p.coeff], ord(p))
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
    R = promote_type(S, eltype(T))
    iszero(x) && return convert(R, p[0]) * one(x)
    c = p.coeff
    n = length(c)
    a = n == 0 ? zero(R) : convert(R, c[n])
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

"""
    companion(p::UnivariatePolynomial[, q::UnivariatePolynomial])

Return the companion matrix of monic polynomial `p`.
The negative of `p`'s trailing coefficients are in the last column of the matrix.
Its characteristic polynomial is identical to `p`.

If `q` is given, return the companion matrix with respect to `q`. For `q == x` that is
identical to the original definition. If `p` is the minimal polynomial of an algebraic
number `a`, then `det(x*I - companion(p, q))` is a multiple of the minimal polynomial
of `q(a)`.

Note, that `companion(p, q) == q(companion(p))`.
"""
function companion(p::UnivariatePolynomial{T}) where T
    companion(T, p)
end
function companion(::Type{S}, p::UnivariatePolynomial) where S
    ismonic(p) || throw(ArgumentError("polynomial is not monic"))
    n = deg(p)
    A = zeros(S, n, n)
    @inbounds for i = 1:n-1
        A[i+1,i] = 1
    end
    b = p.first
    @inbounds for i = 1:length(p.coeff)-1
        A[i+b, n] = -p.coeff[i]
    end
    A
end

function companion(p::UnivariatePolynomial{S}, q::UnivariatePolynomial{T}) where {S,T}
    R = promote_type(S, T)
    n = deg(p)
    A = zeros(R, n, n)
    if deg(q) >= n
        q = mod(q, p)
    end
    f = q.first
    for k in axes(q.coeff, 1)
        A[k+f, 1] = q.coeff[k]
    end
    for j = 2:n
        aa = A[n, j-1]
        for i = 2:n
            A[i, j] = A[i-1, j-1]
        end
        if !iszero(aa)
            for i = 1:n
                A[i, j] -= p[i-1] * aa
            end
        end
    end
    A
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

function Base.iterate(x::IterTerms{P}, st = typemin(Int)) where P<:UnivariatePolynomial
    p = x.p
    st = max(st, ord(p))
    d = deg(p)
    while st <= d && iszero(p[st])
        st += 1
    end
    st <= d ? (p[st] * monom(P, st), st + 1) : nothing
end

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
