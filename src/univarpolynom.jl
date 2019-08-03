
# constructors
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
UnivariatePolynomial{X}(v::Vector{S}) where {X,S} = UnivariatePolynomial{X,S}(v)
UnivariatePolynomial{X,S}(p::UnivariatePolynomial{X,S}) where {X,S} = p
function UnivariatePolynomial{X,S}(p::UnivariatePolynomial) where {X,S}
    UnivariatePolynomial{X,S}(S.(p.coeff))
end
"""
    UnivariatePolynomials{X,S}(vector)

Construct a new polynomial Ring-element.
Allow all coefficient classes, which can be mapped to S, that means
the canonical homomorphism is used.
"""
function UnivariatePolynomial{X,S}(v::AbstractVector) where {X,S}
    UnivariatePolynomial{X,S}(S.(v))
end

copy(p::UnivariatePolynomial) = typeof(p)(copy(p.coeff))

# arithmetic
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
function +(p::T, q::Union{Integer,S}) where {X,S,T<:UnivariatePolynomial{X,S}}
    p + T([S(q)])
end
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
-(p::T, q::Union{Integer,S}) where {X,S,T<:UnivariatePolynomial{X,S}} = +(p, -q)

function *(p::T, q::T) where T<:UnivariatePolynomial
    vp = p.coeff
    vq = q.coeff
    np = length(p.coeff)
    nq = length(q.coeff)
    np <= nq || return *(q, p)
    nv = np + nq - 1
    if np == 0 || nq == 0
        return zero(T)
    elseif np == 1
        divi = vp[1]
        if isone(divi)
            return q
        end
        v = copy(vq)
        for i = 1:nq
            v[i] *= divi
        end
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
    T(v, NOCHECK)
end

function *(p::T, q::Union{Integer,S}) where {X,S,T<:UnivariatePolynomial{X,S}}
    if iszero(q)
        zero(T)
    else
        # make broadcast recognize q as scalar
        T(p.coeff .* Ref(S(q)), NOCHECK)
    end
end
*(q::Union{Integer,Ring}, p::UnivariatePolynomial) = *(p, q)

function /(p::T, q::S) where {X,S,T<:UnivariatePolynomial{X,S}}
    T(p.coeff ./ Ref(q), NOCHECK)
end

# division and remainder algorithm
function divrem(vp::Vector{S}, vq::Vector{S}) where S<:Ring
    np = length(vp)
    nq = length(vq)
    nq > 0 || throw(DomainError(vq, "Cannot divide by zero polynomial."))
    lead = vq[nq]
    if np < nq
        return S[], vp
    end
    divi = lead
    if nq == 1
        if isone(divi)
            return vp, S[]
        end
        vf = vp ./ Ref(divi)
        vr = S[]
    else
        vf = similar(vp, np - nq + 1)
        vr = copy(vp)
        for i = np:-1:nq
            multi = vr[i] / divi
            for j = 1:nq-1
                vr[j+i-nq] -= vq[j] * multi
            end
            vf[i-nq+1] = multi
        end
        n = nq - 1
        while n > 0 && iszero(vr[n])
            n -= 1
        end
        resize!(vr, n)
    end
    vf, vr
end

function divrem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    d, r = divrem(cp, cq)
    tweak(d, cp, p), tweak(r, cp, p)
end

function tweak(d, cp, p::T) where T<:UnivariatePolynomial
    d === cp ? p : T(d, NOCHECK)
end

function div(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    r = divrem(cp, cq)[1]
    tweak(d, cp, p)
end

function rem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    r = divrem(cp, cq)[2]
    tweak(r, cp, p)
end

"""
    content(p::UnivariatePolynomial)

Return the degree of the polynimial p, i.e. the `gcd` of its coefficients.
"""
content(p::UnivariatePolynomial) = gcd(p.coeff)

"""
    primpart(p::UnivariatePolynomial)

The primitive part of the polynomial p, that means the `gcd` of its coefficients is `1`,
"""
primpart(p::UnivariatePolynomial) = div(p, primpart(p))

"""
    degree(p::UnivariatePolynomial)

Return the degree of the polynomial p, i.e. the highest exponent in the polynomial that has a
nonzero coefficient. The degree of the zero polynomial is defined to be -1.
"""
degree(p::UnivariatePolynomial) = length(p.coeff) - 1

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
hash(p::UnivariatePolynomial{X}, h::UInt) where X = hash(X, hash(p.coeff, h))

# auxiliary functions

"""
    lc(p::UnivariatePolynomial)

Return the leading coefficient of a non-zero polynomial. This coefficient
cannot be zero.
"""
lc(p::UnivariatePolynomial) = p.coeff[end]

# pseudo-division to calculate gcd of polynomial using subresultant pseudo-remainders.

"""
    pgcd(a, b)

Modification of Euclid's algorithm to produce `subresultant sequence of pseudo-remainders`.
The next to last calculated remainder is a scalar multiple of the gcd. 
See: https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Euclidean_division
"""
function pgcd(a::T, b::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    
    iszero(b) && return a
    E = -one(S)
    da = degree(a)
    db = degree(b)
    d = da - db
    ψ = E
    β = iseven(d) ? -E : E
    while true
        γ = lc(b)
        a = a * γ^(d+1)
        c = rem(a, b) / β
        a, b = b, c
        iszero(b) && break
        # prepare for next turn
        da = db
        db = degree(c)
        ψ = (-γ)^d / ψ^(d-1)
        d = da - db
        β = -γ * ψ^d
    end
    a
end

function Base.show(io::IO, p::UnivariatePolynomial)
    show(io, getfield.(p.coeff, :val))
end