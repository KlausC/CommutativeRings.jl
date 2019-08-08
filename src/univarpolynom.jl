
### Constructors
basetype(::Type{<:UnivariatePolynomial{m,T}}) where {m,T} = T

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
# convert polynomial with different symbol / coefficient type
function UnivariatePolynomial{X,S}(p::UnivariatePolynomial) where {X,S}
    UnivariatePolynomial{X,S}(S.(p.coeff), NOCHECK)
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

# canonical embedding homomorphism from base ring
UnivariatePolynomial{X}(r::R) where {X,R<:Ring} = UnivariatePolynomial{X,R}([r])

# make new copy
copy(p::UnivariatePolynomial) = typeof(p)(copy(p.coeff))

# convenience type constructor:
# enable `R[:X]` as short for `UnivariatePolynomial{:X,R}`
getindex(R::Type{<:Ring}, s::Symbol) = UnivariatePolynomial{s,R}


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
+(p::T, q::Ring) where {X,S,T<:UnivariatePolynomial{X,S}} = p + T([S(q)])
+(p::T, q::Integer) where {X,S,T<:UnivariatePolynomial{X,S}} = p + T([S(q)])
+(q::Union{Integer,S}, p::T) where {X,S,T<:UnivariatePolynomial{X,S}} = +(p, q)

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
-(q::Union{Integer,S}, p::T) where {X,S,T<:UnivariatePolynomial{X,S}} = +(-p, q)

function *(p::T, q::T) where T<:UnivariatePolynomial
    vp = p.coeff
    vq = q.coeff
    np = length(p.coeff)
    nq = length(q.coeff)
    np <= nq || return *(q, p)
    nv = np + nq - 1
    if np == 0 || nq == 0
        return zero(T)
    elseif ismonomial(p)
        v = multmono(p, np, vp, q, nq, vq)
    elseif ismonomial(q)
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

function smul!(v::Vector{S}, r, m::S) where S
    for i in r
        v[i] *= m
    end
    v
end
function sdiv!(v::Vector{S}, r, m::S) where S
    for i in r
        v[i] /= m
    end
    v
end

# division and remainder algorithm
# if the third argument is true, perform `pseudo-division` by multiplying
# the divident by Ring element in order to allow division.
# In the other case, throw error, if division by the leading coefficient fails.
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
    if nq == 1
        isone(divi) && return vp, S[], f
        vf = copy(vp)
        if fac
            f = divi / gcd(divi, gcd(vp))
            !isone(f) && smul!(vf, 1:np, f)
        end
        sdiv!(vf, 1:np, divi)
        vr = S[]
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
            end
            multi = vri / divi
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
    vf, vr, f
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

function rem(p::T, q::T) where T<:UnivariatePolynomial
    cp = p.coeff; cq = q.coeff
    r = divrem(cp, cq, Val(false))[2]
    tweak(r, cp, p)
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
hash(p::UnivariatePolynomial{X}, h::UInt) where X = hash(X, hash(p.coeff, h))
ismonomial(p::UnivariatePolynomial) = all(iszero.(view(p.coeff, 1:deg(p))))
ismonic(p::UnivariatePolynomial) = isone(lc(p))

# auxiliary functions

"""
    lc(p::UnivariatePolynomial)

Return the leading coefficient of a non-zero polynomial. This coefficient
cannot be zero.
"""
lc(p::UnivariatePolynomial{X,S}) where {X,S} = deg(p) < 0 ? zero(S) : p.coeff[end]

# pseudo-division to calculate gcd of polynomial using subresultant pseudo-remainders.

"""
    pgcd(a, b)

Modification of Euclid's algorithm to produce `subresultant sequence of pseudo-remainders`.
The next to last calculated remainder is a scalar multiple of the gcd. 
See: `https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Subresultant_pseudo-remainder_sequence`
"""
function pgcd(a::T, b::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    
    iszero(b) && return a
    E = -one(S)
    da = deg(a)
    db = deg(b)
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
        db = deg(c)
        ψ = (-γ)^d / ψ^(d-1)
        d = da - db
        β = -γ * ψ^d
    end
    a
end
"""
    g, u, v = pgcdx(a, b)

Extended pseudo GCD algorithm.
Return `g == pgcd(a, b)` and `u, v` with `p * u + q * v == g`.
"""
function pgcdx(a::T, b::T) where {X,S,T<:UnivariatePolynomial{X,S}}
    iszero(b) && return a
    E = one(S)
    da = deg(a)
    db = deg(b)
    d = da - db
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
        ψ = (-γ)^d / ψ^(d-1)
        d = da - db
        β = -γ * ψ^d
    end
    cs = gcd(content(s2), content(t2))
    a = a / cs
    f = content(a)
    a/f, s2/cs, t2/cs, f
end

function multmono(p, np, vp, q, nq, vq)
    fact = lc(p)
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

issimple(::Union{ZZ,ZZmod,Number}) = true
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
        bra && n != N && print(io, " + ")
        if !iszero(el)
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
