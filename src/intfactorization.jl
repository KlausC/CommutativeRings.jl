
function factor(p::P) where P<:UnivariatePolynomial{<:ZZ}
    c = content(p)
    q = primpart(p)
    r = yun(q)
    s = zassenhaus(r)
    isone(c) ? s : [P(c) => 1; s]
end

function yun(p)
    p
end

function zassenhaus(p)
    [p => 1]
end

"""
    coeffbounds(u::Polygon, m)::Vector{<:Integer}

Assuming `u` is a univariate polygon with integer coefficients and `LC(u) != 0 != u(0)`.
If `u` has a factor polynom `v` with integer coefficients `v(x) = v[m+1] * x^m + ... + v[1]`,
calculate bounds `b[i]` with `abs(v[i]) <= b[i] for i = 1:m+1`.
Algorithm see TAoCP 2.Ed 4.6.2 Exercise 20.
"""
function coeffbounds(u::UnivariatePolynomial{ZZ{T},X}, m::Integer) where {T<:Integer,X}
    I = widen(T)
    n = deg(u)
    0 <= m <= n || throw(ArgumentError("required m ∈ [0,deg(u)] but $m ∉ [0,$n]"))
    un = abs(value(LC(u)))
    u0 = abs(value(u.coeff[1]))
    iszero(u0) && throw(ArgumentError("required u(0) != 0"))
    ua = Integer(ceil(norm(value.(u.coeff))))
    v = zeros(I, m+1)
    if m > 0
        v[m+1], v[1] = un, u0
    else
        v[1] = min(u0, un) # abs(content(u)) would be possible but not worth the effort
    end
    bk = I(1)
    for j = m-1:-1:1
        bj = bk
        bk = bk * j ÷ (m - j)
        v[j+1] = min(bj * ua + bk * un, bk * ua + bj * u0)
    end
    v
end

"""
    hensel_lift()

Algorithm see TAoCP 2.Ed 4.6.2 Exercise 22.
"""
function _hensel_lift(u::P, v::P1, w::P1, a::P1, b::P1, p::Integer, q::Integer, r::Integer, c::Integer) where {P<:Polynomial,P1<:Polynomial}
#= The following assumptions are made, but not verified here:
    r = gcd(p, q) - p and q need not be prime!
    u == v * w (modulo q)
    a * v + b * w == 1 (modulo p) with deg(a) < deg(w) and deg(b) < deg(v)
    c * LC(v) == 1 (modulo r)
    deg(u) == deg(v) + deg(w)

    The algorithm constructs polynomials V == v (modulo q) and W == w (modulo q)
    such that u == V * W ( modulo q*r) and
    LC(V) == LC(v) and LC(W) == lc(w) and deg(V) == deg(v) and deg(W) == deg(w)

    If r is prime, the results are unique modulo q*r.
=#
    X = varnames(P)[1]
    Pqr = (ZZ/(q*r))[X]
    Pr = (ZZ/r)[X]
    u, v, w, a, b = convert.(Pqr, (u, v, w, a, b))
    f = convertmod(Pqr, u - v * w, ÷, q)
    t, vv = divrem(f * b, v)
    V = convertmod(Pqr, vv, %, r)
    W = convertmod(Pqr, f * a + t * w, %, r)
    V * q + v, W * q + w
end

function convertmod(::Type{P}, u::UnivariatePolynomial, op, q::Integer) where P<:UnivariatePolynomial
    P(op.(value.(u.coeff), q))
end

function convertmod(::Type{P}, u::Q) where {P,Q}
    m = modulus(basetype(P))
    n = modulus(basetype(Q))
    convertmod(P, u, %, div(n, m))
end



