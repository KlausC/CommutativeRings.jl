module UnivarTest

using CommutativeRings
using Test
using Polynomials

import CommutativeRings: shiftleft, ismonic, multiply

if !isdefined(Polynomials, :Poly)
    Poly = Polynomials.Polynomial
end

import Base: ==
function ==(a::UnivariatePolynomial, b::Poly)
    va = value.(a[:])
    vb = coeffs(b)
    n = length(vb)
    while n > 0 && vb[n] == 0
        n -= 1
    end
    va == vb[1:n]
end

S = ZZ{Int}
P = UnivariatePolynomial{S,:x}
PQ = UnivariatePolynomial{QQ{Int},:x}

x = P([0, 1])
CP = (Int[], [1], [0, 0, 4], [2, 1], [1, 0, 30])

@testset "constructors" begin
    @test P == S[:x]
    @test_throws DomainError S[:y](x)
    @test basetype(P) == S
    @test depth(P) == 2
    @test P([S(0), S(1)]).coeff[1] == S(1)
    @test ord(P([S(0), S(1)])) == 1
    @test P([1]).coeff[1] == S(1)
    @test length(P(Int[]).coeff) == 0
    @test length(P(Int[0]).coeff) == 0
    @test eltype(UnivariatePolynomial(:x, S[]).coeff) == S
    @test iscoprime(x^2 + 1, x + 1)
    @test !iscoprime(4x^2 + 4x + 1, 2x + 1)

    @test typeof(UnivariatePolynomial(:x, ZZ(1))) == P
    co = [1, 2, 3]
    @test copy(P(co)) == P(co)
    @test copy(P(co)).coeff !== P(co).coeff
    @test P(co) == P(co, big(0))
    @test P(co, 1) == P([0; co])

    @test isunit(P([-1]))
    @test isunit(P([1]))
    @test !isunit(P([0]))
    @test length(zero(P).coeff) == 0
    z = zero(P)
    o = one(P)
    @test length(o.coeff) == 1 && o.coeff[1] == S(1)
    @test iszero(z)
    @test !iszero(o)
    @test isone(o)
    @test !isone(z)

    @test P([1, 2, 3]) == P([1, 2, 3])
    @test P([1, 2]) != P([1])

    @test P(1) == 1
    @test P(ZZ(Int8(1))) == 1
    @test 1 + P(1) == P(2)
    @test ZZ(1) + P(1) == P(2)
    @test ZZ(1) - P(1) == z
    @test P(1) == UnivariatePolynomial{ZZ{Int8},:y}(1)
    @test P([0, 1]) != UnivariatePolynomial{ZZ{Int},:y}([0, 1])
    @test P(1) == UnivariatePolynomial{ZZ{Int},:x}(1)
    @test UnivariatePolynomial{ZZ{Int8},:x}([1]) == P([1])
    @test UnivariatePolynomial(ZZ(1)) == 1
    @test hash(UnivariatePolynomial{ZZ{Int8},:x}([1])) == hash(P([1]))
    @test P(co, 0) != P(co, 1)
    @test S[:y](co) != P(co)
    @test one(S[:y]) == one(P)
end

@testset "coefficient accessors" begin
    p = x^3 + 2x - 2
    @test (p[0], p[1], p[2], p[3]) == (-2, 2, 0, 1)
    @test (x * p)[:] == [0, -2, 2, 0, 1]
    @test p[0] isa basetype(x) <: Ring
    @test value.(p[0]) isa Integer
end

@testset "varnames and generators" for P in (S[:x],)
    x = monom(P)
    @test [x] == generators(P)
    @test varnames(P) == [:x]
    @test varnames(P(0)) == [:x]

    p = P(S[1, 2, 3])
    @test deg(p) == 2
    @test multideg(p) == [2]
    @test LC(p) == S(3)
    @test LM(p) == x^2
    @test LT(p) == 3 * x^2

    @test P([1], -1) * x == 1
end

@testset "promotion of types" begin
    @test promote_type(P, PQ) == PQ
    @test promote_type(P, ZZ{Int}) == P
    @test promote_type(P, Int) == P
    @test promote_type(P, Rational{Int8}) == UnivariatePolynomial{QQ{Int},:x}
    @test promote_rule(P, UnivariatePolynomial{S,:y}) == Base.Bottom
end

@testset "operation $cp $(string(op)) $cq" for op in (+, -, *), cp in CP, cq in CP
    p = P(S.(cp))
    q = P(S.(cq))
    @test op(p, q) == op(Poly(cp), Poly(cq))
end

@testset "multiply stripped" begin
    x = monom(ZZ{Int}[:x])
    @test multiply(x^2, x^2 + 1, 2) == x^2
    @test multiply(x^2 + 1, x^2, 2) == x^2
    @test multiply(x, x^2 + 1, 3) == x^3 + x
    @test multiply(x^2 + 1, x, 3) == x^3 + x
end

@testset "derivation" begin
    x = monom(ZZ{Int}[:x])
    p = x^20 + 3x + 5
    @test derive(p) == 20x^19 + 3
    @test derive(p, 2) == 380x^18
    @test p' == derive(p)
    @test p'' == derive(p')
end

@testset "operation unary - and ^ $cp" for cp in CP
    p = P(S.(cp))
    @test -p == -Poly(cp)
    @test p^10 == Poly(cp)^10
    @test p^0 == one(P)
    !isunit(p) && @test_throws DomainError p^-2
    @test zero(p)^0 == one(P)
    @test one(p)^-1 == one(P)
    @test zero(p)^0 == one(P)
    deg(p) > 0 && @test_throws DomainError p^-1
    deg(p) > 0 && @test p != one(ZZ{Int}[:y])
end

hasunitlead(p::UnivariatePolynomial) = isunit(LC(p))

@testset "operation divrem($cp,$cq)" for cp in CP, cq in CP
    p = P(S.(cp))
    q = P(S.(cq))
    if hasunitlead(q) || deg(p) < deg(q) || (p == q && !iszero(q))
        @test divrem(p, q) == divrem(Poly(cp), Poly(cq))
        @test deg(rem(p, q)) < deg(q)
    elseif !iszero(q)
        @test deg(rem(p, q)) >= deg(q)
    else
        @test_throws DomainError divrem(p, q)
    end
end

@testset "gcd calculations" begin

    P = UnivariatePolynomial{ZZ{Int},:x}
    @test P([0, 1]) == monom(P)
    x = P([0, 1])
    @test deg(x + 2x^2 + 1 + 0 * x^3) == 2
    p = x^8 + x^6 - 3x^4 - 3x^3 + 8x^2 + 2x - 5
    q = 21 + 3x^6 + 5x^4 - 4 * x^2 - 9x
    @test deg(pgcd(p, q)) == 0
    r1 = pgcd(p, q)
    s = (ZZ(1) + 3x + x^2)^5
    @test pgcd(p * s, q * s) / r1 == s

    p = P([1, 2, 1])
    q = P([1, 1])
    @test gcd(p, q) == q
    @test gcd([p, p, q]) == q
    @test gcdx(p, q) == (q, P(Int[]), P([1]))
    @test lcm(p, q) == p
    @test lcm([p, q, p]) == p

    @test UnivariatePolynomial{ZZ{Int},:x}(p) === p
    @test UnivariatePolynomial{ZZ{Int32},:x}(p) == p
    @test div(p, q) == q
    @test content(p) == ZZ(1)
    @test primpart(p) == p
    @test content(-p) == ZZ(-1)
    @test primpart(-p) == p

    Q = UnivariatePolynomial{QQ{Int},:x}
    qp = Q(-p) / 12
    @test primpart(qp) == Q(p)
    @test content(qp) == -1 // 12
    @test content(qp) isa QQ
    @test primpart(qp) isa P

    @test iszero(LC(zero(P)))
    @test isone(LC(one(P)))
    @test LC(p) == 1
    @test multideg(one(P)) == [0]
    @test multideg(p) == [2]

    PP = UnivariatePolynomial{P,:z}
    pp = PP([p, q, s])

    # call show
    @test sprint(show, p) !== nothing
    @test sprint(show, zero(P)) !== nothing
    @test sprint(show, one(P)) !== nothing
    @test sprint(show, x^3 + x) !== nothing
end

@testset "pseudo gcd" begin
    S = ZZ{BigInt}
    P = UnivariatePolynomial{S,:x}
    x = monom(P)
    p = 1 + 4x + 5x^2 + x^3 + 6x^4 + 3x^6
    q = 5 + x + x^2 + 3x^3
    @test content(2p) == S(2)
    @test primpart(12p) == p
    @test LC(p) == S(3)
    a, b, f = pdivrem(p, q)
    @test f * p == a * q + b
    a, b, f = pdivrem(p, P([2]))
    @test f * p == a * P([2]) + b

    @test gcd(p, q) == one(P)
    @test pgcd(p, q) == P([1])
    @test_throws DomainError gcdx(p, q)
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    @test deg(g) == 0
    p = 3x^10 - 3x^9 - 3x^8 + 3x^7 - 2x^5 - 3x^4 - 2x^3 - 1x - 3
    q = 2x^4 + 3x^3 - 1x^2 + x - 2
    g, u, v, f = pgcdx(q, p)
    @test iszero(q * u + p * v - g * f)
    @test deg(g) == 0
    s = 3x^3 - 2x^2 - ZZ(1)
    p *= s
    q *= s
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    @test isdiv(g, s)

    S = ZZmod{31,Int}
    P = UnivariatePolynomial{S,:x}
    x = monom(P)
    p = x^3 + 3x^2 - 4
    q = 4 - (-x)
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    p2 = 2p
    @test p2 / 2 == p

    p = 12x^2 + 45x + 60
    q = 5x^2 + 1
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)

    qq = [q, 2 + x]
    a, r = divremv(p, qq)
    @test sum(a .* qq) + r == p

    x = monom(UnivariatePolynomial{ZZ{Int},:x})
    @test CommutativeRings.invert(x, x^2 + 1) == -x
    @test_throws DomainError CommutativeRings.invert(x + 1, x^2 + 1)

    @test CommutativeRings.issimple(1.0)
    @test CommutativeRings.issimple(x^3)
    @test !CommutativeRings.issimple(x + 1)
end

@testset "polynomials of other structures" begin

    Zp = ZZmod{17,Int8}
    P = Zp[:x]
    @test P([1, 2]) != Zp[:y]([1, 2])
    x = P([0, 1])
    p = (3x^2 + 2x + 1) * (x - 1)
    q = x^2 - x
    @test p / (x - 1) == (3x^2 + 2x + 1)
    @test gcd(p, q) == x - 1

    @test ismonom(P([0, 2]))
    @test !ismonom(P([1, 2]))
    @test ismonic(P([2, 1]))
    @test !ismonic(P([2, -1]))

end

@testset "apply polynomial" begin
    x = monom(ZZ{Int}[:x], 1)
    y = monom(ZZ{Int}[:y], 1)
    @test x(1) == 1
    @test x(0) == 0
    @test (y^2)(x + 1) == x^2 + 2x + 1
    @test (0 * y)(x^2) == 0
end

@testset "abstract types" begin
    @test QQ[:x]([1 // 2, 2 // 3]) == QQ{Int}[:x]([1 // 2, 2 // 3])
end

@testset "GF[:x]" begin
    G = GF(7, 3)
    GX = G[:x]
    x = monom(GX)
    p = x^3 + ofindex((7 * 2 + 1) * 7 + 4, G) * x + 1
    r = x + ofindex(28, G)
    q = (x^2 + ofindex(201, G) * x + 1) * r
    @test isirreducible(p)
    @test factor(q) |> length == 3
    @test deg(p^2) == 6
    @test p * q == q * p
    @test p + q - p == q
    @test q / r |> deg == 2
    @test_throws DomainError q / (r + 1)
end

@testset "primpart and content" begin
    x = monom(ZZ{Int}[:x])
    p = 12x^3 + 3x
    @test content(p) == 3
    @test primpart(p) == p / content(p)
    @test content_primpart(p) == (content(p), primpart(p))

    x = monom(QQ{Int}[:x])
    p = 12 // 5 * x^3 + 3x
    @test content(p) == 3 // 5
    @test primpart(p) == p // content(p)
    @test content_primpart(p) == (content(p), primpart(p))
end

@testset "reverse" begin
    x = monom(ZZ{Int}[:x])
    p = 2x^6 - 3x^4
    @test ord(p) == 4
    @test reverse(reverse(p)) == p
    k = ord(p) + deg(p)
    @test reverse(p) == p(1 // x) * x^k
end

@testset "evaluate polynomial of $Z with $T" for Z in (Int, BigInt),
    T in (Float32, BigFloat, ComplexF64)

    P = ZZ{Z}[:x]

    x = monom(P)
    p = x^5 + 2x + 1
    a = T(pi)
    @test p(a) isa promote_type(Z, T)
    @test p(a) ≈ (a^4 + 2) * a + 1
end

@testset "evaluate with zero polynomial and zero matrix" begin
    A = rand(-10:10, 3, 3)
    P = ZZ{Int}[:x]
    x = monom(P)
    p0 = 0 * x
    @test p0(A) == zero(A)
    @test x(zero(A)) isa Matrix{ZZ{Int}}
end

end # module
