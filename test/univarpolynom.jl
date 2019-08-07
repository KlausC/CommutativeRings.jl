
using CommutativeRings
using Test
using Polynomials

const S = ZZ{Int}
const P = UnivariatePolynomial{:x,S}

CP = (Int[], Int[1], Int[2], Int[2, 1], Int[1,0,30])

import Base: ==
function ==(a::UnivariatePolynomial, b::Poly)
    va = getproperty.(a.coeff, :val)
    vb = b.a
    n = length(vb)
    while n > 0 && vb[n] == 0
        n -= 1
    end
    va == vb[1:n]
end

@testset "constructors" begin
    @test P([S(0), S(1)]).coeff[2] == S(1)
    @test P([1]).coeff[1] == S(1)
    @test length(P(Int[]).coeff) == 0
    @test length(P(Int[0]).coeff) == 0
    @test eltype(UnivariatePolynomial{:x}(S[]).coeff) == S

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

    @test P([1,2,3]) == P([1,2,3])
    @test P([1,2]) != P([1])
    @test UnivariatePolynomial{:X,S}([1]) != P([1])
    @test hash(UnivariatePolynomial{:X,S}([1])) != hash(P([1]))
end

@testset "operation $cp $(string(op)) $cq" for op in (+, -, *), cp in CP, cq in CP
    p = P(S.(cp))
    q = P(S.(cq))
    @test op(p, q) == op(Poly(cp), Poly(cq)) 
end
@testset "operation unary - and ^ $cp" for cp in CP
    p = P(S.(cp))
    @test -p == -Poly(cp) 
    @test p^10 == Poly(cp)^10 
    @test p^0 == one(P)
    !isunit(p) && @test_throws DomainError p^-1
    @test zero(p)^0 == one(P)
    @test one(p)^-1 == one(P)
    @test zero(p)^0 == one(P)
end

hasunitlead(p::UnivariatePolynomial) = !iszero(p) && isunit(p.coeff[end])

@testset "operation divrem($cp,$cq)" for cp in CP, cq in CP
    p = P(S.(cp))
    q = P(S.(cq))
    if hasunitlead(q) || deg(p) < deg(q) || ( p == q && !iszero(p))
        @test divrem(p, q) == divrem(Poly(cp), Poly(cq)) 
    else
        @test_throws DomainError divrem(p, q)
    end
end

@testset "gcd calculations" begin

    P = UnivariatePolynomial{:x,ZZ{Int}}
    @test P([0, 1]) != nothing
    x = P([0,1])
    @test deg(x + 2x^2 + 1 +0*x^3) == 2
    p = x^8 + x^6 -3x^4 - 3x^3 + 8x^2 +2x - 5
    q = 3x^6 + 5x^4 - 4*x^2 -9x + 21
    @test deg(pgcd(p, q)) == 0
    r1 = pgcd(p, q)
    s = (x^2 + 3x + 1)^5
    @test pgcd(p * s, q * s) / r1 == s

    p = P([1, 2, 1])
    q = P([1, 1])
    @test gcd(p, q) == q
    @test gcd([p, p, q]) == q
    @test gcdx(p, q) == (q, P(Int[]), P([1]))
    @test lcm(p, q) == p
    @test lcm([p, q, p]) == p

    @test UnivariatePolynomial{:x,ZZ{Int}}(p) === p
    @test UnivariatePolynomial{:x,ZZ{Int32}}(p) != p
    @test div(p, q) == q
    @test content(p) == ZZ(1)
    @test primpart(p) == p

    @test iszero(lc(zero(P)))
    @test isone(lc(one(P)))

    PP = UnivariatePolynomial{:z,P}
    pp = PP([p, q, s])

    # call show
    io = IOBuffer()
    @test show(io, p) == nothing
    @test show(io, zero(P)) == nothing
    @test show(io, one(P)) == nothing
    @test show(io, pp) == nothing
end

@testset "pseudo gcd" begin
    S = ZZ{BigInt}
    P = UnivariatePolynomial{:x,S}
    p = P([1, 4, 5, 1, 6, 0, 3])
    q = P([5, 1, 1, 3])
    x = P([0, 1])
    @test content(2p) == S(2)
    @test primpart(12p) == p
    @test lc(p) == S(3)
    a, b, f = pdivrem(p, q)
    @test f * p == a * q + b
    @test_throws DomainError gcd(p, q)
    @test pgcd(p, q) == P([-225750])
    @test_throws DomainError gcdx(p, q)
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    @test deg(g) == 0
    p = 3x^10 - 3x^9 - 3x^8 + 3x^7 - 2x^5 - 3x^4 - 2x^3 - 1x - 3
    q = 2x^4 + 3x^3 - 1x^2 + x - 2
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    @test deg(g) == 0
    s = 3x^3 - 2x^2 - 1
    p *= s
    q *= s
    g, u, v, f = pgcdx(p, q)
    @test iszero(p * u + q * v - g * f)
    @test isdiv(g, s)
end

@testset "polynomials of other structures" begin

    Zp = ZZmod{17, Int8}
    P = UnivariatePolynomial{:x, Zp}
    x = P([0, 1])
    p = (3x^2 + 2x + 1) * (x - 1)
    q = x^2 - x
    @test p / (x-1) == (3x^2 + 2x + 1)
    @test gcd(p, q) == x - 1
end

