
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
deg = CommutativeRings.degree

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

end
