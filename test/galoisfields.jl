
using Random
using LinearAlgebra

import CommutativeRings: GFImpl

let rng = MersenneTwister(1), x
mat(p::Integer, n::Integer) = rand(rng, 0:p-1, n, n)

@testset "Galois Fields Implementation" begin
    
    @test GFImpl(7) <: ZZmod{7}
    @test GFImpl(3) == GFImpl(3,1)
    @test GFImpl(5,3) <: Quotient{<:UnivariatePolynomial{<:ZZmod{5},:γ}}
    
    G7 = GFImpl(7)
    @test G7(3)^2 == G7(2)

    G53 = GFImpl(5,3)
    @test isone(inv(G53([1,0,1])) * G53([1,0,1]))
   
    x = monom(basetype(G53), 1)
    ma53(p, n, k) = Matrix{G53}(mat(p, n) .* x^k)
    A = ma53(4, 3, 0) + ma53(4, 3, 1) + ma53(4, 3, 2)
    @test inv(A) * A == I

    @test sprint(show, GFImpl(5,3)([1,2,3])) == "{3:2:1%5}"
end

@testset "Galois Fields" begin
    @test_throws ArgumentError GF(1)
    @test_throws ArgumentError GF(12)
    @test GF(32) == GF(2, 5)
    @test GF(625) == GF(5, 4)
end

@testset "Galois Fields $p^$r" for (p, r) in ((2,8), (7,2))
    @test GF(p) == GF(p,1)
    @test GF(p, r) <: GaloisField{p^r}
    G = GF(p, r)
    @test basetype(G) <: Quotient{<:UnivariatePolynomial{<:ZZmod{p},:γ}}
    Q = basetype(G)
    @test modulus(G) == modulus(Q)
    @test order(G) == order(Q) == p ^ r
    @test characteristic(G) == characteristic(Q) == p
    @test dimension(G) == r

    g1, g2 = rand(rng, G, 2)
    while iszero(g1)
        g1 = rand(rng, G)
    end
    @test convert(G, convert(Q, g1)) == g1
    q1, q2 = Quotient.((g1, g2))
    @test G(1) == Q(1)
    @test G(p) != Q(p)
    @test q1 == Q(g1)
    @test g1 == G(q1)
    @test g1 == q1

    @test g1 * g2 == q1 * q2
    @test g1^17 == q1^17
    @test g1^-17 == q1^-17
    @test g1 + g2 == q1 + q2
    @test g1 - g2 == q1 - q2
    @test -g1 == -q1
    @test inv(g1) == inv(q1)

    @test iszero(G(0))
    @test isone(G(1))
    @test isunit(G(2))
    @test zero(G) == 0
    @test one(G) == 1
    @test G(10) / G(10) == 1
    @test one(G) * g1 == g1
    @test zero(G) * g1 == 0
    @test g1 * 1 == g1
    @test 1 * g2 == g2
    @test 2g1 == g1 + g1
    @test g2 ^ 2 == g2 * g2
    @test_throws ArgumentError inv(G(0))
    @test_throws ArgumentError G(0) ^ -2

    @test sprint(show, g1) == sprint(show, q1)

    @test G(one(ZZ/p)) === one(G)
    @test length(modulus(G).(G)) == length(G)
end

@testset "Galois Field Implementation - Homomorphisms" begin

    Z1 = GFImpl(5, 2)
    Z2 = GFImpl(5, 6)
    z1 = Z1(monom(basetype(Z1)))
    iso = isomorphism(Z1, Z2)
    z2 = iso(z1)
    @test z1 != z2
    @test iso(z1) == z2
    @test z1 + 1 == z1 + Z1(1)
    @test iso(Z1(0)) == Z2(0)
    @test iso(Z1(1)) == Z2(1)
    @test iso(z1^17 + 2z1^12 + 1) == z2^17 + 2z2^12 + 1

end

@testset "Galois field - irreducibles GF{$q,$r} ^ $s" for (q, r, s) in ((2, 3, 3), (3, 2, 3))
    G = GF(q, r)
    irr = irreducibles(G[:x], s)
    @test length(collect(irr)) == necklace(order(G), s)
end

end
