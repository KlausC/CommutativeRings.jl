
using Random
using LinearAlgebra

import CommutativeRings: GFImpl

let rng = MersenneTwister(1), x
mat(p::Integer, n::Integer) = rand(rng, 0:p-1, n, n)

@testset "Galois Fields Implementation" begin
    
    @test GFImpl(7) <: ZZmod{7}
    @test GFImpl(3) == GFImpl(3,1)
    @test GFImpl(5,3) <: Quotient{X,<:UnivariatePolynomial{:γ,<:ZZmod{5}}} where X
    
    G7 = GFImpl(7)
    @test G7(3)^2 == G7(2)

    G53 = GFImpl(5,3)
    @test inv(G53([1,0,1])) * G53([1,0,1]) == 1
   
    x = monom(basetype(G53), 1)
    ma53(p, n, k) = Matrix{G53}(mat(p, n) .* x^k)
    A = ma53(4, 3, 0) + ma53(4, 3, 1) + ma53(4, 3, 2)
    @test inv(A) * A == I

    io = IOBuffer()
    show(io, GFImpl(5,3)([1,2,3]))
    s = String(take!(io))
    @test s == "{3:2:1%5}"
end

@testset "Galois Fields $p^$r" for (p, r) in ((2,10), (7,2))
    
    @test GF(p) == GF(p,1)
    @test GF(p, r) <: GaloisField{p^r}
    G = GF(p, r)
    @test basetype(G) <: Quotient{X,<:UnivariatePolynomial{:γ,<:ZZmod{p}}} where X
    Q = basetype(G)
    @test modulus(G) == modulus(Q)
    @test order(G) == order(Q)
    @test characteristic(G) == characteristic(Q)
    @test dimension(G) == r

    g1, g2 = rand(G, 2)
    @test convert(G, convert(Q, g1)) == g1
    q1, q2 = convert.(Q, (g1, g2))
    @test g1 * g2 == convert(G, q1 * q2)
    @test g1^17 == convert(G, q1^17)
    @test g1^-17 == convert(G, q1^-17)
    @test g1 + g2 == convert(G, q1 + q2)
    @test g1 - g2 == convert(G, q1 - q2)
    @test -g1 == convert(G, -q1)
    @test inv(g1) == convert(G, inv(q1))
end

end
