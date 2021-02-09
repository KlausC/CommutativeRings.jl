
@testset "construction" begin
    P = UnivariatePolynomial{ZZ{Int},:x}
    p = P([1, -2])
    q = P([1, -1])
    pq = Frac(p, q)
    F = Frac{P}
    @test basetype(F) == P
    @test depth(F) == 3
    @test !issimpler(pq, pq)
    @test lcunit(pq) == 1
    @test copy(pq) == pq
    @test F(pq) === pq
    @test Frac(p) == p
    P2 = UnivariatePolynomial{ZZ{Int8},:x}
    pq2 = P2([1, -2]) // P2([1, -1])
    @test F(pq2) == pq
    @test F(13) == F(13, 1)
    @test F(ZZ(11)) == F(ZZ(22), ZZ(2))
    @test basetype(Frac(Int8(11))) == ZZ{Int8}

    @test convert(F, pq) === pq
    @test convert(F, pq2) == pq2
    @test convert(F, p) == p
    @test convert(F, 42) == F(84, 2)
    @test convert(F, 42 // 8) == 21 // 4

    @test Frac(p, q) != nothing
    @test p // q == Frac(p, q)
    @test p // p == 1
    @test pq * pq == F(p * p, P([1, -2, 1]))
    @test pq / pq == 1
    @test isunit(F(-1))
    @test isunit(pq)
    @test isone(one(F))
    @test !isone(pq)
    @test one(F) == F(10, 10)
    @test iszero(zero(F))
    @test !iszero(F(1))
    @test F(1) + P(1) == 2
    @test P(1) + F(1) == 2

    @test sprint(show, F(p)) == "-2*x + 1"
    @test sprint(show, pq) == "(2*x - 1)/(x - 1)"

end

@testset "polynomial over GF(7)" begin
    G = GF(7)
    GX = G[:x]
    x = monom(GX)
    p = (x + 1) ^ 3 + 1
    q =  x + 2
    @test p // q == p / q
    @test p // q^2 == (x^2 + x + 1) // q
end

@testset "polynomial over GF(4)" begin
    G = GF(4)
    GX = G[:x]
    x = monom(GX)
    p = (x + 1) ^ 3 + 1
    q =  x + G[2]
    @test p // q == p / q
    @test p // q^2 == (x^2 + G[3]*x) // q
end
