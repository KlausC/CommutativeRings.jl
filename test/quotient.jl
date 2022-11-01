
let S = ZZ{BigInt}, P = S[:x], x = P([0, 1])

@testset "construction of quotient ring" begin
    ideal = x^2 + 1
    @test P / ideal <: Quotient{P}
    @test P / (x^3+1) <: Quotient{P}
    Q = P / ideal
    Qp = P / (x^3+1)

    @test basetype(Q) == P
    @test depth(Q) == 3
    @test P / ideal !== nothing
    p = 4x + 5
    @test Qp(p) == p
    @test Qp(1) == 1
    @test Qp(ZZ(1)) == 1
    q = Q(p)
    @test q + q == Q(8x + 10)
    @test q - q == 0
    @test q * q == p * p
    @test 3q == Q(12x + 15)
    pp = (4im + 5)^10
    @test q^10 == Q(P([pp.re, pp.im])) 


    @test !iszero(q)
    @test iszero(zero(Q))
    @test !isone(q)
    @test isone(one(Q))
    @test isunit(Q(x))
    @test !isunit(Q(x+1))
    @test inv(Q(x)) == -Q(x)
    @test Q(x) * 5 == Q(5x)

    @test hash(q) != 0
    @test sprint(show, q) isa String

    @test value(q + 3 * ideal) == p
end

@testset "quotient of polynomial over GF" begin
    G = GF(2, 2)
    GX = G[:x]
    x = monom(GX)
    p = x^3 + 1
    Q = GX / p
    @test order(Q) == order(G)^3
end

@testset "show" begin
    P = ZZ{Int}[:x]
    x = monom(P)
    Q = P / (x^2 + 17)
    @test sprint(show, Q(1)) == "1"
    @test sprint(show, Q(x)) == "\u23b7-17"
    @test sprint(show, Q(-2x + 10)) == "-2*\u23b7-17 + 10"
    @test sprint(show, -Q(2x + 10)) == "-2*\u23b7-17 - 10"
    R = P / (x^3 + 1)
    @test sprint(show, R(x^2 + x + 1)) == "x^2 + x + 1 mod(x^3 + 1)"
end

end
