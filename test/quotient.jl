
@testset "construction of quotient ring" begin
    S = ZZ{BigInt}
    P = S[:x]
    x = P([0, 1])
    ideal = x^2 + 1
    @test P / ideal <: (Quotient{X,P} where X)
    @test P / (x^3+1) <: Quotient{X,P} where X
    Q = P / ideal
    Qp = P / (x^3+1)

    @test basetype(Q) == P
    @test depth(Q) == 3
    @test P / ideal != nothing
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

    io = IOBuffer()
    show(io, q)
    @test String(take!(io)) isa String

end

