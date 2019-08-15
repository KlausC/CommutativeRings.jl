
@testset "construction of quotient ring" begin
    S = ZZ{BigInt}
    P = UnivariatePolynomial{:x,S}
    x = P([0, 1])
    ideal = x^2 + 1
    Q = P / ideal

    Qp = new_class(Quotient{:p,P}, x^3+1)

    @test basetype(Q) == P
    @test depth(Q) == 3
    @test P / ideal != nothing
    p = 4x + 5
    @test Quotient{:p}(p) == p
    @test Quotient{:p,P}(1) == 1
    @test Quotient{:p,P}(ZZ(1)) == 1
    q = Q(p)
    @test q + q == Q(8x + 10)
    @test 3q == Q(12x + 15)
    pp = (4im + 5)^10
    @test q^10 == Q(P([pp.re, pp.im])) 


    io = IOBuffer()
    show(io, q)
    @test String(take!(io)) isa String

end

