
@testset "construction of quotient ring" begin
    S = ZZ{BigInt}
    P = UnivariatePolynomial{:x,S}
    x = P([0, 1])
    ideal = x^2 + 1

    @test P / ideal != nothing
    Pi = P / ideal
    p = Pi(4x + 5)
    @test p + p == Pi(8x + 10)
    @test 3p == Pi(12x + 15)
    pp = (4im + 5)^10
    @test p^10 == Pi(P([pp.re, pp.im])) 

end

