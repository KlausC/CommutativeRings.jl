
@testset "cyclotomic" begin
    P = ZZ{Int}[:x]
    @test deg(cyclotomic(P, 385)) == totient(385)
end

@testset "Galois Fields" begin
    
    @test GF(7) <: ZZmod{7}
    @test GF(5,3) <: Quotient{X,<:UnivariatePolynomial{:x,<:ZZmod{5}}} where X
    
    G7 = GF(7)
    @test G7(3)^2 == G7(2)

    G53 = GF(5,3)
    @test inv(G53([1,0,1])) * G53([1,0,1]) == 1
    
end
