
using CommutativeRings: sintern

@testset "sintern" begin
    @test sintern(:x) === :x
    @test sintern(12) === 12
    @test sintern(:x, :y) === :xy
    @test sintern(big"2") === Symbol(big"2")
    @test sintern(big"2.0") === Symbol(hash(big"2.0"))
end


@testset "gettypevar" begin
    @test deg(modulus(GF(2, 5))) == 5
end

