

@testset "iterate" begin
    @test length(collect(ZZ/7)) == 7
    @test length(collect(GF(3,5))) == 3^5
    @test length(collect(Monic(:x, ZZ/2, 5))) == 2^5
end

