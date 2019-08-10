
@testset "construction" begin
    @test QQ{Int}(3, 6) == 1//2
    @test QQ(3, 6) == 1//2
    @test QQ(2) == QQ(ZZ(2))
    @test QQ(Int8(2)) == QQ{BigInt}(2//1)
    @test QQ{Int8}(2) == QQ(2)
end

@testset "arithmetic" begin
    @test QQ(2//3) + QQ(1//2) == QQ(7//6)
end
