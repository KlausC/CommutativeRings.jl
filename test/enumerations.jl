

using CommutativeRings: len

@testset "iterate" begin
    @test length(collect(ZZ/7)) == 7
    @test length(collect(GF(3,5))) == 3^5
    @test length(collect(Monic(:x, ZZ/2, 5))) == 2^5
    @test eltype(Monic(:x, ZZ/2, 5)) == (ZZ/2)[:x]
end


@testset "ofindex $T" for (T, r) in ((Int, 0), (UInt, 0), (ZZ{Int8}, 0), (ZZ/77, 77), (GF(2,5),2^5), (QQ{Int}, 0))
    @test iszero(ofindex(0, T))
    @test isone(ofindex(1, T))
    @test ofindex(10, T) isa T
    @test len(T) == r
end

@testset "ofindex $T degree $n" for (T, n) in ((GF(2)[:z], 3),)
    @test ofindex(0, T, n) == monom(T, n)
    @test ofindex(1, T, n) == monom(T, n) + 1
    @test ofindex(10, T, n) isa T
end
