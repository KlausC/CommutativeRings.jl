

@testset "iterate" begin
    @test length(collect(ZZ/7)) == 7
    @test length(collect(GF(3,5))) == 3^5
    @test length(collect(Monic(:x, ZZ/2, 5))) == 2^5
end


@testset "ofindex $T" for T in (Int, UInt, ZZ{Int8}, ZZ/1000, GF(2,5), QQ{Int})
    @test iszero(ofindex(0, T))
    @test isone(ofindex(1, T))
    @test ofindex(10, T) isa T
end

@testset "ofindex $T degree $n" for (T, n) in ((GF(2)[:z], 3),)
    @test ofindex(0, T, n) == monom(T, n)
    @test ofindex(1, T, n) == monom(T, n) + 1
    @test ofindex(10, T, n) isa T
end
