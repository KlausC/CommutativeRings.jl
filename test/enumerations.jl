
using CommutativeRings: len, GFImpl

@testset "iterate" begin
    @test length(collect(ZZ/7)) == 7
    @test length(collect(GF(3,5))) == 3^5
    @test length(collect(Monic((ZZ/2)[:x], 5))) == 2^5
    @test eltype(Monic((ZZ/2)[:x], 5)) == (ZZ/2)[:x]
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

@testset "ofindex Quotient" begin
    P = (ZZ/5)[:x]
    x = monom(P)
    Q = P / ( x^3 + x + 1)
    n = length(Q)
    @test length(Q) == 125
    @test sort(ofindex.(0:n-1, Ref(Q))) == sort(collect(Q))
end

@testset "factors" begin
    @test length(factors(12)) == 6
    @test factors(12) |> collect |> sort == [1, 2, 3, 4, 6, 12]
end
