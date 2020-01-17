
using Test

import CommutativeRings: gz, gz1, wmul, wdiv


@testset "fast gcd calculation ($x, $y)" for x = typemin(Int8)+1:typemax(Int8), y = typemin(Int8)+1:typemax(Int8)
    @test gcdx(x, y) == gz(x, y) == gz1(x, y)
end

@testset "fast gcd corner cases $gg" for gg in (gz, gz1)
    @test gg(typemin(Int), -1) == (1, 0, -1)
    @test_throws OverflowError @test gg(typemin(Int), typemin(Int)) != nothing

    x, y = (86697573192186698532684444884802582408, 49191954801396582735279031812411962073)
    @test gcdx(x, y) == gg(x, y)
end

