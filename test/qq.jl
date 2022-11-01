
@testset "construction" begin
    @test basetype(QQ{Int}) == ZZ{Int}
    @test lcunit(QQ(-1, 3)) == 1
    @test lcunit(QQ(0)) == 1
    @test copy(QQ(12//15)) == QQ(4, 5)
    @test QQ{Int32}(QQ(3, 4)) isa QQ{Int32}
    @test QQ{Int}(QQ(3, 4)) !== nothing
    @test QQ{BigInt}(ZZ(11)) == 11
    @test ZZ(12) // ZZ(13) == QQ(12, 13)

    @test QQ(1, 2) + QQ{Int8}(1, 3) == 5//6
    @test QQ(1, 3) - ZZ(1) == -2//3
    @test QQ(1, 2) * 2 == 1
    @test QQ(1, 2) - 1//3 == 1//6

    @test QQ(1, 2) / QQ(1, 3) == 3//2
    @test -QQ(1) == -1
    @test divrem(QQ(1,2), QQ(1, 3)) == (3//2, 0//1)
    @test div(QQ(1,2), QQ(1, 3)) == 3//2
    @test iszero(rem(QQ(1,2), QQ(1, 3)))
    @test isunit(QQ(23, 24))
    @test !isunit(QQ(0))
    @test isone(QQ(11, 11))
    @test zero(QQ{Int}) == 0
    @test one(QQ{Int8}) == 1
    @test hash(QQ(13, 14)) == hash(13//14)

    @test sprint(show, QQ(12, 13)) == "12/13"
    @test sprint(show, QQ(12, 1)) === "12"

    @test QQ{Int}(3, 6) == 1//2
    @test QQ(3, 6) == 1//2
    @test QQ(2) == QQ(ZZ(2))
    @test QQ(Int8(2)) == QQ{BigInt}(2//1)
    @test QQ{Int8}(2) == QQ(2)
    @test QQ(1//2) == 1//2

    @test_throws ArgumentError QQ(0, 0)
    @test_throws ArgumentError QQ(1, typemin(Int))
    @test QQ(2, typemin(Int)) == QQ(-1, typemin(Int)÷(-2))
    @test QQ(1, typemin(Int16)) == QQ(-1, -Int(typemin(Int16)))
    @test_throws InexactError QQ(1, typemax(UInt))
    @test_throws InexactError QQ(-1, typemax(UInt))
    #= would be nice to have
    @test_broken QQ(-3, typemax(UInt)) == QQ(-1, Int(typemax(UInt)÷3))
    @test_broken QQ(3, typemax(UInt)) == QQ(1, Int(typemax(UInt)÷3))
    @test_broken QQ(typemax(UInt), -3) == QQ(-1, Int(typemax(UInt)÷3))
    @test_broken QQ(typemax(UInt), 3) == QQ(1, Int(typemax(UInt)÷3))
    =#
end

@testset "arithmetic" begin
    @test QQ(2//3) + QQ(1//2) == QQ(7//6)
end

@testset "gcd calculations" begin
    @test gcd(QQ(1//3), QQ(2//5)) == 1 // 15
    @test gcd(QQ((2*3)//(5*7)), QQ((2*5)//(3*7))) == QQ(2, 3*5*7)
    @test gcdx(QQ((2*3)//(5*7)), QQ((2*5)//(3*7))) == (QQ(2, 3*5*7), -11, 4)
    @test lcm(QQ((2*3)//(5*7)), QQ((2*5)//(3*7))) == QQ(2*3*5, 7)
end

