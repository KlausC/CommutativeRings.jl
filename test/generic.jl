
@testset "ZZ" begin
    
    z = zero(ZZ{Int32})
    @test z == zero(z)
    @test iszero(z)
    @test !isone(z)
    o = one(z)
    @test isone(o)
    @test !iszero(o)
    n1 = Int32(19)
    n2 = typemax(Int32)
    z1 = ZZ{Int32}(n1)
    z2 = ZZ(n2)
    @test z1 + z1 == ZZ(Int32(2n1))
    @test_throws OverflowError z2 + z2
    
    @test z1 - z1 == z
    @test z1 - z2 == ZZ(n1 - n2)
    @test -z2 == ZZ(-n2)
    @test_throws OverflowError -z1 - z2
    
    @test z1 * z1 == ZZ(Int32(n1 * n1))
    @test z1 * n1 == ZZ(Int32(n1 * n1))
    @test n1 * z1 == ZZ(Int32(n1 * n1))
    @test_throws OverflowError z1 * z2

    @test z1^2 == ZZ(n1^2)
    @test_throws OverflowError z1^1000
    
    z3 = 2z1
    z4 = z3 + o
    @test z3 / z1 == ZZ(Int32(2))
    @test_throws DivideError z4 / z2

end
