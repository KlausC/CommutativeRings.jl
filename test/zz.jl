
@testset "ZZ{$T}" for T in (Int32, Int64, BigInt)
    
    z = zero(ZZ{T})
    @test z == zero(z)
    @test iszero(z)
    @test !isone(z)
    o = one(z)
    @test isunit(o)
    @test isone(o)
    @test !iszero(o)
    n1 = T(19)
    n2 = Base.hastypemax(T) ? typemax(T) : T(big"987654321987654321987654321")
    z1 = ZZ{T}(n1)
    z2 = ZZ(n2)
    @test !isunit(z1)
    @test z1 + z1 == ZZ(T(2n1))
    T != BigInt && @test_throws OverflowError z2 + z2
    
    @test z1 - z1 == z
    @test z1 - z2 == ZZ(n1 - n2)
    @test -z2 == ZZ(-n2)
    @test isunit(-o)
    T != BigInt && @test_throws OverflowError -z1 - z2
    
    @test z1 * z1 == ZZ(T(n1 * n1))
    @test z1 * n1 == ZZ(T(n1 * n1))
    @test n1 * z1 == ZZ(T(n1 * n1))
    T != BigInt && @test_throws OverflowError z1 * z2

    @test z1^2 == ZZ(n1^2)
    T != BigInt && @test_throws OverflowError z1^1000
    
    z3 = 2z1
    z4 = z3 + o
    @test z3 ÷ z1 == ZZ(T(2))
    @test z1 ÷ z3 == z
    @test z3 / z1 == ZZ(T(2))
    @test z1 \ z3 == ZZ(T(2))
    @test_throws DomainError z4 / z2

    @test inv(-o) == -o
    @test_throws DomainError inv(z1)
    
    @test gcd(z3, z1) == z1
    @test gcdx(z3, z1) == (z1, zero(z3), one(z1))
    @test lcm(z3, z1) == z3
    @test rem(ZZ(12), ZZ(5)) == ZZ(2)

    io = IOBuffer()
    @test show(io, z3) == nothing
end
