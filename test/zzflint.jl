module TestZZZ

using CommutativeRings
using Test

@testset "construction and promotion" begin
    @test basetype(ZZZ) == BigInt
    @test depth(ZZZ) == 1
    @test iscoprime(ZZZ(18), ZZZ(35))
    @test isirreducible(ZZZ(17))
    @test !isirreducible(ZZZ(18))
    @test typeof(copy(ZZZ(big"2"))) == ZZZ
    a = ZZZ(16)
    @test convert(ZZZ, a) === a
    @test ZZZ(a) == a
    @test ZZZ(100) + ZZZ(100) == ZZZ(200)
    @test ZZZ(10) + 10 == 20
    @test ZZZ(1) + QQ(1, 2) == QQ(3, 2)
    @test ZZZ(Int8(1)) + QQ(1, 2) == QQ(3, 2)
    @test typeof(ZZZ(1) + QQ(1, 2)) == QQ{BigInt}
    @test typeof(ZZZ(1) + 1 // 2) == QQ{BigInt}
    @test hash(ZZZ(big"123")) == hash(123)
end

@testset "ZZZ()" begin
    T = Int
    Z = ZZZ
    z = zero(Z)
    @test z == zero(z)
    @test iszero(z)
    @test !isone(z)
    o = one(z)
    @test isunit(o)
    @test isone(o)
    @test !iszero(o)
    n1 = T(19)
    n2 = Base.hastypemax(T) ? typemax(T) : T(big"987654321987654321987654321")
    z1 = Z(n1)
    z2 = ZZZ(n2)
    @test !isunit(z1)
    @test z1 + z1 == ZZZ(T(2n1))

    @test z1 - z1 == z
    @test z1 - z2 == ZZZ(n1 - n2)
    @test -z2 == ZZZ(-n2)
    @test isunit(-o)

    @test z1 * z1 == ZZZ(T(n1 * n1))
    @test z1 * n1 == ZZZ(T(n1 * n1))
    @test n1 * z1 == ZZZ(T(n1 * n1))

    @test z1^2 == ZZZ(n1^2)
    @test z1^1000 > 0

    z3 = 2z1
    z4 = z3 + o
    @test z3 ÷ z1 == ZZZ(T(2))
    @test z1 ÷ z3 == z
    @test z3 / z1 == ZZZ(T(2))
    @test z1 \ z3 == ZZZ(T(2))
    @test_throws DomainError z4 / z2

    @test inv(-o) == -o
    @test_throws DomainError inv(z1)

    @test gcd(z3, z1) == z1
    @test gcd(z3, z1, z3) == z1
    @test gcdx(z3, z1) == (z1, zero(z3), one(z1))
    @test gcdx(ZZZ(60), ZZZ(28), ZZZ(6)) == (2, [-1, 2, 1])
    @test lcm(z3, z1) == z3
    @test rem(ZZZ(12), ZZZ(5)) == ZZZ(2)

    @test sprint(show, z3) == "$(Int(2n1))"

    @test value(z2) == n2

    @test factor(z3) == [Z(2) => 1, n1 => 1]
    @test eltype(factor(z3)) == Pair{Z,Int}
end

@testset "conversion from rational type $T" for T in (QQ{Int}, Frac{ZZZ}, Rational{Int})
    a = T(1 // 2)
    @test_throws InexactError Int(a)
    b = T(12)
    @test Int(b) == 12
end
@testset "conversion from fraction type Frac{ZZZ[:x]}" begin
    P = ZZZ[:x]
    x = monom(P)
    @test_throws InexactError P((x^2 + 1) // (2x))
    a = 2x^3 - x + 1
    b = a // 1
    @test P(b) == a
end

@testset "div/rem div($Z($a), $b, $m)" for Z in (ZZZ,),
    a in Z.((900, 945, 955, -945, -955)),
    b in Z.((100, -100)),
    m in (RoundToZero, RoundDown, RoundUp, RoundNearest, nothing)

    if m === nothing
        @test divrem(a, b) == divrem(Int(a), Int(b))
        @test div(a, b) == div(Int(a), Int(b))
        @test rem(a, b) == rem(Int(a), Int(b))
        @test mod(a, b) == mod(Int(a), Int(b))
    else
        @test divrem(a, b, m) == divrem(Int(a), Int(b), m)
        @test div(a, b, m) == div(Int(a), Int(b), m)
        @test rem(a, b, m) == rem(Int(a), Int(b), m)
    end
end

end
