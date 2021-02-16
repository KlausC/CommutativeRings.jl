
import CommutativeRings: pseudo_ideal

@testset "basics" begin
    R = ZZ{Int}
    RX = R[:x]
    RYZ = R[:y,:z]
    @test iszero(Ideal(0))
    @test isone(Ideal(-1))
    @test Ideal(15, 21) == Ideal(3)
    @test Ideal([3, 5]) == R
    @test R == Ideal(-1)
    @test Ideal(3, ZZ(15)) == Ideal(3)

    x, = generators(RX)
    y, z = generators(RYZ)
    @test Ideal(x, x^2-x) == Ideal(x)
    @test Ideal(y + z, y^2 - z^2) == Ideal(y + z)

    @test pseudo_ideal(R, 15) == ZZ(15)
    @test pseudo_ideal(R, ZZ(Int8(127))) == 127
    @test pseudo_ideal(R, [15, 21]) == Ideal(3)
    i = Ideal(ZZ(3))
    @test pseudo_ideal(R, i) === i
    j = Ideal(ZZ(Int16(3)))
    @test i == j
end

@testset "operations" begin
    P = QQ{Int}[:x,:y,:z]
    x, y, z = generators(P)
    @test Ideal(x, y) isa Ideal

    A = [x*z^2 - 3y*z; x^2-2y; x*y - 5z]
    B = [x*y]
    ida = Ideal(A)
    idb = Ideal(B)
    idint = intersect(ida, idb)
    idsum = ida + idb

    @test ida isa Ideal{P}
    @test Ideal(ida.base) == ida
    @test zero(Ideal{P}) == zero(ida)
    @test zero(Ideal{P}) == Ideal(P(0))
    @test one(Ideal{P}) == Ideal(P(1))
    @test isone(Ideal(QQ(2)))
    @test issubset(idint, ida) 
    @test issubset(idint, idb) 
    @test issubset(ida, idsum)
    @test issubset(idb, idsum)
    @test A[1] * y + A[2] in ida
    @test 2x*y*z^2 - 9x*y^2 in idint
    @test B[1] * x + A[1] * y in idsum

    i0 = zero(ida)
    i1 = one(ida)
    @test i0 ⊆ ida ⊆ i1
    @test i0 + ida == ida
    @test i1 + ida == i1
    @test i1 ∩ ida == ida
    @test i0 ∩ ida == i0
    @test zero(ida) != idint^2 ⊆ ida * idb ⊆ idint
    @test one(ida) != idsum ⊆ one(ida)

    @test isone(idb^0)
    @test idb^1 === idb
    @test idb^2 == idb * idb
    @test idb^3 == idb * idb * idb
    @test idb^4 == idb * idb * idb * idb

    @test idb + x == x + idb
    @test idb * x == x * idb
    @test rem((x + y)^2, idb) == x^2 + y^2
end
