
@testset "construction" begin
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
    @test_throws MethodError Ideal(QQ(1))
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
end
