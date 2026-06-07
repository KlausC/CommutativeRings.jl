module DetermiantTest

using Test
using CommutativeRings
using CommutativeRings: det_DJB, det_QR, det_Bird, det_MV

X = ZZ / (2^2 * 3 * 5)
@testset "determinant division free $i" for (i, a) in enumerate((
    [2 3 5; 3 3 2; 10 2 3],
    [2 3 3 4; 4 0 4 2; 2 3 0 4; 3 3 4 2],
    [-6 4 -11 9; -2 21 -16 25; 21 2 24 -25; 24 -23 2 2],
))

    A = X.(a)
    res = X(Integer(round(det(a))))
    db = det_Bird(A)
    @test db == res
    @test db isa X
    @test_throws AssertionError("category_trait(D) <: IntegralDomainTrait") det_DJB(A)
    @test det_QR(A) == res
    @test det_MV(A) == res
end

@testset "crt" begin
    @test crt(Int8(3), Int8(-3), 4, 15) == (27, 60, 1)

    pp = rand(2:typemax(Int), 10)
    lp = lcm(big.(pp))
    a = rand(0:lp)
    xx = Int.(mod.(a, pp))
    c, l = crt(xx, pp)
    @test c == a
    @test l == lp
end


end # module
