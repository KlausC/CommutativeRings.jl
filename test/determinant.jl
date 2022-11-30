module DetermiantTest

using Test
using CommutativeRings
import CommutativeRings: det_DJB, det_QR, det_Bird, det_MV

Z = ZZ / (2^2 * 3 * 5)
@testset "determinant division free $i" for (i, a) in enumerate((
    [2 3 5; 3 3 2; 10 2 3],
    [2 3 3 4; 4 0 4 2; 2 3 0 4; 3 3 4 2],
    [-6 4 -11 9; -2 21 -16 25; 21 2 24 -25; 24 -23 2 2],
))

    A = Z.(a)
    res = det_Bird(A)
    @test res isa Z
    @test_throws AssertionError("category_trait(D) <: IntegralDomainTrait") det_DJB(A)
    @test det_QR(A) == res
    @test det_MV(A) == res
end

end # module
