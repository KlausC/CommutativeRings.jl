module TestLLL

using CommutativeRings
using LinearAlgebra
using Test

# example data from wikipedia article on LLL
B1 = Matrix(
    [
        33554516 3750842 -8343524 21489465 13970499
        25456939 2845665 -6330013 16303498 10599055
        10552673 1179613 -2623983 6758294 4393630
        10628092 1188047 -2642738 6806596 4425031
    ]',
)

BM1= Matrix([
    -22 35 -64 -6 -67
    -57 59 -45 8 93
    28 114 -8 43 -4
    -42 36 118 -28 -3
]')

C1 = Matrix(
    [
        -2+2im  7+3im  7+3im -5+4im
         3+3im -2+4im  6+2im -1+4im
         2+2im -8     -9+im  -7+5im
         8+2im -9      6+3im -4+4im
    ]'
)

CM1 = Matrix(
    [
        -6+3im -2+2im  2-2im -3+6im
         6-im   3+3im  5-5im  2+im
         2-2im  2+2im -3-im  -5+3im
        -2+im   8+2im  7+im  -2-4im
    ]'
)

@testset "lll_reduce $i" for (i, pair) in enumerate([(B1, BM1), (C1, CM1)])
    B, BM = pair
    Q, R, M = lll_reduce(B)
    @test norm(Q'Q - I) <= 1e-8
    @test norm(Q' * B * M - R) <= 1e-5
    @test abs(abs(det(M)) - 1) <= 1e-5
    @test norm(B * M) <= norm(BM) * 2
end

end # module
