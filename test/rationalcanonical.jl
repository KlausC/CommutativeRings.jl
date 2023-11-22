module RationalNormalFormTest

using Test
using CommutativeRings
using LinearAlgebra

Q = QQ{BigInt}
#! format: off
tm = [
    Q.([1 2 3; 4 5 6; 7 8 10]),

    Q.([-3 -1  4 -3 -1
         1  1 -1  1  0
        -1  0  2  0  0
         4  1 -4  5  1
        -1  0  1 -1  1]),

    Q.([-1  3 -1  0 -2  0  0 -2
        -1 -1  1  1 -2 -1  0 -1
        -2 -6  4  3 -8 -4 -2  1
        -1  8 -3 -1  5  2  3 -3
         0  0  0  0  0  0  0  1
         0  0  0  0 -1  0  0  0
         1  0  0  0  2  0  0  0
         0  0  0  0  4  0  1  0])
]
#! format: on
A = tm[2]
push!(tm, [A A; -A A])

@testset "minimal_polynomial" begin
    A = tm[2]

    ma, xa = CommutativeRings._minimal_polynomial(A)
    ca = companion(ma)
    n = 4
    @test deg(ma) == n
    @test characteristic_polynomial(ca) == ma
    @test rem(characteristic_polynomial(A), ma) == 0
    B = CommutativeRings.axspace(A, xa, n)
    @test A * B == B * ca
end

@testset "rational normal form test $i" for (i, A) in enumerate(tm)
    rnf = rational_normal_form(A)
    B = transformation(rnf)
    M = matrix(rnf)

    @test det(B) |> isunit
    @test minimal_polynomial(rnf) == minimal_polynomial(A)
    @test characteristic_polynomial(rnf) == characteristic_polynomial(A)
    @test A * B == B * M
end

@testset "Weierstrass normal form test $i" for (i, A) in enumerate(tm)
    nf = weierstrass_normal_form(A)
    B = transformation(nf)
    M = matrix(nf)

    @test det(B) |> isunit
    @test minimal_polynomial(nf) == minimal_polynomial(A)
    @test characteristic_polynomial(nf) == characteristic_polynomial(A)
    @test A * B == B * M
end

Z = ZZ{BigInt}
x = monom(QQ{BigInt}[:x])

#! format: off
    sm = Any[
        Z[1;;],
        Z[12 0; 0 6],
        Z[12 0; 0 15],
        Z[0 0 0; 1 0 0; 1 1 0],
        Z[2 4 4;-6 6 12; 10 4 16],
        Z[
        0  0  0  8  0  0  0  0  0  0  4  0  0  0  0  0  0  8  0  1
        0  0  0  0  0  0  9  0  0  0  0  0  0  0  0  0  0  0  0  0
        6  0  3  0  2  0  0  0  1  0  0  0  0  0  0  0  0  0  0  0
        0  7  7  0  0  0  0  0  0  0  0  0  0  0  0  6  0  1  0  0
        0  5  0  0  4  0  0  0  0  1  0  0  0  0  0  0  0  0  0  0
        0  0  0  0  0  0  0  0  0  9  0  0  0  0  0  0  5  6  0  1
        0  0  0  0  0  0  0  0  0  0  0  0  0  0  3  0  0  0  0  0
        0  0  9  0  0  7  0  0  0  0  0  0  0  0  0  0  0  0  0  0
        0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0
        0  0  0  0  1  7  0  0  0  8  0  0  0  0  0  0  0  0  0  0
        4  0  0  7  0  0  0  0  0  0  0  0  0  0  7  0  0  0  0  0
        0  0  0  0  0  0  9  7  0  0  0  9  0  0  0  3  0  9  0  0
        0  0  5  0  4  0  0  0  0  0  0  0  0  0  0  0  0  0  0  7
        0  0  0  6  0  0  2  4  0  0  0  0  3  0  0  0  0  0  0  0
        0  0  0  0  0  4  0  0  4  0  0  0  6  0  0  0  0  0  0  0
        0  0  0  0  0  3  0  6  0  0  6  0  0  2  0  0  0  0  0  4
        0  0  0  0  0  0  0  0  0  5  0  3  0  0  0  0  0  1  0  0
        6  7  0  0  0  0  0  0  0  0  0  0  0  0  6  0  0  0  0  0
        0  0  0  4  4  0  0  0  0  0  0  0  0  1  0  0  0  0  0  9
        0  0  0  0  0  0  0  0  0  0  0  4  0  0  6  0  0  0  9  0],
        x - Q[3 -4; 1 1],
        x - Q[31 2; 0 1],
        QQ{BigInt}[:x][1;;],
    ]
#! format: on

@testset "Smith normal form test $i" for (i, A) in enumerate(sm)
    snf = smith_normal_form(A)
    S, T = transformation(snf)
    M = matrix(snf)
    @test isdiag(M)
    @test isunit(det(S))
    @test isunit(det(T))
    @test S * A * T == M
    d = snf.diag
    @test all(mod(d[i+1], d[i]) == 0 for i = 1:length(d)-1)
end

end # module
