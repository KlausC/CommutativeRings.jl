module AlgebraicNumbers

using CommutativeRings
using Test

P = QQ{BigInt}[:x]
x = monom(P)
tol = eps(BigFloat) * 100

@testset "AlgebraicNumber basics" for (p, s, r) in [
    (x^2 + 1, eps() * im, im),
    (x^2 - 2, 1, sqrt(big(2))),
    (x^2 - 2, -1, -sqrt(big(2))),
]
    a = AlgebraicNumber(p, s)
    @test minimal_polynomial(a) == p
    @test approx(a) ≈ r
end

@testset "Algebraic identities" begin
    a = AlgebraicNumber(x^2 + 1, im)
    b = AlgebraicNumber(x^2 + 1, -im)
    @test AlgebraicNumber(im) == a
    @test a == a + 0
    @test a != b
    @test hash(a) == hash(a + 0)
    @test isunit(a)
    @test !isunit(zero(a))
    @test isone(one(a))
    @test !iszero(a)
    @test one(a) == 1
    @test zero(a) == 0
    @test hash(zero(a)) == hash(0)
    @test hash(one(a)) == hash(1)
end

@testset "AlgebraicNumber reducible" begin
    p = x^17 + x - 1 # == (x^15 + x^14 .... -1) * (x^2 - x + 1)
    a = AlgebraicNumber(p, 0.5 + 0.9 * im)
    @test p(approx(a)) ≈ 0.0 atol = tol
    @test deg(a) == 2
    mini = minimal_polynomial(a)
    @test mini == x^2 - x + 1
    @test mini(approx(a)) ≈ 0.0 atol = tol

    a = AlgebraicNumber(p, 0.5)
    @test p(approx(a)) ≈ 0.0 atol = tol
    mini = minimal_polynomial(a)
    @test deg(a) == 15
    @test mini(approx(a)) ≈ 0.0 atol = tol
end

@testset "AlgebraicNumber powers" begin
    a = AlgebraicNumber(x^2 + 1)
    @test a^2 == -1
    @test approx(a^2) ≈ -1.0
    @test deg(a^2) == 1
    @test minimal_polynomial(a^2) == x + 1
    @test field_polynomial(a, x^2) == (x + 1)^2
    @test field_polynomial(a, x^2, Val(true)) == field_polynomial(a, x^2)
end

# cbrt is not defined for complex arguments intentionally - we use it here to test `pow`.
cbrt(a::Any) = a^(1 // 3)
@testset "Algebraic $op arithmetic" for (op, d) in (
    (-, 3),
    (inv, 3),
    (sqrt, 6),
    (cbrt, 9),
    (conj, 3),
    (real, 3),
    (imag, 6),
    (abs, 6),
)
    a = AlgebraicNumber(x^3 + x + 1, Inf)
    c = op(a)
    @test deg(c) == d
    @test minimal_polynomial(c)(c) == 0
    @test approx(c) ≈ op(approx(a))
end

@testset "Algebraic $op(.,.) arithmetic" for op in (+, -, *, /)
    a = AlgebraicNumber(x^2 + 1)
    b = AlgebraicNumber(x^3 + x + 1)
    c = op(a, b)
    @test deg(c) == deg(a) * deg(b)
    @test minimal_polynomial(c)(c) == 0
    @test approx(c) ≈ op(approx(a), approx(b))
end

@testset "Algebraic $op(A, $b) arithmetic" for op in (+, -, *, /), b in (11, QQ(1 // 11))
    a = AlgebraicNumber(x^3 + x + 1)
    b = big(b)
    c = op(a, b)
    @test deg(c) == deg(a)
    @test minimal_polynomial(c)(c) == 0
    @test approx(c) ≈ op(approx(a), approx(b))
end

@testset "Algebraic $op($a,A) arithmetic" for op in (+, -, *, /), a in (11, ZZ(11))
    a = big(a)
    b = AlgebraicNumber(x^3 + x + 1)
    c = op(a, b)
    @test deg(c) == deg(b)
    @test minimal_polynomial(c)(c) == 0
    @test approx(c) ≈ op(approx(a), approx(b))
end

@testset "Algebraic conjugates $n" for n in (2, 3, 5)
    p = (x^n - 1) / (x - 1)
    a = AlgebraicNumber(p, 1 + 0.5im)
    b = conj(a)
    @test minimal_polynomial(a) === minimal_polynomial(b)
    @test conj(approx(a)) ≈ approx(b)
    @test conj(a, a.rootid) == a

    cs = conj.(a, 1:n-1)
    @test prod(cs) == -(-1)^n
    @test sum(cs) == -1
    for i = 1:n-1
        @test minimal_polynomial(cs[i]) == p
        @test approx(cs[i])^n ≈ 1
    end
end

@testset "Algebraic - roots of unity" begin
    q = QQ(1 // 5)
    a = cispi(q)
    b = cospi(q)
    @test minimal_polynomial(a) == (x^5 + 1) / (x + 1)
    @test b == real(a)
    @test sinpi(q) == imag(a)
    @test cispi(-q) * cispi(q) == 1
end

@testset "Algebraic - expressions" begin
    expr5 = :(sqrt(5) + 1)
    @test AlgebraicNumber(expr5) / 4 == cospi(QQ(1 // 5))

    expr17 = :(
        1 - sqrt(17) +
        sqrt(34 - sqrt(68)) +
        sqrt(68 + sqrt(2448) + sqrt(2720 + sqrt(6284288)))
    )
    @test AlgebraicNumber(expr17) / 16 == cospi(QQ(1 // 17))
end

@testset "exactness of pure imaginary roots" begin
    q = QQ(1//7)
    a = cospi(q)
    @test real(approx(a * AlgebraicNumber(im))) == 0
end

@testset "show AlgebraicNumber" begin
    a = AlgebraicNumber(1 // 2)
    @test string(a) == "AlgebraicNumber(x - 1/2, 1, 0.5)"
    a = AlgebraicNumber(x^2 + 4, im)
    @test string(a) == "AlgebraicNumber(x^2 + 4, 2, 0.0 + 2.0im)"
end

@testset "cardano's formula $(x^3+a*x^2+b*x+c)" for (a, b, c) in (QQ.(rand(-10:10, 3)),)

    pc = x^3 + a * x^2 + b * x + c
    p = b - a^2 / 3
    q = 2 * a^3 / 27 - a * b / 3 + c

    da = sqrt(AlgebraicNumber((q / 2)^2 + (p / 3)^3))
    ua = (da - q / 2)^(1 // 3)
    va = (-da - q / 2)^(1 // 3)
    e3 = cispi(QQ(2 // 3))

    ra = ua + va - a / 3
    @test minimal_polynomial(ra) == pc
    rb = (ua * e3 + va) * e3 - a / 3
    rc = (ua + va * e3) * e3 - a / 3
    @test minimal_polynomial(rb) == pc
    @test minimal_polynomial(rc) == pc
    @test Set(conj.(ra, 1:3)) == Set([ra, rb, rc])
end

end
