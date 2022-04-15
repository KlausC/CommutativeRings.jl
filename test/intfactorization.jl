
using CommutativeRings: hensel_lift, partsums, subset, remove_subset!, allgcdx

let x = monom(ZZ{Int}[:x]), u = x^8 + x^6 -3x^4 -3x^3 +8x^2 + 2x - 5

@testset "integer polynomials over $T" for T in (Int64, BigInt)
    x = monom(ZZ{T}[:x])
    b = x^2 + 5x + 1
    a = x + 2
    c = a * b
    @test factor(c) == [a =>1; b=>1]
end

@testset "coeffbounds" begin
    @test_throws ArgumentError coeffbounds(zero(u), 0)
    @test_throws ArgumentError coeffbounds(10one(u), 1)
    @test coeffbounds(10one(u), 0) == [10]
    @test coeffbounds(u, 0) == [1]
    @test coeffbounds(u, 1) == [5, 1]
    @test coeffbounds(u, 2) <= [5, 12, 1]
    @test coeffbounds(u, 3) <= [5, 21, 13, 1]
    @test coeffbounds(u, 4) <= [5, 26, 36, 14, 1]
end

@testset "hensel_lifting" for (p, q) in [(13, 13)]
    X = varname(x)
    
    r = gcd(p, q)
    Pq = (ZZ/q)[X]
    Pqr = (ZZ/(q*r))[X]
    v = first.(factor(Pq(u)))
    a = allgcdx(v)
    V, qr = hensel_lift(u, v, a)
    @test Pqr(u) == Pqr(prod(V))
    @test all(Pq.(V) .== v)

    #=
    p, q = p, q * r
    r = gcd(p, q)
    Pq = (ZZ/q)[X]
    Pqr = (ZZ/(q*r))[X]
    v = V
    V, qr = hensel_lift(u, v, a)
    @test Pqr(u) == prod(V)
    @test all(Pq.(V) .== v)
    =#
end

@testset "partsums" begin
    s = [2, 3, 10]
    @test partsums(s) == ( 0xb42d, [1,0,1,1,0,1,0,0], [[0], [], [1], [2], [], [3], [], []])


end

@testset "subsets" begin
    vv = [10, 20, 30, 40]
    @test subset(vv, 0) == Int[]
    @test subset(vv, 6) == [20, 30]
    @test subset(vv, -1) == vv

    @test remove_subset!(copy(vv), -1) |> isempty
    @test remove_subset!(copy(vv), 5) == [20, 40]
    remove_subset!(vv, 8)
    @test vv == [10, 20, 30]
end

@testset "factor in ZZ[x]" begin
    P = ZZ{Int}[:x]
    x = monom(P)
    p = (x^2 + 3)^4 * (x^3 + 1)^3
    f = factor(p)
    @test length(f) == 3
    @test f[1] == Pair(x + 1, 3)
    @test f[2] == Pair(x^2 - x + 1, 3)
    @test f[3] == Pair(x^2 + 3, 4)

    p = x^100 - 1
    f = factor(p)
    @test length(f) == 9
    for i = 1:9
        u = first(f[i])
        @test isirreducible(u)
    end
    f = factor(p, 2)
    @test length(f) == 12

    P = ZZ{BigInt}[:x]
    x = monom(P)
    p = 2x^3 + 7x^2 + x + 1
    q = 3x^2 + 2

    fac = factor(p * q)
    @test prod(fac) == p * q
    @test length(fac) == 2
    @test isreducible(p * q)

    fac = factor(p(x^40))
    @test prod(fac) == p(x^40)
    @test length(fac) == 1
    @test isirreducible(p(x^40))
    
end

end
