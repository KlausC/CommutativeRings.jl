
using Primes

tm(T::Type{<:Integer}) = typemax(T)
tm(::Type{BigInt}) = big"1000000000000000000000000000000000067"

@testset "ZZmod{$m,$T}" for T in (UInt16, Int32, Int64, BigInt), m in (65, tm(T))
    
    while T != BigInt && isprime(m)
        m -= 2
    end
    m = T(m)

    if T != BigInt || m <= typemax(UInt128)
        phi = totient(m)
        p = factor(m).pe[end].first # the greatest prime factor of m
    else
        phi = (m-1)*4
        m = m * T(5)
    end

    n1 = T(19)
    while gcd(n1, m) != 1
        n1 += T(1)
    end
    n2 = tm(T) - T(16)
    while gcd(n2, m) != 1
        n2 += T(1)
    end

    ZZp = new_class(ZZmod{:p,T}, m)
    @test typeof(modulus(ZZp)) == T
    isbitstype(T) && @test typeof(modulus(ZZmod{m,T})) == T
    @test typeof(modulus(ZZmod{3,T})) == T
    z = zero(ZZp)
    @test z == zero(z)
    @test iszero(z)
    @test !isone(z)
    o = one(z)
    @test isunit(o)
    @test isone(o)
    @test !iszero(o)
    z1 = ZZp(n1)
    z2 = ZZp(n2)
    zp = ZZp(p)
    @test isunit(z1)
    @test z1 + z1 == ZZp(T(2n1))
    
    @test z1 - z1 == z
    @test z1 - z2 == ZZp(m + mod(n1, m) - mod(n2, m))
    @test -z2 == ZZp(m - mod(n2, m))
    
    @test z1 * z1 == ZZp(T(n1 * n1))
    @test z1 * n1 == ZZp(T(n1 * n1))
    @test n1 * z1 == ZZp(T(n1 * n1))

    @test z1^2 == ZZp(n1^2)
    
    z3 = 2z1
    z4 = z3 + o
    @test z3 / z1 == ZZp(T(2))
    @test z4 / z1 == z4 * inv(z1)
    @test z1 \ z4 == z4 / z1

    @test z1^phi == o
    @test z2^(phi-1) == inv(z2)

    @test_throws DomainError inv(zp)
    @test_throws DomainError ZZmod{0,T}(0)

    if T != BigInt
        @test zero(ZZmod{m}) == z
        @test one(ZZmod{m}) == o
        @test ZZmod(n1, m) == ZZp(n1)
        @test hash(ZZmod(n1, m)) == hash(ZZp(n1))
    end

    @test ZZp(m-1) + ZZp(2) == ZZp(1)
    @test ZZp(1) - ZZp(2) == ZZp(m-1)
    @test ZZp(1) + ZZp(3) == ZZp(4)
    @test ZZp(3) - ZZp(2) == ZZp(1)

    @test ZZp(4)^-1 == inv(ZZp(4))
    @test ZZp(3)^1 == ZZp(3)
    @test ZZp(3)^0 == o

    @test copy(ZZp(5)) == ZZp(5)
    @test CommutativeRings.degree(z3) == 0
    @test_throws MethodError div(z3, z3)
    @test_throws MethodError rem(z3, z3)
end

@testset "auxiliary functions" begin
    @test CommutativeRings.invmod2(big"12", big"31") == big"13" # gcdx[2] > 0
    @test CommutativeRings.invmod2(big"15", big"31") == big"29" # gcdx[2] < 0
    @test CommutativeRings._unsigned(Int) == UInt
    @test CommutativeRings._unsigned(BigInt) == BigInt
    @test CommutativeRings._unsigned(big"-1") == big"-1"
end

