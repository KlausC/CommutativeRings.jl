
using Primes

tm(T::Type{<:Integer}) = typemax(T)
tm(::Type{BigInt}) = big"98723497897819812497842123481211786588091"

@testset "ZZmod{$m,$T}" for T in (Int32, Int64, #= BigInt =# ), m in (65, tm(T))
    
    while isprime(m)
        m -= 2
    end
    m = T(m)
    phi = totient(m)
    p = factor(m).pe[end].first # the greateset prime factori of m

    z = zero(ZZmod{m,T})
    @test z == zero(z)
    @test iszero(z)
    @test !isone(z)
    o = one(z)
    @test isone(o)
    @test !iszero(o)
    n1 = T(19)
    while gcd(n1, m) != 1
        n1 += T(1)
    end
    n2 = tm(T) - 16
    z1 = ZZmod{m,T}(n1)
    z2 = ZZmod{m}(n2)
    zp = ZZmod{m}(p)
    @test z1 + z1 == ZZmod(T(2n1), m)
    
    @test z1 - z1 == z
    @test z1 - z2 == ZZmod(n1 - n2, m)
    @test -z2 == ZZmod{m}(-n2)
    
    @test z1 * z1 == ZZmod{m}(T(n1 * n1))
    @test z1 * n1 == ZZmod{m}(T(n1 * n1))
    @test n1 * z1 == ZZmod{m}(T(n1 * n1))

    @test z1^2 == ZZmod{m}(n1^2)
    
    z3 = 2z1
    z4 = z3 + o
    @test z3 / z1 == ZZmod{m}(T(2))
    @test z4 / z1 == z4 * inv(z1)

    @test z1^phi == o
    @test z2^(phi-1) == inv(z2)

    @test_throws DomainError inv(zp)
end
