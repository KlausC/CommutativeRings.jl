
module TestFourier
using CommutativeRings
using Test
using CommutativeRings: schoenhage_strassen

function dft(n, f, w)
    r = similar(f)
    for i = 1:n
        s = 0
        for j = 1:n
            s += f[j] * w^((i - 1) * (j - 1))
        end
        r[i] = s
    end
    r
end

N = 3 * 2^12 # 12288
@testset "fft $n" for n in 2 .^ (1:12)
    Z = ZZ / (N + 1)
    g = Z(107)
    @test order(g) == order(Z) - 1
    w = g^(order(g) ÷ n)
    @test w^n == 1 && w^(n ÷ 2) == -1

    f = Z.([1; n; zeros(Int, n - 2)])
    ff = fft(n, f, w)
    n > 512 || @test dft(n, f, w) == ff
    @test fft(n, Z.([1; n]), w) == ff
    @test ff[1] == 1 + n
    @test ff[n÷2+1] == 1 - n
    @test fft(n, ff, inv(w)) == f * n
end

@testset "fft! $(2*2^k)" for k = 1:8
    n = 2^k
    d = 2^(k ÷ 2)
    δ = n ÷ d
    z = d == δ ? 4 : 2
    F = rand(1:100, 2n)
    W = similar(F)
    FQ = fft!(δ, copy(F), 2d, z, W)
    FF = fft!(δ, copy(FQ), 2d, -z, W)
    @test all(FF .== F * δ)
end

@testset "schoenhage_strassen " for N in (8, 16, 32, 64)
    F = rand(-100:100, N)
    P = ZZ{Int}[:x]
    Q = P / (monom(P, N) + 1)
    p = P(F)^2
    F2 = schoenhage_strassen(F, F, 2N)
    @test p[0:2N-1] == F2
    q = Q(p)
    FN = schoenhage_strassen(F, F, N)
    @test value(q)[0:N-1] == FN
end

end # module
