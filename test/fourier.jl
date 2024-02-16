
module TestFourier
using CommutativeRings
using Test
using CommutativeRings: ffthf, ffthb, butterfly!, fft2
using CommutativeRings: revert, ilog, allpf

# naive implementation for testing
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

# product of prime factors of `k`, which are <= `n`.
function smallprod(k, n)
    f = factor(k)
    prod(p^x for (p, x) in f if p <= n; init = 1)
end

# return some examples for p^k - 1 having big smallprods
function smallcases(p, n, m = 99)
    tm = typemax(Int)
    [(i, x) for (i, x) in enumerate(smallprod.(p .^ (1:ilog(p, tm)) .- 1, n)) if x > m]
end

N = 3 * 2^12 # 12288
@testset "fft $n" for n in 2 .^ (1:12)
    Z = ZZ / (N + 1)
    g = Z(107)
    @test order(g) == order(Z) - 1
    w = g^(order(g) ÷ n)
    @test w^n == 1 && w^(n ÷ 2) == -1

    f = Z.([1; n; zeros(Int, n - 2)])
    ff = fft2(n, f, w)
    n > 512 || @test dft(n, f, w) == ff
    @test fft2(n, Z.([1; n]), w) == ff
    @test ff[1] == 1 + n
    @test ff[n÷2+1] == 1 - n
    @test fft2(n, ff, inv(w)) == f * n
end

@testset "fft! $(2*2^k)" for k = 1:8
    n = 2^k
    d = 2^(k ÷ 2)
    δ = n ÷ d
    z = d == δ ? 4 : 2
    F = rand(1:100, 2n)
    W = similar(F)
    FQ = fft!(δ, copy(F), 2d, z)
    FF = fft!(δ, copy(FQ), 2d, -z)
    @test all(FF .== F * δ)
end

@testset "ffth $p" for p in (2, 3, 5)
    d, n = first(smallcases(p, 11, 100))
    pf = allpf(n)
    bf = revert.(0:n-1, Ref(pf)) .+ 1
    R = GF(p, d)
    x = monom(R)
    W = x^(order(x) ÷ n)
    @test order(W) == n
    F = x .^ (0:n-1)
    f = ffthf(n, F, W)
    ff = dft(n, F, W)
    @test f[bf] == ff
    FF = ffthb(n, f, W)
    dF = dft(n, f[bf], inv(W))
    @test FF == dF
    @test FF / n == F
end

end # module
