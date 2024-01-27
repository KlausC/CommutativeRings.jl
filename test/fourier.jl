
module TestFourier
using CommutativeRings
using Test

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

@testset "fft! $(2^k)" for k = 1:8
    n = 2^k
    dd = 2^(k ÷ 2)
    z = Int(2 * dd / n)
    F = rand(1:100, n * dd)
    W = similar(F)
    FQ = fft!(n, copy(F), dd, z, W)
    FF = fft!(n, copy(FQ), dd, -z, W)
    @test all(FF .== F * n)
end

end # module
