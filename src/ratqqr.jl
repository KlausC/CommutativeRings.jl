"""
    ratqqr(A)

For a `mxn` columns regular matrix `A` (m >= n)
calculate an orthogonal (not necessary orthonormal) matrix `Q` and an upper triangular
matrix `R` such that `Q * R` = `A`.

The calculations use only rational operations.
The diagonal elements of  `D = Q'Q` are kept in the rational interval `[1,4)`.
The ordinary `qr` factorization is related by `(Q / √D)' (Q / √D) = I` and
`(Q / √D) * (√D *R) = Q * R = A`.
"""
function ratqr!(A::AbstractMatrix{T}, r::AbstractVector{T}) where T
    m, n = size(A)
    m >= n || throw(ArgumentError("mxn-Matrix with m >= n required, but m = $m < $n = n"))
    if n != length(r)
        resize!(r, n)
    end

    k = 1
    qk = sum(abs2, A[:,k])
    xk = 2^(ilog2(qk) ÷ 2)
    r[k] = xk
    A[:,k] ./= xk

end

"""
    r1sqrt(a, n)
For given real `a` and `n > 0`, find a integers `b` (odd) and `k` so `a * b^2 * 2^-2k ≈ 1`,
were `b` isodd and `ilog2(b) <= n`.
"""
function r1sqrt(a::Real, n::Integer)
    m, x = frexp(float(a))
    x2 = fld(x, 2)
    m2 = isodd(x) ? m * 2 : m
    b = Integer(floor(sqrt(m2) * 2.0^n))
    b, x2
end
