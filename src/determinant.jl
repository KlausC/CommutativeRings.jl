
function LinearAlgebra.det(a::AbstractMatrix{D}) where D<:Ring
    checksquare(a)
    det!(copy(a))
end
det!(a::AbstractMatrix{D}) where D<:Union{Ring,Number} = _det(a, category_trait(D))

_det(a::AbstractMatrix, ::Type{<:IntegralDomainTrait}) = det_DJB!(a)
_det(a::AbstractMatrix{D}, ::Type{<:IntegralDomainTrait}) where D<:QuotientRing =
    det_DJB!(a)
_det(a::AbstractMatrix{D}, ::Type{<:CommutativeRingTrait}) where D<:QuotientRing =
    det_QR!(a)
_det(a::AbstractMatrix, ::Type{<:CommutativeRingTrait}) = det_Bird(a)

"""
    det_DJB(a::Matrix{D}) where D<:Union{Ring,Number}

This code is taken from "Algorithm 8.36 (Dogdson-Jordan-Bareiss)" of
"Algorithms in Real Algebraic Geometry" by Basu, Pollak, Roy - 2016.

Its use is restricted to the case of `D` an integral domain.
"""
det_DJB(a::AbstractMatrix{D}) where D<:Union{Ring,Number} = det_DJB!(copy(a))

function det_DJB!(b::AbstractMatrix{D}) where D<:Union{Ring,Number}
    n = checksquare(b)
    @assert category_trait(D) <: IntegralDomainTrait
    b00 = one(D)
    n == 0 && return b00
    s = 1
    for k = 1:n-1
        j0 = 0
        for j = k:n
            if !iszero(b[k, j])
                j0 = j
                break
            end
        end
        if j0 == 0
            return zero(D)
        end
        if j0 != k
            for i = k:n
                b[i, j0], b[i, k] = b[i, k], b[i, j0]
            end
            s = -s
        end
        bkk = b[k, k]
        for i = k+1:n
            bik = b[i, k]
            b[i, k] = 0
            for j = k+1:n
                bkj = b[k, j]
                bij = b[i, j]
                b[i, j] = div(bkk * bij - bik * bkj, b00)
            end
        end
        b00 = bkk
    end
    return b[n, n] * s
end

"""
    det_QR(a::Matrix{D}) where D<:QuotientRing

This code is an extension of det_DJB to certain quotient rings which are domains.
I.e. `ZZ/p` where `p` is not prime and `P[:x]/q` where `q` is the product of polynomials.
"""
det_QR(a::AbstractMatrix{D}) where {Z,D<:QuotientRing{Z}} = det_QR!(copy(a))

function det_QR!(b::AbstractMatrix{D}) where {Z,D<:QuotientRing{Z}}
    n = checksquare(b)
    s = one(D)
    n == 0 && return s

    for k = 1:n-1
        a = view(b, k:n, k:n)
        ij = findfirst(isunit, a)
        if ij !== nothing
            ij += CartesianIndex(k - 1, k - 1)
            s = flipall!(b, ij, k, s)
        else
            for i = k:n
                ij, s = rowdivgcd!(b, i, k, ij, s)
                iszero(s) && return s
            end
            if ij !== nothing
                s = flipall!(b, ij, k, s)
            else
                # now no element of `a` is unit - all have common divisors with `m`
                m = modulus(D)
                ij = findfirst(!iszero, a)
                u = value(a[ij])
                v, w = splitmod(u, m)
                # println("splitmod($u, $m) = $v, $w")
                @assert v != m && w != m
                ZV = Quotient(v, Z)
                dv = det!(ZV.(a))
                isone(w) && return dv
                ZW = Quotient(w, Z)
                dw = det!(ZW.(a))
                return _crt(D(value(dv)), D(value(dw)), v, w) * s
            end
        end
        bkk = one(D)
        for i = k+1:n
            bik = b[i, k]
            for j = k+1:n
                bkj = b[k, j]
                bij = b[i, j]
                b[i, j] = bkk * bij - bik * bkj
            end
        end
    end
    return b[n, n] * s
end

function flipall!(a::AbstractMatrix, ij::CartesianIndex, k, s)
    # println("flipall($ij, $k)")
    # display(a)
    i, j = ij[1], ij[2]
    if i != k
        s = -s
        for u = k:size(a, 2)
            a[i, u], a[k, u] = a[k, u], a[i, u]
        end
    end
    if j != k
        s = -s
        for u = k:size(a, 1)
            a[u, j], a[u, k] = a[u, k], a[u, j]
        end
    end
    akk = a[k, k]
    if isunit(akk)
        for u = k:size(a, 2)
            # println("a[$k,$u] / akk == $(a[k,u]) / $akk = $(a[k,u] / akk)")
            a[k, u] /= akk
        end
        s *= akk
    end
    # println("k = $k:")
    # display(a)
    s
end

"""
    rowdivgcd!(b::Matrix, i, k, ij, s)

Divide row `b[i,k::end]` by the gcd of that row.
Return gcd, index of a now unit element of the row, s * gcd
"""
function rowdivgcd!(b::AbstractMatrix{D}, i, k, ij, s) where {Z,D<:QuotientRing{Z}}
    n = size(b, 2)
    g = gcd_generator(value(b[i, j]) for j = k:n)
    s *= g
    if !isone(g) && !iszero(g)
        for j = k:n
            bij = D(value(b[i, j]) ÷ g)
            b[i, j] = bij
            if ij === nothing && isunit(bij)
                ij = CartesianIndex(i, j)
            end
        end
    end
    ij, s
end

"""
    crt(x, y, p, q)

Chinese remainder theorem.
Given `x, y, p, q` with `gcd(p, q) == 1`,
return `0 <= z < lcm(p, q)` with 'mod(z - x, p) == 0` and `mod(z - y, q) == 0`.
The result type is widened to avoid overflows.
"""
function crt(x, y, p, q)
    g, c = _crt2(widen(x), widen(y), p, q)
    mod(c, div(widen(p) * widen(q), g))
end
_crt(x, y, p, q) = _crt2(x, y, p, q)[2]
function _crt2(x, y, p, q)
    g, u, v = gcdx(p, q)
    g, y * u * p + x * v * q
end
"""
    v = splitmod(a, m)

Find `v` which divides `m` in a way that `gcd(v, m/v) == 1`.
The input `a < m` with `gcd(a, m) != 1 serves as a starting point.
"""
function splitmod(v, m)
    a = gcd(v, m)
    @assert 1 < a < m
    b = m ÷ a
    x = 1

    while !isone(b)
        g = gcd(a, b)
        if !isone(g)
            b ÷= g
            x += 1
        else
            break
        end
        v = g
    end
    a = v^x
    b = m ÷ a
    a, b
end

"""
    det_Bird(a::Matrix{D}) where D

This is a division-free algorithm to calculate the determinant of `a`.
There are no conditions on `D` except it is a non-empty commutative ring with one.
Derived from "Pearls of Functional Algorithm Design, chap. 22" by Richard Bird - 2010
"""
det_Bird(a::AbstractMatrix{D}) where D = det_Bird!(copy(a), a)
function det_Bird!(x::AbstractMatrix{D}, a::AbstractMatrix{D}) where D
    n = checksquare(x)
    n == 0 && return one(D)
    for k = n-1:-1:1
        mutx!(x, k, a)
    end
    isodd(n) ? x[1, 1] : -x[1, 1]
end

function mutx!(x::AbstractMatrix, k::Integer, a::AbstractMatrix{T}) where T
    # assuming size(x) == size(a) == (n, n) && 0 < k < n
    n = size(a, 1)
    for j = 1:n
        for i = j+1:n
            x[i, j] = 0
        end
    end
    s = -x[k+1, k+1]
    x[k+1, k+1] = 0
    for j = k:-1:1
        xjj = x[j, j]
        x[j, j] = s
        s -= xjj
    end
    s = zero(T)
    for l = k:n
        s += x[k, l] * a[l, k]
    end
    x[k, k] = s
    for j = k+1:n
        x[k, j] = 0
    end
    for i = k-1:-1:1
        for j = i:n
            x[j, 1] = x[i, j]
        end
        for j = n:-1:1
            s = zero(T)
            for l = i:n
                s += x[l, 1] * a[l, j]
            end
            x[i, j] = s
        end
        for j = i+1:n
            x[j, 1] = 0
        end
    end
    x
end

"""
    det_MV(a)

Divisionfree combinatoric algorithm to calculate determinant.
"Determinant: Combinatorics, Algorithms, andComplexity" by Mahajan, Vinay
in Chicago Journal of Theoretical Computer Science1997-5
http://cjtcs.cs.uchicago.edu/articles/1997/5/cj97-05.pdf
"""
function det_MV(a::AbstractMatrix{D}) where D<:Union{Ring,Integer}
    n = checksquare(a)
    A1 = zeros(D, n, n)
    A2 = zeros(D, n, n)
    B1 = zeros(D, n, n)
    B2 = zeros(D, n, n)
    p = n & 1 + 1
    for u = 1:n
        (p == 1 ? A1 : A2)[u, u] = one(D)
    end
    for i = 0:n-2
        for u = 1:n
            for v = u:n
                Auvp = A1[u, v]
                if !iszero(Auvp)
                    for w = u+1:n
                        #println("addpush(0, $u, $w, $(Auvp*a[v,w]))")
                        B1[u, w] += Auvp * a[v, w]
                        #println("addpush(1, $w, $w, $(Auvp * a[v,u]))")
                        B2[w, w] += Auvp * a[v, u]
                    end
                end
                Auvp = A2[u, v]
                if !iszero(Auvp)
                    for w = u+1:n
                        #println("addpush(1, $u, $w, $(Auvp*a[v,w]))")
                        B2[u, w] += Auvp * a[v, w]
                        #println("addpush(0, $w, $w, $(Auvp * a[v,u]))")
                        B1[w, w] += Auvp * a[v, u]
                    end
                end
            end
        end
        A1, B1 = B1, A1
        A2, B2 = B2, A2
        fill!(B1, zero(D))
        fill!(B2, zero(D))
        #println("i = $i")
        #display([A1 A2])
    end

    for u = 1:n
        for v = u:n
            avu = a[v, u]
            if !iszero(avu)
                B1[1, 1] += A1[u, v] * avu
                B2[1, 1] += A2[u, v] * avu
            end
        end
    end
    B2[1, 1] - B1[1, 1]
end


#TODO normal forms to dedicated file
"""
    hermite_normal_form(A::AbstractMatrix; column_style=true, round=RoundUp) -> H, U

Calculate matrixes `H` in column/row Hermite normal form and unimodular `U` and
 `if column_style; A * U else U * A end == H`.
Unimodular means `det(U)` is unit element of the ring `R`.

`H` is lower triangular, if `column_style`, else upper triangular.
The off-pivot elements in a row (if `column_style`) or else column are strictly smaller than
the pivot elements, which are not negative.
The off-pivot elements are non-negative, non-positive, minimal-abs, maximum-abs depending
on `round` in `(RoundDown, RoundUp, RoundToZero, RoundFromZero)` correspondingly.

See [Wiki](https://en.wikipedia.org/wiki/Hermite_normal_form)
[Algorithm](https://www.math.tamu.edu/~rojas/kannanbachemhermitesmith79.pdf)

The algorithm was generalized to matrices of arbitrary rank and shape.
"""
function hermite_normal_form(
    a::AbstractMatrix{R};
    column_style::Bool = true,
    round::RoundingMode = RoundUp,
) where R<:Union{Ring,Integer}
    m, n = size(a)

    if column_style
        u = Matrix(R.(I(n)))
        hermite_normal_form!(copy(a), u, round)
    else
        u = Matrix(R.(I(m)))
        H, U = hermite_normal_form!(copy(permutedims(a)), u, round)
        permutedims(H), permutedims(U)
    end
end

function hermite_normal_form!(
    a::AbstractMatrix{R},
    u::AbstractMatrix{R},
    round::RoundingMode,
) where R
    m, n = size(a)
    piv = something.(findfirst.(!iszero, eachcol(a)), m + 1)
    n = something(findlast(x -> x <= m, piv), 0)
    i = 1
    while i <= n
        while i < n && piv[i] > m
            swap(a, i, n)
            swap(u, i, n)
            swap(piv, i, n)
            n -= 1
        end
        if i <= n
            for j = 1:i-1
                pj = piv[j]
                pi = piv[i]
                if pj > pi
                    swap(a, j, i)
                    swap(u, j, i)
                    swap(piv, j, i)
                    reduce_off_diagonal!(a, u, j, piv, round)
                elseif pi == pj && pi <= m
                    ajj = a[pj, j]
                    aji = a[pj, i]
                    r, q, p, qq, pp = gcdex(aji, ajj)
                    for k = 1:m
                        akj = a[k, j]
                        aki = a[k, i]
                        bkj = akj * p + aki * q
                        bki = akj * pp + aki * qq
                        a[k, j] = bkj
                        a[k, i] = bki
                    end
                    for k = 1:size(u, 1)
                        akj = u[k, j]
                        aki = u[k, i]
                        bkj = akj * p + aki * q
                        bki = akj * pp + aki * qq
                        u[k, j] = bkj
                        u[k, i] = bki
                    end
                    piv[i] = something(findfirst(!iszero, view(a, 1:m, i)), m + 1)
                    reduce_off_diagonal!(a, u, j, piv, round)
                end
            end
        end
        reduce_off_diagonal!(a, u, i, piv, round)
        i += 1
    end
    a, u
end

function gcdex(a, b)
    r, p, q = gcdx(a, b)
    pp = -div(b, r)
    qq = div(a, r)
    r, p, q, pp, qq
end

function swap(a::AbstractMatrix, i, j)
    m = size(a, 1)
    for k = 1:m
        b = a[k, i]
        a[k, i] = a[k, j]
        a[k, j] = b
    end
end
function swap(a::AbstractVector, i, j)
    a[i], a[j] = a[j], a[i]
end

function reduce_off_diagonal!(a, u, k, piv, round)
    pk = piv[k]
    pk > size(a, 1) && return
    akk = a[pk, k]
    if akk < 0
        akk = -akk
        a[:, k] .= -a[:, k]
        u[:, k] .= -u[:, k]
    end
    for z = 1:k-1
        d = div(-a[pk, z], akk, round)
        a[:, z] .+= a[:, k] .* d
        u[:, z] .+= u[:, k] .* d
    end
end

#
# u, v unimodular, d diagonal with mod(d[i+1,i+1], d[i,i]) == 0
# u * a * v = d
function smith_normal!(a::AbstractMatrix, u::AbstractMatrix, v::AbstractMatrix)
    b = copy(a)
    m, n = size(a)
    m == size(u, 1) || throw(DimensionMismatch("left square matrix"))
    n == size(v, 2) || throw(DimensionMismatch("right square matrix"))
    i = 1
    while i <= min(m, n)
        A = view(a, i:m, i:n)
        U = view(u, i:m, 1:size(u, 2))
        V = view(v, 1:size(v, 1), i:n)

        hermite_normal_form!(A, V, RoundUp)
        swap_zero_rows!(A, U)
        stop = false
        while !stop
            hermite_left!(A, U)
            hermite_normal_form!(A, V, RoundUp)
            stop = is_unit_column(A)
            if stop
                k = first_non_multiple_column(A)
                stop = k == 0
                if k > 1
                    A[:, 1] .+= A[:, k]
                    V[:, 1] .+= V[:, k]
                end
            end
        end
        i += 1
    end
    u, a, v
end

function hermite_left!(a, u)
    m, n = size(a)
    j = 1
    for i = 2:m
        aij = a[i, j]
        iszero(aij) && continue
        ajj = a[j, j]
        g, q, p, qq, pp = gcdex(aij, ajj)
        for k = 1:n
            akj = a[j, k]
            aki = a[i, k]
            bkj = akj * p + aki * q
            bki = akj * pp + aki * qq
            a[j, k] = bkj
            a[i, k] = bki
        end
        for k = 1:size(u, 2)
            akj = u[j, k]
            aki = u[i, k]
            bkj = akj * p + aki * q
            bki = akj * pp + aki * qq
            u[j, k] = bkj
            u[i, k] = bki
        end
    end
end

function swap_zero_rows!(A, U)
    m, n = size(A)
    k = 1
    while k <= m && iszero(A[k, 1])
        k += 1
    end
    if k > 1
        for j = k:m
            A[j-k+1, :] .= A[j, :]
            A[j, :] .= 0
            for i = 1:size(U, 2)
                ukk = U[j-k+1, i]
                U[j-k+1, i] = U[j, i]
                U[j, i] = ukk
            end
        end
    end
end

function is_unit_column(A)
    iszero(A[2:size(A, 1), 1])
end

function isunit(a::Integer)
    abs(a) == 1
end

function first_non_multiple_column(A)
    m, n = size(A)
    akk = A[1, 1]
    for j = 1:n
        for i = j:m
            aij = A[i, j]
            iszero(aij) || iszero(mod(aij, akk)) || return j
        end
    end
    return 0
end
