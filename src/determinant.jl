
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


#TODO fix algorithm. normal forms to dedicated file
"""
    hermite_normal_form(A::AbstractMatrix{R}) where R<:Ring -> H, U

Calculate matrixes `H` in column Hermite normal form and unimodular `U` with `A * U = H`.
Unimodular means `det(U)` is unit element of the ring `R`.

See [Wiki](https://en.wikipedia.org/wiki/Hermite_normal_form)
[Algorithm](https://www.math.tamu.edu/~rojas/kanna?nbachemhermitesmith79.pdf)
"""
function hermite_normal_form(a::Matrix{R}) where R<:Union{Ring,Integer}
    m, n = size(a)
    u = Matrix(R.(I(n)))
    hermite_normal_form!(copy(a), u)
end

function hermite_normal_form!(a::Matrix{R}, u::Matrix{R}) where R
    m, n = size(a)

    for i = 1:min(m, n)-1
        for j = 1:i
            ajj = a[j, j]
            aji = a[j, i+1]
            r, p, q = gcdx(ajj, aji)
            #@assert max(abs(p), abs(q)) <= max(abs(ajj), abs(aji))
            pp = -div(aji, r)
            qq = div(ajj, r)
            for k = 1:m
                akj = a[k, j]
                aki = a[k, i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                a[k, j] = bkj
                a[k, i+1] = bki
            end
            for k = 1:n
                akj = u[k, j]
                aki = u[k, i+1]
                bkj = akj * p + aki * q
                bki = akj * pp + aki * qq
                u[k, j] = bkj
                u[k, i+1] = bki
            end
            reduce_off_diagonal!(a, u, j)
        end
        reduce_off_diagonal!(a, u, i + 1)
    end
    a, u
end

function reduce_off_diagonal!(a, u, k)
    akk = a[k, k]
    if akk < 0
        akk = -akk
        a[:, k] .= -a[:, k]
        u[:, k] .= -u[:, k]
    end
    for z = 1:k-1
        d = cld(a[k, z], akk)
        a[:, z] .-= a[:, k] .* d
        u[:, z] .-= u[:, k] .* d
    end
end

Base.cld(a::T, b::T) where T<:ZZ = T(cld(value(a), value(b)))
Base.fld(a::T, b::T) where T<:ZZ = T(fld(value(a), value(b)))
Base.cld(a::T, b::T) where T<:Ring = div(a, b)
Base.fld(a::T, b::T) where T<:Ring = div(a, b)
