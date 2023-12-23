
# Implementation of an accurate floating point variant of LLL () algorithm.
# Based on:
# Phong Q. Nguyên and Damien Stehlé: Floating-Point LLL Revisited (2005)
# [paper](https://link.springer.com/content/pdf/10.1007/11426639_13.pdf)

function ll_reduce(B::AbstractMatrix{T}, δ::Real = 0.99, η::Real = 0.51) where T<:Integer
    ll_reduce!(copy(B), δ, η)
end
function ll_reduce!(B::AbstractMatrix{T}, δ::Real, η::Real) where T<:Integer
    0.25 < δ < 1 || throw(ArgumentError("need δ in (0.25,1), but was $δ"))
    0.25 <= η^2 < δ || throw(ArgumentError("need η in (0.5, $(sqrt(δ)), but was $η"))

    d = size(B, 2)
    I = gram_type(B)
    l = req_precision(δ, η, d)
    if l <= precision(Float64)
        ll_reduce!(B, δ, η, Float64, I)
    else
        B, = call_repeatedly(ll_reduce!, B, δ, η, Float64, I)

        setprecision(BigFloat, l) do
            ll_reduce!(B, δ, η, BigFloat, I)
        end
    end
end

function ll_reduce!(B::AbstractMatrix, δ, η, ::Type{F}, ::Type{I}) where {I<:Integer,F}
    """
    Input: A valid pair (δ, η) like in Th. 1, a basis [b1,..., bd] and a fp-precision F.
    Output: An L3-reduced basis with factor pair (δ, η).
    Variables: A matrix G, two d × d fp-matrices (¯r[i,j] ) and (¯μ[i,j] ), a fp-vector ¯s.
    """
    d = size(B, 2)

    # 1. Compute exactly G = G(b1, . . . , bd).
    G = zeros(I, d, d)
    r = zeros(F, d, d)
    μ = r
    s = zeros(F, d)
    for i = 1:d
        for j = 1:i
            g = zero(I)
            for k in axes(B, 1)
                g += B[k, i]' * oftype(g, B[k, j])
            end
            G[i, j] = g
        end
    end
    # 2. ¯δ:= (δ + 1) / 2
    δ = (δ + 1.0) * 0.5
    # 2 , ¯r[1,1] := (〈b1, b1〉), κ:=2. While κ ≤ d, do
    r[1, 1] = G[1, 1]
    # μ[1, 1] = 1
    k = 2
    while k <= d
        # 3. Size-reduce bκ using the algorithm of Fig. 5. It updates the fp-GSO.
        babai_nearest_plane!(G, B, r, μ, s, k, η)
        # 4. κ′:=κ. While κ ≥ 2 and ¯δ¯r[κ−1,κ−1] ≥ ¯s[κ−1], do κ:=κ − 1.
        m = k
        while k >= 2 && δ * r[k-1, k-1] >= s[k-1]
            k -= 1
        end
        if k < m
            # 5. For i = 1 to κ − 1 do ¯μ[κ,i]:=¯μ[κ′,i], ¯r[κ,i] :=¯r[κ′,i], ¯r[κ,κ]:=¯s[κ].
            for i = 1:k-1
                μ[k, i] = μ[m, i]
                r[i, k] = r[i, m]
            end
            r[k, k] = s[k]
            # 6. Insert bκ′ right before bκ and update G accordingly.
            cyclic_shift!(B, G, k, m)
        end
        #@assert LowerTriangular(B' * I.(B)) == G
        #dev = LowerTriangular(LowerTriangular(r)*UnitLowerTriangular(μ)')
        #@assert dev[1:k, 1:k] ≈ G[1:k, 1:k]
        # 7. κ:=κ + 1.
        k += 1
    end
    #8. Output [b1, ... , bd] and r
    B, r
end

function babai_nearest_plane!(G, B::AbstractMatrix{T}, r, μ, s, k::Integer, η) where T
    """
    Input: A factor η > 1/2, a fp-precision l, an integer κ, a basis [b1,..., bd],
    G(b1,..., bd), and fp numbers ¯r[i,j] and ¯μ[i,j] ’s for j ≤ i < κ.
    Output: fp numbers ¯r[κ,j] , ¯μ[κ,j] and ¯s[j] for j ≤ κ, [b1,..., bκ−1, b′κ, bκ+1, ... , bd] ,
    and G(b1,..., bκ−1, b′κ, bκ+1,..., bd) where b′κ = bκ − ∑i<κ x[i]*b[i]
    for some integers x[i]’s and: |〈b′κ, b∗i〉| ≤ η ‖b∗i‖^2 for any i < κ.
    """
    d = size(G, 1)
    # 1. ¯η:= (η + 1/2) / 2
    η = (η + 0.5) * 0.5
    # 2 . Repeat
    reduce = true
    while reduce
        reduce = false
        # 2. Compute the ¯r[κ,j] ’s, ¯μ[κ,j] ’s, ¯s[j] ’s with Steps 2–7 of the CFA with “i = κ”.
        # assuming (r*μ)[1:k-1,1:k-1] is Cholesky decomposition of G, (re-)calculate for 1:k
        CFA!(r, μ, s, G, k)
        # 3. For i = κ − 1 downto 1 do
        for i = k-1:-1:1
            μki = μ[k, i]
            xi = abs(μki) >= η ? T(round(μki)) : T(0)
            if xi != 0
                #println("before babai($k,$i): $(norm(LowerTriangular(B'B)-G))")
                B[:, k] .-= B[:, i] * xi
                G[k, 1:i-1] .-= G[i, 1:i-1] * xi'
                G[k, i:k] .-= G[i:k, i] * xi'
                G[k:d, k] .-= G[k:d, i] * xi
                reduce = true
                #println("after  babai($k,$i): $(norm(LowerTriangular(B'B)-G))")
            end
        end
    end
    nothing
end

# r μ' is a Cholesky decomposition of G in 1:k-1
# afterwards it is a decomposition in 1:k
# entries after k in r and μ are invalid(ated)
# s[1:k] is filled by s[1]:= G[k,k]. For j = 2 to d do s[j] :=s[j−1] − μ[k,j] * r[k,j]
function CFA!(r::S, μ::S, s, G, k::T) where {T<:Integer,F,S<:AbstractMatrix{F}}

    #dev = LowerTriangular(LowerTriangular(r) * UnitLowerTriangular(μ)') - G
    #println("before CFA $k: $(norm(dev[1:k-1,1:k-1])) should be zero")

    for j = 1:k-1
        rkj = F(G[k, j])
        for m = 1:j-1
            rkj -= r[m, k] * μ[j, m]
        end
        r[j, k] = rkj
        μ[k, j] = rkj / r[j, j]
    end
    s0 = float(G[k, k])
    s[1] = s0 # s0 is higher precision than s
    for j = 1:k-1
        s0 -= μ[k, j] * r[j, k]
        s[j+1] = s0
    end
    #r[k+1:end, :] .= 0
    #μ[k+1:end, :] .= 0
    #s[k+1:end] .= 0

    r[k, k] = s0
    #dev = LowerTriangular(LowerTriangular(r) * UnitLowerTriangular(μ)') - G
    #println("after  CFA $k: $(norm(dev[1:k,1:k])) should be zero")
    nothing
end

# B[:,k], B[:,k+1],...B[:,m] := B[:,m], B[:,k], ... B[:,m-1]
# assert k < m
function cyclic_shift!(B, G, k, m)
    #println("before shift($k,$m): $(norm(LowerTriangular(B'B)-G))")
    d = size(B, 2)
    for j in axes(B, 1)
        a = B[j, m]
        for i = m:-1:k+1
            B[j, i] = B[j, i-1]
        end
        B[j, k] = a
    end
    for j = 1:k-1
        g = G[m, j]
        for i = m:-1:k+1
            G[i, j] = G[i-1, j]
        end
        G[k, j] = g
    end
    for j = m+1:d
        g = G[j, m]
        for i = m:-1:k+1
            G[j, i] = G[j, i-1]
        end
        G[j, k] = g
    end
    for j = k:m
        g = G[m, m+k-j]
        for i = m:-1:j+1
            G[i, i+k-j] = G[i-1, i+k-j-1]
        end
        G[j, k] = g
    end
    for j = k+1:k+(m-k)÷2
        G[j, k], G[m+k-j+1, k] = G[m+k-j+1, k], G[j, k]
    end
    #println("after  shift($k,$m): $(norm(LowerTriangular(B'B)-G))")
end

# requested precision of fp operations to achieve exact result
function req_precision(δ, η, d)
    c = log2((1 + η)^2 / (δ - η^2))
    Int(ceil(c * d)) + 1
end

# find smallest integer type to hold Gram matrix of B
function gram_type(B::AbstractMatrix{T}) where T<:Integer
    g = maximum(sum(x -> abs2(float(x)), B; dims = 1))
    G = BigInt
    for t in (Int64, Int128)
        if typemax(t) > g
            G = t
            break
        end
    end
    G
end

"""
    lll_repeated(A, result=[]; imax, igap)

Repeatedly call `C, = lll_reduce(B)`, initially with `B = A`, then `B = C[:,pcol]`,
where `pcol` is a permutation of the columns of `C`.
Record all suboptimal solutions of `norm(C, 1)` in `result`.
Stop iteration as soon as after `igap` iterations the optial value did not change,
at most `imax iterations`.
"""
function lll_repeated(A, res = []; igap=1000, imax=igap*10)
    if isempty(res)
        i = 0
        pr = collect(1:size(A, 2))
        n = norm(A, 1)
        push!(res, (A, diagm(ones(Int, size(A, 2))), n, i, pr))
    end
    A, R, n, i, pr = res[end]
    i0 = i
    while n > 0 && i < i0 + igap && i <= imax
        i += 1
        p = randperm(length(diag(R)))
        B, R = ll_reduce(A[:, p])
        nn = norm(B, 1)
        if nn < n
            i0 = i
            pr = pr[p]
            A = B
            n = nn
            push!(res, (A, R, nn, i, pr))
            println("opt at $i: $nn $(norm(A, 2)) $(norm(A, Inf))")
        end
    end
    res
end

"""
    randlattice([rng,] n, p)

Create "random" nxn - integer lattice base with maximal entry of `p`.
Result is the matrix of columns of the base.
"""
function randlattice(rng, n, p::T) where T
    r = rand(rng, 1:p-1, n-1)
    [p r'; zeros(T, n-1) diagm(ones(T, n-1))]
end
randlattice(n, p) = randlattice(Random.default_rng(), n, p)

"""
    randm([rng,], n::Int, k::Int, r, T) where T<:Integer

Create "random" integer unimodal nxn transformation matrix `M` by repeatedly compose
elementary operations (add multiple of column `i` to column `j`).

The number of operations is limited by `k`, and `norm(M, Inf) <= rmax`. The elemental
multiplicity is restricted by `max(1, r / norm(M, Inf))` at every step.
"""
function randm(rng::AbstractRNG, n::Int, rmax::T, lim, imax::Int) where T<:Integer
    M = Matrix(T(1)*I(n))
    v = Vector{T}(undef, n)
    for _ = 1:imax
        j1, j2 = rand(rng, 1:n, 2)
        if j1 != j2
            f = false
            rm = maximum(abs, M)
            rm > rmax && break
            s = max(Int(ceil( lim / rm)), 1)
            x = T(rand(rng, -s:s))
            if !iszero(x)
                for i in axes(M, 1)
                    r, f = mul_with_overflow(M[i,j2], x)
                    f && break
                    r, f = sub_with_overflow(M[i,j1], r)
                    f && break
                    v[i] = r
                end
                f && break
                M[:,j1] .= v
            else
                for i in axes(M, 1)
                    M[i,j1], M[i,j2] = M[i,j2], M[i,j1]
                end
            end
        end
    end
    M
end
randm(n, rmax, lim=1, imax=n^2) = randm(Random.default_rng(), n, rmax, lim, imax)
export ll_reduce, randm, randlattice

function gauss_reduce2!(a::AbstractVector{T}, b::AbstractVector{T}) where T
    Ti = typeof(Integer(zero(T)))
    na, nb = dot(a, a), dot(b, b)
    swi = false
    maybe_changed = false
    changed = false
    while na != nb
        changed = maybe_changed
        swi = na > nb
        if swi
            a, b = b, a
            na, nb = na, nb
        end
        m = Ti(round(dot(a, b) / na))
        iszero(m) && break
        b .-= a .* m
        nb = dot(b, b)
        maybe_changed = true
    end
    changed
end

function gauss_reduce!(A::Matrix{T}) where T
    for i in axes(A, 2)
        changed = true
        while changed
            p = sortperm(vec(sum(abs2, A, dims = 1)))
            A = A[:,p]
            changed = false
            for j in i+1:size(A, 2)
                changed |= gauss_reduce2!(view(A, :, i), view(A, :, j))
            end
        end
    end
    A
end
