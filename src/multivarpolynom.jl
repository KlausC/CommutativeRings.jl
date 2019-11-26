
# class constructors
# convenience type constructor:
# enable `R[:x,:y,:z,...]` as short for `MultivariatePolynomial{:X,R}`
function getindex(R::Type{<:Ring}, s::Symbol, t::Symbol...)
    vs = collect((s, t...))
    N = length(vs)
    Id = sintern((vs,R))
    new_class(MultivariatePolynomial{Id,N,R}, vs)
end


import Base: +, -, *, zero, one, ==

function zero(::Type{<:T}) where {Id,N,S,T<:MultivariatePolynomial{Id,N,S}}
    T(Int[], S[])
end
function one(::Type{<:T}) where {Id,N,S,T<:MultivariatePolynomial{Id,N,S}}
    T(Int[1], S[1])
end

-(p::T) where T<:MultivariatePolynomial = T(p.ind, -p.coeff)
-(a::T, b::T) where T<:MultivariatePolynomial = +(a, -b)
*(p::T, a::Integer) where T<:MultivariatePolynomial = T(p.ind, p.coeff .* a)
*(a::Integer, p::T) where T<:MultivariatePolynomial = T(p.ind, a .* p.coeff)
==(a::T, b::T) where T<:MultivariatePolynomial = a.ind == b.ind && a.coeff == a.coeff

function +(a::T...) where T<:MultivariatePolynomial
    n = length(a)
    n >  0 || throw(ArgumentError("+ requires at least one argument"))
    n == 1 && return a[1]
    c = similar(a[1].coeff)
    d = similar(a[1].ind)
    j = 0
    p = ones(Int, n)
    pm = [get(x.ind, 1, 0) for x in a]
    
    while true
        m = typemax(Int)
        imin = 0
        for i = 1:n
            ix = pm[i]
            if ix > 0 && ix < m
                m = ix
                imin = i
            end
        end
        imin == 0 && break
        cj = a[imin].coeff[p[imin]]
        p[imin] += 1
        pm[imin] = get(a[imin].ind, p[imin], 0)
        for i = imin+1:n
            if pm[i] == m
                cj += a[i].coeff[p[i]]
                p[i] += 1
                pm[i] = get(a[i].ind, p[i], 0)
            end
        end
        if !iszero(cj)
            j += 1
            if j > length(d)
                resize!(d, 2*j)
                resize!(c, 2*j)
            end
            d[j] = m
            c[j] = cj
        end
    end
    resize!(c, j)
    resize!(d, j)
    T(d, c)
end

function *(a::T, b::T) where {Id,N,T<:MultivariatePolynomial{Id,N}}
    m = length(a.ind)
    n = length(b.ind)
    m >= n || return *(b, a)
    n == 0 && return zero(T)

    c = similar(a.coeff)
    d = similar(a.ind)
    j = 0
    p = ones(Int, n)
    pm = [indexsum(a.ind[1], x, N) for x in b.ind]
    
    while true
        m = typemax(Int)
        imin = 0
        for i = 1:n
            ix = pm[i]
            if ix > 0 && ix < m
                m = ix
                imin = i
            end
        end
        imin == 0 && break
        cj = a.coeff[p[imin]] * b.coeff[imin]
        p[imin] += 1
        pm[imin] = indexsum(get(a.ind, p[imin], 0), b.ind[imin], N)
        for i = imin+1:n
            if pm[i] == m
                cj += a.coeff[p[i]] * b.coeff[i]
                p[i] += 1
                pm[i] = indexsum(get(a.ind, p[i], 0), b.ind[i], N)
            end
        end
        if !iszero(cj)
            j += 1
            if j > length(d)
                resize!(d, 2*j)
                resize!(c, 2*j)
            end
            d[j] = m
            c[j] = cj
        end
    end
    resize!(c, j)
    resize!(d, j)
    T(d, c)
end

#= Tuple mappings. See for reference:
https://stackoverflow.com/questions/26932409/compact-storage-coefficients-of-a-multivariate-polynomial
https://en.wikipedia.org/wiki/Combinatorial_number_system
=#

"""
    tuple2index(a)

bijective mapping from tuples of non-negative integers to positive integers.
"""
function tuple2index(a::AbstractVector{<:Integer})
    c = similar(a)
    d = length(a)
    d == 0 && return c + 1
    ci = s = sum = a[1]
    for i = 2:d
        s += a[i]
        ci = s + i - 1
        sum += binomial(ci, i)
    end
    sum + 1
end

"""
    index2tuple(n, d)

bijective mapping from integers to `d`-tuples of integers.

"""
function index2tuple(n::T, d::Int) where T<:Integer
    c = Vector{T}(undef, d)
    n < 1 && throw(ArgumentError("index must be positive but is $n"))
    n -= 1
    for i = d:-1:1
        ci, b = cbin(n, i)
        c[i] = ci
        n -= b
    end
    ci = c[d]
    for i = d:-1:2
        cp = c[i-1]
        c[i] = ci - cp - 1
        ci = cp
    end
    c
end

"""
Caculate the greatest integer `c` such that `binomial(c, d) <= n`
"""
function cbin(n::T, d::Int) where T<:Integer
    d <= 0 && throw(ArgumentError("tuple size > 0 required, but is $d"))
    d == 1 && return n, n
    n == 0 && return d-1, n
    n == 1 && return d, n
    c = T(floor((n * sqrt(2pi*d))^(1/d) * d / ℯ + d/2))
    if c <= d
        c = d
        b = T(1)
    else
        b = binomial(c, d)
    end
    b == n && return c, b
    bp = b
    while b <= n
        bp = b
        c += 1
        b = b * c ÷ (c-d)
    end
    b >= n > bp && return c-1, bp
    while b > n
        bp = b
        b = b * (c-d) ÷ c
        c -= 1
    end
    return c, b
end

function indexsum(x::T, y::T, d::Int) where T<:Integer
    x > 0 && y > 0 || return 0
    tuple2index(index2tuple(x, d) + index2tuple(y, d))
end
