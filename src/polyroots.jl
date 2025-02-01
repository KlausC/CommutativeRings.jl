
"""
    qfactor(p:UnivariatePolynomial{QQ})

Return a quadratic factor of the real polynomial `p`, close to initial estimation.
"""
function qfactor(p::UnivariatePolynomial{T}, v1::R, u1::R) where {T,R<:AbstractFloat}
    u, v = u1, v1
    n = deg(p) + 1
    m = isodd(n) ? n : n + 1
    c = Vector{R}(undef, m)
    c[1] = zero(R)
    c[m-n+1:m] .= value.(coeffs(p))
    i = 0
    while i < 100
        f, df = qderive(c, v, u)
        desc, dvu = descend(f, df)
        f0norm = norm(f)
        step = 1
        u0, v0 = u, v
        while step < 100
            v = v0 - dvu[1] / step
            u = u0 - dvu[2] / step
            f1, _ = qderive(c, v, u)
            f1norm = norm(f1)
            if f1norm <= f0norm - desc / step
                break
            end
            step = step * 2
        end
        i += 1
    end
    return v, u
end

function descend(f, df)
    R = eltype(f)
    luf = lu(df; allowsingular = true)
    if issuccess(luf)
        dvu = luf \ f
    else
        println(df)
        if norm(df) <= eps()
            dvu = randn(R, 2) * sqrt(eps(R))
        else
            dvu = pinv(df) \ f
        end
    end
    desc = 2 * dot(f, df * dvu)
    if desc < 0
        desc = -desc
        dvu .*= -1
    end
    f0 = norm(f)
    if desc > f0 * 3
        desc /= desc
        dvu ./= desc
    end
    desc, dvu
end

"""
    qderive(p::Vector, u, v)

Return the remainder term dividing p by (x² + u * x + v), the parameters of a linear and
its partial derivative by `u` and `v`.
"""
function qderive(p::AbstractVector{T}, v::T, u::T) where T<:AbstractFloat
    m = size(p, 1)
    if m < 3
        if m == 2
            return a[1:2], zeros(T, 2, 2)
        elseif m == 1
            return [a[1]; 0], zeros(T, 2, 2)
        else
            return zeros(T, 2), zeros(T, 2, 2)
        end
    end
    a1, a2 = p[m], p[m-1]
    au1, au2, av1, av2 = zeros(T, 4)
    for n = m-2:-1:1
        a0, a1, a2 = a1, a2, p[n]
        au0, au1, au2 = au1, au2, zero(T)
        av0, av1, av2 = av1, av2, zero(T)
        a1 -= a0 * u
        a2 -= a0 * v
        au1 -= au0 * u + a0
        au2 -= au0 * v
        av1 -= av0 * u
        av2 -= av0 * v + a0
    end
    return [a1, a2], [av1 au1; av2 au2]
end
