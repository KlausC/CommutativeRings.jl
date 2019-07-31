
ZZmod{m}(a::T) where {m,T} = m > 0 ? ZZmod{m,T}(mod(a, T(m))) : throw(DomainError(m, "modulus > 0 required."))
ZZmod(a::T, m::S) where {T,S} = ZZmod{m}(S(a))

function +(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T}
    s = a.val + b.val
    ZZmod{m,T}(0 <= s < m ? s : s - m)
end
function -(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T}
    s = a.val - b.val
    ZZmod{m,T}(s >= 0 ? s : s + m)
end
function -(a::ZZmod{m,T}) where {m,T}
    ZZmod{m,T}(m - a.val)
end
function *(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T}
    p, ov = Base.mul_with_overflow(a.val, b.val)
    ov || return ZZmod{m,T}(mod(p, m))
    ZZmod{m,T}(T(mod(widemul(a.val, b.val), m)))
end
function inv(a::ZZmod{m,T}) where {m,T}
    g, x, y = gcdx(a.val, m)
    g == 1 || throw(DomainError((val.a, m), "gcd is $g."))
    if x < 0
        x += m
    end
    ZZmod{m,T}(x)
end
function /(a::ZZmod, b::ZZmod)
    iszero(b.val) && throw(DivisionError())
    a * inv(b)
end
function ^(a::ZZmod{m,T}, n::Integer) where {m,T}
    ZZmod{m,T}(powermod(a.val, n, m))
end

