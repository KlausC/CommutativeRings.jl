
gz(u::T, v::T) where T<:Signed = _ggz(u, v, gy)
gz1(u::T, v::T) where T<:Signed = _ggz(u, v, gy1)
function _ggz(u::T, v::T, gg::Function) where T<:Integer
    su = signbit(u) ? -T(1) : T(1)
    sv = signbit(v) ? -T(1) : T(1)
    k = min(trailing_zeros(u), trailing_zeros(v))
    u >>= k; v>>= k
    uu = reinterpret(unsigned(T), u)
    vv = reinterpret(unsigned(T), v)
    s, x, y = gg(uu, vv)
    s, x, y = s % T, x % T, y % T
    vs = div(v, s)
    us = div(u, s)
    ws, xy = u<<1 > u ? (vs + us, x - y) : (midpoint(vs, us), midpoint(x, -y))
    q = div(ws>>1 + xy, ws)
    x -= q*vs; y += q * us
    checked_abs(s<<k), su * x, sv * y
end

function _gz(u::T, v::T, gg::Function) where T<:Signed
    su = signbit(u) ? -T(1) : T(1)
    sv = signbit(v) ? -T(1) : T(1)
    dx = dy = T(0)
    iszero(v) && return checked_abs(u), su, T(0)
    iszero(u) && return checked_abs(v), T(0), sv
    k = min(trailing_zeros(u), trailing_zeros(v))
    u >>= k; v>>= k
    u = abs(u); v = abs(v)
    sw = gg == gy1 && !isodd(v)
    if sw
        u, v = v, u
    end
    if u < 0
        u = u - v
        dy = T(1)
    end
    if v < 0
        v = v - u
        dx = T(1)
    end
    s, x, y = gg(u, v)
    x, y = x - dx * y, y - dy * x
    vs = div(v, s)
    us = div(u, s)
    ws, xy = u<<1 > u ? (vs + us, x - y) : (midpoint(vs, us), midpoint(x, -y))
    q = div(ws>>1 + xy, ws)
    x -= q*vs; y += q * us
    if sw
        x, y = y, x
    end
    checked_abs(s<<k), su * x, sv * y
end

function gy(u::T, v::T) where T<:Integer
    @assert u >= 0 && v >= 0
    n = UInt8(sizeof(T)*8 -1)
    u1, u2, u3 = oneunit(T), zero(T), u
    v1, v2, v3 = v, u - u1, v
    t1, t2, t3, tpos = iseven(u) ? (u1, u2, u3, true) : (u2, u1, v3, false)
    tc = _cond(T, tpos)
    while !iszero(t3)
        #println("$t1 $t2 $t3 $tpos")
        while iseven(t3)
            if isodd(t1) || isodd(t2)
                t1 = midpoint(t1, v)
                t2 = midpoint(t2, u)
            else
                t1 >>= 1; t2 >>=1
            end
            t3 >>= 1
        end
        if tpos
            u1, u2, u3 = t1, t2, t3
        else
            v1, v2, v3 = v - t1, u - t2, t3
        end
        tpos = u3 >= v3
        tc = _cond(T, tpos)
        t3 = _condneg(tc, u3 - v3)
        if u1 >= v1
            t1, t2 = u1 - v1, u2 - v2
        else
            t1, t2 = u1 + v - v1, u2 + u - v2
        end
    end
    u3, u1, -u2
end

"""
    condneg(cond, x)

Return `-x` if cond == -1 and `x` id cond == 0.
"""
function _condneg(c::T, x::T) where T<:Base.BitInteger
    c ⊻ x + c&T(1)
end
function _condadd(c::T, x::T, y::T) where T<:Base.BitInteger
    c ⊻ y + c&T(1) + x
end
function _cond(::Type{T}, b::Bool) where T<:Base.BitInteger
    ifelse(b, T(0), -T(1))
end

function gy1(u::T, v::T) where T<:Integer
    @assert u >= 0 && v >= 0 && isodd(v)
    u1, u3 = oneunit(T), u
    v1, v3 = v, v
    t1, t3 = iseven(u) ? (u1, u3) : (zero(T), -v3)
    while !iszero(t3)
        #println("$t1 $t3")
        #println("$(trailing_zeros(t1)) $(trailing_zeros(t3))")
        while iseven(t3)
            if isodd(t1)
                t1 = midpoint(t1, v)
            else
                t1 >>= 1
            end
            t3 >>=1
        end
        if t3 > 0
            u1, u3 = t1, t3
        else
            v1, v3 = v - t1, -t3
        end
        t1, t3 = u1 - v1, u3 - v3
        if t1 <= 0
            t1 += v
        end
    end
    u, v = div(u, u3), div(v, u3)
    u3, u1, -wmuldiv(u, v, u3, u1)
end

function wmuldiv(u::T, v::T, u3::T, u1::T) where T<:Integer
    div(widemul(u, u1) - T(1), v)
end

function wmuldiv(u::T, v::T, u3::T, u1::T) where T<:Union{Int128,UInt128}
    a, b = wmul(u, u1)
    b -= T(1)
    wdiv_checked(a, b, v)
end

function wmul(u::T, v::T) where T<:Signed
    sig = signbit(u) ⊻ signbit(v)
    uabs(u) = unsigned(abs(u))
    x, y = wmul(uabs(u), uabs(v))
    xx = ifelse(sig, signed(~x), signed(x))
    xx, y
end

function wmul(u::T, v::T) where T<:Unsigned
    n = UInt8(sizeof(T)<<2)
    a = u>>>n
    b = (u<<n)>>>n
    c = v>>>n
    d = (v<<n)>>>n
    bd = b * d
    bc = b * c
    ac = a * c
    ad = a * d
    adbc = ad + bc
    ov = Base.ifelse(adbc < ad, T(1)<<n, T(0))
    bd1 = bd + adbc<<n
    ov += Base.ifelse(bd1 < bd, T(1), T(0))
    ac1 = ac + ov + adbc>>>n
    ac1, bd1
end

function wdiv_checked(u::S, v::U, w::S) where {S<:Integer,U<:Unsigned}
    x, y = wdiv(u, v, w)
    sig = signbit(x)
    x = ifelse(sig, ~x, x)
    yy = y % S
    if S<:Signed && (!iszero(x) || signbit(yy))
        throw(ArgumentError("results $x, $y not convertible to $S"))
    end
    yy
end

function wdiv(u::S, v::U, w::S) where {S<:Signed,U<:Unsigned}
    U == unsigned(S) || throw(MethodError("$wdiv"))
    sig = signbit(u)
    uu = ifelse(sig, unsigned(~u), unsigned(u))
    sig ⊻= signbit(w)
    ww = unsigned(abs(w))
    x, y = wdiv(uu, v, ww)
    xx = ifelse(sig, signed(~x), signed(x))
    xx, y
end

function wdiv(u::T, v::T, w::T) where T<:Unsigned
    n = UInt8(sizeof(T)<<2)
    e1 = w>>n + oneunit(T)
    f = (w<<n)>>>n

    x, u = divrem(u, w)
    y, u = divrem(u, e1)
    u += y
    u = u<<n - y * f + v>>>n

    yy, u = divrem(u, w)
    y += yy
    z, u = divrem(u, e1)
    u += z
    u = u<<n - z * f + (v<<n)>>>n

    yy, u = divrem(u, w)
    z += yy
    x, y<<n + z, u
end

midpoint(a::Integer, b::Integer) = signbit(a) == signbit(b) ? (b - a)÷2 + a : (a + b) ÷ 2
midpoint(a::T, b::T) where T<:Base.BitInteger = a & b + (a ⊻ b)>>1
