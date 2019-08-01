
# construction

function ZZmod{m,T}(a::Integer) where {m,T}
    mo = modulus(ZZmod{m,T})
    mo > 0 && return ZZmod{m,T}(mod(T(a), T(mo)), NOCHECK)
    throw(DomainError(m, "modulus > 0 required."))
end
ZZmod{m}(a::Integer) where m = ZZmod{m,typeof(m)}(oftype(m, a))
ZZmod(a::T, m::S) where {T,S} = ZZmod{m}(S(a))
function ZZmod{s,T}(a::Integer, m::Integer) where {s,T<:Integer}
    register!(ZZmod{s,T}, T(m))
    ZZmod{s,T}(T(a))
end

# get type variable
modulus(T::Type{<:ZZmod{m}}) where m = m isa Symbol ? gettypevar(T).modulus : m
modulus(::T) where T<:ZZmod = modulus(T)

# arithmetic

function +(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T}
    mb = T(m) - b.val
    s = a.val < mb ? a.val + b.val : a.val + mb
    ZZmod{m,T}(s, NOCHECK)
end
function -(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T}
    mb = T(m) - b.val
    s = a.val < b.val ? a.val + mb : a.val - b.val
    ZZmod{m,T}(s, NOCHECK)
end
-(a::ZZmod{m,T}) where {m,T} = iszero(a.val) ? a : ZZmod{m,T}(T(m) - a.val, NOCHECK)
*(a::ZZmod{m,T}, b::ZZmod{m,T}) where {m,T} = ZZmod{m,T}(mult_ZZmod(a.val, b.val, T(m)), NOCHECK)
*(a::ZZmod{m,T}, b::Integer) where {m,T} = ZZmod{m,T}(mult_ZZmod(a.val, T(b), T(m)), NOCHECK)
*(a::Integer, b::ZZmod{m,T}) where {m,T} = ZZmod{m,T}(mult_ZZmod(T(a), b.val, T(m)), NOCHECK)

inv(a::ZZmod{m,T}) where {m,T} = ZZmod{m,T}(invmod2(a.val, T(m)), NOCHECK)
/(a::ZZmod, b::ZZmod) = a * inv(b)
^(a::ZZmod{m,T}, n::Integer) where {m,T} = ZZmod{m,T}(powermod(a.val, n, T(m)), NOCHECK)

isunit(x::ZZmod{m,T}) where {m,T} = gcd(T(m), x.val) == 1
iszero(x::ZZmod) = iszero(x.val)
isone(x::ZZmod) = isone(x.val)
zero(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(zero(S), NOCHECK)
zero(::Type{ZZmod{m}}) where {m} = ZZmod{m,typeof(m)}(zero(m), NOCHECK)
one(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m}(one(S))
one(::Type{ZZmod{m}}) where {m} = ZZmod{m}(one(m))
==(a::ZZmod{m},b::ZZmod{m}) where m = a.val == b.val

# implementation of checked multiplication
function mult_ZZmod(a::T, b::T, m::T) where T<:Integer
    p, ov = Base.mul_with_overflow(a, b)
    ov || return mod(p, m)
    T(mod(widemul(a, b), m))
end

# improved version of invmod
function invmod2(n::T, m::T) where T<:Integer
    m == T(0) && throw(DomainError(m, "`m` must not be 0."))
    p = _unsigned(abs(m))
    q = n >= 0 ? rem(_unsigned(n), p) : p - rem(_unsigned(-n), p)
    !iszero(q) && p != q || throw(DomainError((n, m), "Greatest common divisor is $m"))
    r = invmod_unsigned(q, p)
    m < 0 ? T(r) + m : T(r)
    # The postcondition is: mod(widemul(r, n), m) == mod(T(1), m) && div(r, m) == 0
end
# assumptions is, that  0 <= n < m
function invmod_unsigned(n::T, m::T) where T<:Union{Unsigned,BigInt}
    n = n < m ? n : rem(n, m)
    g, r, y = gcdx(n, m)
    g != 1 && throw(DomainError((n, m), "Greatest common divisor is $g."))
    # For unsigned T, x might be close to typemax; add m to force a wrap-around.
    if _underflow(r)
        r += m
    end
    r
    # The postcondition is: mod(widemul(r, n), m) == mod(T(1), m) && div(r, m) == 0
end

_underflow(r::Signed) = r < 0
_underflow(r::T) where T<:Unsigned = Base.hastypemax(T) && typemax(T)>>1 < r

_unsigned(::Type{BigInt}) = BigInt
_unsigned(T::Type) = unsigned(T)
_unsigned(x::BigInt) = x
_unsigned(x::Integer) = unsigned(x)

