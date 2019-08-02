
# construction

function ZZmod{m,T}(a::Integer) where {m,T}
    mo = modulus(ZZmod{m,T})
    mo > 0 && return ZZmod{m,T}(mod(T(a), T(mo)), NOCHECK)
    throw(DomainError(m, "modulus > 0 required."))
end
ZZmod{m}(a::Integer) where m = ZZmod{m,typeof(m)}(oftype(m, a))
ZZmod(a::T, m::S) where {T,S} = ZZmod{m}(S(a))

copy(a::ZZmod) = typeof(p)(p.val)

# get type variable
modulus(T::Type{<:ZZmod{m}}) where m = m isa Integer ? m : gettypevar(T).modulus
modulus(::T) where T<:ZZmod = modulus(T)

# arithmetic

function +(a::T, b::T) where T<:ZZmod
    mb = modulus(T) - b.val
    s = a.val < mb ? a.val + b.val : a.val - mb
    T(s, NOCHECK)
end
function -(a::T, b::T) where T<:ZZmod
    mb = modulus(T) - b.val
    s = a.val < b.val ? a.val + mb : a.val - b.val
    T(s, NOCHECK)
end
-(a::T) where T<:ZZmod = iszero(a.val) ? a : T(modulus(T) - a.val, NOCHECK)
*(a::T, b::T) where T<:ZZmod = T(mult_ZZmod(a.val, b.val, modulus(T)), NOCHECK)
*(a::T, b::Integer) where T<:ZZmod = T(mult_ZZmod(a.val, b, modulus(T)), NOCHECK)
*(a::Integer, b::T) where T<:ZZmod = T(mult_ZZmod(a, b.val, modulus(T)), NOCHECK)

inv(a::T) where T<:ZZmod = T(invmod2(a.val, modulus(T)), NOCHECK)
/(a::T, b::T) where T<:ZZmod = a * inv(b)
^(a::T, n::Integer) where T<:ZZmod = T(powermod(a.val, n, modulus(T)), NOCHECK)

isunit(x::T) where T<:ZZmod = gcd(modulus(T), x.val) == 1
iszero(x::ZZmod) = iszero(x.val)
isone(x::ZZmod) = isone(x.val)
zero(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(zero(S), NOCHECK)
zero(::Type{ZZmod{m}}) where {m} = ZZmod{m,typeof(m)}(zero(m), NOCHECK)
one(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(one(S))
one(::Type{ZZmod{m}}) where {m} = ZZmod{m}(one(m))
==(a::ZZmod{m1},b::ZZmod{m2}) where {m1,m2} = modulus(a) == modulus(b) && a.val == b.val
hash(a::ZZmod, h::UInt) = hash(a.val, hash(modulus(a), h))

# implementation of checked multiplication
function mult_ZZmod(a::T, b::T, m::T) where T<:Integer
    p, ov = Base.mul_with_overflow(a, b)
    ov || return mod(p, m)
    T(mod(widemul(a, b), m))
end
function mult_ZZmod(a::T1, b::T2, c::T) where {T1<:Integer,T2<:Integer,T<:Integer}
    a = T(mod(a,c))
    b = T(mod(b,c))
    mult_ZZmod(a, b, c)
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

