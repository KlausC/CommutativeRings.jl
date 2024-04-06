
# class constructors
function ZZmod(m::Integer, ::Type{T}) where T<:Integer
    m > 0 || throw(DomainError(m, "modulus > 0 required."))
    new_class(ZZmod{sintern(m),T}, T(m))
end
/(::Type{ZZ{T}}, m::Integer) where T<:Integer = ZZmod(T(m), T)
/(::Type{ZZ}, m::Integer) = ZZmod(m, mintype_for(m, 1, false))

# construction
isprimemod(Z::Type{<:ZZmod}) = isprime(modulus(Z))
basetype(::Type{<:ZZmod{m,T}}) where {m,T} = ZZ{wsigned(T)}

_lcunit(a::ZZmod) = one(a)
issimpler(a::T, b::T) where T<:ZZmod = deg(a) < deg(b)

wsigned(::Type{T}) where T<:Signed = T
wsigned(::Type{T}) where T<:Unsigned = widen(signed(T))
wsigned(a::T) where T<:Integer = convert(wsigned(T), a)

function ZZmod{m,T}(a::Integer) where {m,T}
    mo = modulus(ZZmod{m,T})
    ZZmod{m,T}(T(mod(a, T(mo))), NOCHECK)
end
#ZZmod{m}(a::Integer) where {m} = ZZmod{m,typeof(m)}(oftype(m, a))
ZZmod(a::T, m::S) where {T<:Integer,S<:Integer} = ZZmod(m, S)(S(a))
ZZmod{m,T}(a::ZZmod{m,T}) where {m,T} = a
ZZmod{m,T}(a::ZZmod{m,S}) where {m,T,S} = ZZmod{m,T}(a.val)
ZZmod{m,T}(a::ZZ) where {m,T} = ZZmod{m,T}(a.val)

copy(p::ZZmod) = typeof(p)(p.val)

#promotion and conversion
function promote_rule(ZT::Type{ZZmod{m,S}}, ZS::Type{ZZmod{n,T}}) where {n,m,T,S}
    mzt = modulus(ZT)
    mzs = modulus(ZS)
    if mzt == mzs
        R = promote_type(T, S)
        if m == n
            ZZmod{promote(n, m)[1],R}
        elseif n isa Symbol
            ZZmod{n,R}
        else
            ZZmod{m,R}
        end
    else
        mn = gcd(m,n)
        ZZmod(mn, mintype_for(mn, 1, false))
    end
end
promote_rule(::Type{ZZmod{m,S}}, ::Type{T}) where {m,S,T<:Integer} = ZZmod{m,S}
promote_rule(::Type{ZZmod{m,S}}, ::Type{T}) where {m,S,T<:ZI} = ZZmod{m,S}

function (::Type{ZT})(a::ZS) where {n,m,T,S,ZT<:ZZmod{n,T},ZS<:ZZmod{m,S}}
    mzt = modulus(ZT)
    mzs = modulus(ZS)
    if mzs % mzt == 0
        ZT(a.val % mzt)
    else
        throw(DomainError((ZT, a), "cannot convert $ZS to $ZT"))
    end
end

convert(::Type{Z}, a::ZZ) where Z <: ZZmod = Z(a)
(::Type{Z})(a::ZZ) where Z <: ZZmod = Z(a.val % modulus(Z))
(::Type{T})(a::ZZmod) where T<:Integer = T(value(a))

"""
    value(a::ZZmod{m,T})

Return unique signed(T) integer in the range `[-m/2, m/2)` representing `a`, where `m` is the modulus.
"""
function value(a::ZZmod{X,T}) where {X,T}
    S = signed(T)
    v = a.val
    m = modulus(a)
    m1 = m >> 1
    m2 = m - m1
    v < m2 ? S(v) : S(v - m2) - S(m1)
end

# get type variable
function modulus(t::Type{<:ZZmod{m,T}}) where {m,T}
    p = m isa Integer ? T(m) : gettypevar(t).modulus
    p > 0 || throw(DomainError(m, "modulus must be > 0"))
    p
end
modulus(::T) where T<:ZZmod = modulus(T)

Base.isless(p::T, q::T) where T<:ZZmod = isless(p.val, q.val)

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
^(a::T, n::Integer) where T<:ZZmod = T(powermod(a.val, n, modulus(T)), NOCHECK)

isunit(x::T) where T<:ZZmod = gcd(modulus(T), x.val) == 1
iszero(x::ZZmod) = iszero(x.val)
isone(x::ZZmod) = isone(x.val) === (modulus(x) > 1)
zero(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(zero(S), NOCHECK)
zero(::Type{ZZmod{m}}) where {m} = ZZmod{m,typeof(m)}(zero(m), NOCHECK)
one(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(one(S))
one(::Type{ZZmod{m}}) where {m} = ZZmod{m}(one(m))
==(a::ZZmod{m1}, b::ZZmod{m2}) where {m1,m2} = modulus(a) == modulus(b) && a.val == b.val
hash(a::ZZmod, h::UInt) = hash(a.val, hash(modulus(a), h))
dimension(::Type{<:ZZmod}) = 1

# implementation of checked multiplication
@inline function mult_ZZmod(a::T, b::T, m::T) where T<:Integer
    p, ov = Base.mul_with_overflow(a, b)
    ov || return mod(p, m)
    T(mod(widemul(a, b), m))
end
function mult_ZZmod(a::T1, b::T2, c::T) where {T1<:Integer,T2<:Integer,T<:Integer}
    a = T(mod(a, c))
    b = T(mod(b, c))
    mult_ZZmod(a, b, c)
end

# improved version of invmod
@inline function invmod2(n::T, m::T) where T<:Integer
    iszero(m) && throw(DomainError(m, "`m` must not be 0."))
    p = _unsigned(abs(m))
    q = n >= 0 ? rem(_unsigned(n), p) : p - rem(_unsigned(-n), p)
    !iszero(q) && p != q || throw(DomainError((n, m), "Greatest common divisor is $m"))
    r = invmod_unsigned(q, p)
    m < 0 ? T(r) + m : T(r)
    # The postcondition is: mod(widemul(r, n), m) == mod(T(1), m) && div(r, m) == 0
end
# assumptions is, that  0 <= n < m
@inline function invmod_unsigned(n::T, m::T) where T<:Union{Unsigned,BigInt}
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
_underflow(r::T) where T<:Unsigned = Base.hastypemax(T) && typemax(T) >> 1 < r

_unsigned(::Type{BigInt}) = BigInt
_unsigned(T::Type) = unsigned(T)
_unsigned(x::BigInt) = x
_unsigned(x::Integer) = unsigned(x)

function Base.show(io::IO, a::ZZmod)
    v = a.val
    m = modulus(a)
    if m > 10 && v > m ÷ 2
        print(io, '-', signed(m - v), '°')
    else
        print(io, signed(v), '°')
    end
end

@inline function minlength_for(v::Integer, ::Val{1}, off::Bool)
    ndigits(v - off; base = 2, pad = 0)
end
@inline function minlength_for(v::Integer, ::Val{ex}, off::Bool) where ex
    l2n = log2(v) * ex
    Int(off ? ceil(l2n) : floor(l2n) + 1)
end

function mintype_for(v::Integer, ex::Integer, off::Bool)
    v isa BigInt && v > typemax(UInt128) && return BigInt
    len = minlength_for(v, Val(ex), off)
    for T in (UInt8, UInt16, UInt32, UInt64, UInt128)
        n = sizeof(T) * 8
        len <= n && return len < n ? signed(T) : T
    end
    BigInt
end
