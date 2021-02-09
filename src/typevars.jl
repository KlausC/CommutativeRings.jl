
# functions to set and get associated user data in variable `instance` of `DataType`.

"""
    settypevar!(t::Type, value)

Associate type with a value.
The value can be retrieved by calling `gettypevar(t)`.
"""
function settypevar!(t::Type, value)
    get!(TypeVariableTemp, t, value)
end

const TypeVariableTemp = Dict{DataType, Any}()


"""
    gettypevar(t::Type)

Return value, which has previously been associated with this type
"""
@generated function gettypevar(::Type{R}) where {T,R<:Ring{T}}
    tv = TypeVariableTemp[R]
    :( $tv )
end

"""
Define function before first method will be defined.
"""
function gettypevar_impl end

"""
    new_class(t::Type{<:Ring{T}}, args...) where T<:RingClass

Store type variable `T(args...)` for `t` and return `t`.
The return value can be used to create ring elements of the new class.
Example:
```
    ZZp = new_class(ZZmod{:p,BigInt}, 1000000000000000000000000000057)
    element = ZZp(123456)^10000000 
```
"""
function new_class(t::Type{<:Ring{T}}, args...) where T
    settypevar!(t, T(args...))
    t
end

const IdentSymbols = Union{Symbol,Base.BitInteger,BigInt}
"""
    sintern(a)

Return a symbol, which uniquly identifies the argument.
"""
sintern(m::IdentSymbols) = m
sintern(m::BigInt) = Symbol(m)
sintern(a::IdentSymbols...) = Symbol(tuple(a...))
sintern(a::AbstractVector{<:IdentSymbols}) = Symbol(a)
sintern(a::Tuple{Vararg{<:IdentSymbols}}) = Symbol(a)
sintern(a) = Symbol(hash(a))

