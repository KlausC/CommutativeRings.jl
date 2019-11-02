
# functions to set and get associated user data in variable `instance` of `DataType`.

"""
    settypevar!(t::Type, value)

Associate type with a value.
The value can be retrieved by calling `gettypevar(t)`.
"""
function settypevar!(t::Type, value)
    ex = :( gettypevar_impl(::Type{$t}) = ($value) )
    eval(ex)
end

"""
    gettypevar(t::Type)

Return value, which has previously been associated with this type
"""
function gettypevar(t::Type{<:Ring{T}}) where T
    try
        gettypevar_impl(t)
    catch ex
        if ex isa MethodError
            try
                Base.invokelatest(gettypevar_impl, t)::T
            catch
                rethrow(ex)
            end
        else
            rethrow()
        end
    end
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

"""
    sintern(a)

Return a symbol, which uniquly identifies the argument.
"""
sintern(a::Symbol) = a
sintern(m::Base.BitInteger) = m
sintern(m::BigInt) = Symbol(m)
sintern(a::Symbol...) = Symbol(a...)
sintern(a) = Symbol(hash(a))

