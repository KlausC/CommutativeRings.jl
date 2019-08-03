# CommutativeRings.jl

##### W.I.P
##### Copyright © 2019- by Klaus Crusius. This work is released under The MIT License.
----
[![Build Status](https://travis-ci.org/KlausC/CommutativeRings.jl.svg?branch=master)](https://travis-ci.org/KlausC/CommutativeRings.jl)&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[![codecov](https://codecov.io/gh/KlausC/CommutativeRings.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/KlausC/CommutativeRings.jl)

----

### `CommutativeRings`

This software is the start of a computer algebra system specialized to
discrete calculations in the area of integer numbers Z, modular arithmetic Z/m
fractional Q, polynomials Z[x].

The mentioned examples are elemetary examples for ring structures. The can be
liberately combined to fractional fields, quotient rings, and polynomials of previously defined structures.
So it is possible to work with rational functions, which are fractions of polynomials, where the polynomial coefficients are in Z/p, for example.


#### Usage

```
julia> using CommutativeRings

 # starting with some calculation in the quotient field Z/31

julia> m = 31
31

julia> ZZp = ZZmod{m,Int8}
ZZmod{31,Int8}

julia> modulus(ZZp)
31

julia> z1 = ZZp(12)
ZZmod{31,Int8}(12)

julia> z2 = ZZp(17)
ZZmod{31,Int8}(17)

julia> z1 + z2
ZZmod{31,Int8}(29)

julia> z1 * z2
ZZmod{31,Int8}(18)

julia> inv(z1)
ZZmod{31,Int8}(13)

julia> 13z1
ZZmod{31,Int8}(1)


 # using a big prime as parameter, the class is identified by an arbitrary symbol (:p)

julia> ZZbig = new_class(ZZmod{:p,BigInt}, big(2)^521 - 1)
ZZmod{:p,BigInt}

julia> modulus(ZZbig)
686479766013060971498190079908139321726943530014330540939446345918554318
339765605212255964066145455497729631139148085803712198799971664381257402
8291115057151

julia> zb = ZZbig(10)
ZZmod{:p,BigInt}(10)

julia> zb^(modulus(ZZbig)-1)
ZZmod{:p,BigInt}(1)

... # now polynomials with element type of Z/31

julia> P = UnivariatePolynomial{:x,ZZp}
UnivariatePolynomial{:x,ZZmod{31,Int8}}

julia> x = P([0, 1])
Int8[0, 1]

julia> p = (x + 2)^2 * (x-1)
Int8[27, 0, 3, 1]
 # note: mod(-4, 31) == 27

 # the stored coefficients are really of that type!
julia> p.coeff
4-element Array{ZZmod{31,Int8},1}:
 ZZmod{31,Int8}(27)
 ZZmod{31,Int8}(0) 
 ZZmod{31,Int8}(3) 
 ZZmod{31,Int8}(1) 


julia> gcd(p, P([-1, 1]))
Int8[30, 1]

julia> p / (x + 3) * (x + 1)
ERROR: DomainError with (Int8[27, 0, 3, 1], Int8[3, 1]):
not dividable a/b.

```

#### Installation of this WIP version


```
$ cd ~/.julia/dev

$ git clone https://github.com/KlausC/CommutativeRings.jl.git CommutativeRings

$ julia
...
 # press "]"
(v1.3) pkg> activate CommutativeRings
Activating environment at `~/.julia/dev/CommutativeRings/Project.toml`

(CommutativeRings) pkg>

 # press backspace

julia> using CommutativeRings
[ Info: Recompiling stale cache file ~/.julia/compiled/v1.3/CommutativeRings/mLTUZ.ji for CommutativeRings [a6d4fa9c-9e0b-4795-89f3-f481b7b5e384]

(CommutativeRings) pkg> test
  Updating registry at `~/.julia/registries/General`
  Updating git-repo `https://github.com/JuliaRegistries/General.git`
   Testing CommutativeRings
 Resolving package versions...
[ Info: No changes
Test Summary: | Pass  Total
ZZ            |   89     89
Test Summary: | Pass  Total
ZZmod         |  315    315
[1, 2, 1]Test Summary: | Pass  Total
univarpolynom |  167    167
   Testing CommutativeRings tests passed 


```

#### Mathematical operations

+, -, *, div, rem, /, ^, gcd, gcdx


#### Implementation:

Each algebraic structure corresponds to a parameterized `Julia` type or struct. For example, to represent Z/m, there is
```
    abstract type Ring{<:RingClass} end

    struct ZZmod{m,T<:Integer} <: Ring{ZZmodRingClass}; val::T; end
```
The subtypes of `RingClass` are currently only containers for constant type variables. It may be necessary to hold values, which are specific for the algebraic structure, and cannot be stored in as type paramters. That is for example the case, when the modulus `m` in the example above is a `BigInt`.
In other cases, the classes are unused. The user needs not deal with those types.
Access to the type variable is used within the implementation by method `owner(::Type{<:Ring}}` which provides the `RingClass` object, when the complete type is known.
Preferred operation mode is to take the type parameters directly.



#### Acknowledgements:
This package was inspired by the `C++` library `CoCoALib`, which can be found
here: [CoCoALib](http://cocoa.dima.unige.it/cocoalib/) .



