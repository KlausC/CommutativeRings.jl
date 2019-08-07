# CommutativeRings.jl

##### W.I.P
##### Copyright © 2019- by Klaus Crusius. This work is released under The MIT License.
----
[![Build Status](https://travis-ci.org/KlausC/CommutativeRings.jl.svg?branch=master)](https://travis-ci.org/KlausC/CommutativeRings.jl)&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[![codecov](https://codecov.io/gh/KlausC/CommutativeRings.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/KlausC/CommutativeRings.jl)

----

# `CommutativeRings`

## Introduction

This software is the start of a computer algebra system specialized to
discrete calculations in the area of integer numbers `ℤ`, modular arithmetic `ℤ/m`
fractional `ℚ`, polynomials `ℤ[x]`. It is important, that rings may be freely combined, for example `ℤ/p[x]` (polynomials over the quotient ring for a prime number `p`), or `Frac(ℤ[x])`, the rational functions with integer coefficients.

The mentioned examples are elemetary examples for ring structures. The can be
liberately combined to fractional fields, quotient rings, and polynomials of previously defined structures.

So it is possible to work with rational functions, which are fractions of polynomials, where the polynomial coefficients are in ℤ/p, for example.
The the current standard library we have modules `Rational` and `Polynomial` besides the numeric subtypes of `Number`and some support for modular calculations with integers.

The original motivation for writing this piece of sofware, when I tried to handle polynomials over a quotient ring. There was no obvious way of embedding my ring elements
into the `Julia` language and for example exploit polynomial calculations from the `Polynomial` package for that. There seems to be a correspondence between `Julia` types and structures and the algebraic stuctures I want to work with. So the idea was born to define
abstract and concrete types in `Julia`, the objects of those types representing the ring
elements to operate on. As types are first class objects in `Julia`it was also possible to
define combinations in a language affine way. Also `ring homomorphisms`, i.e. strucure-respecting mappings between rings (of differnt kind) find a natural representation as one-argument-functions or methods with corresponding domains. The typical canonical homomorphisms, can be conveniently implemented as constructors.

The expoitation of the julia structures is in contrast to the alternative package [AbstractAlgebra](https://github.com/Nemocas/AbstractAlgebra.jl), which defines separate types for ring elements and the ring classes themselves, the elements keeping an explicit link to the owner structure.

To distinct variants of rings, we use type parameters, for example the `m` in `ℤ/m` or the `x` in `ℤ[x]`. Other type parameters may be used to specify implementation restictions, for
example typically the integer types used for the representation of the objects.

Correspondence between algebraic and Julia categories:

| algebric                            | Julia          | example
|-------------------------------------|----------------|------------------------------|
| category **Ring**                   |abstract type   | `abstract type Ring ...`
| algebraic structure **ℤ/m**         |concrete type   | `struct ZZmod{m,Int} <: Ring`
| specialisation **ℤ** is a **Ring**  | type inclusion | `ZZ{Int] <: Ring`
| ring element **a** of **R**| object | `a` isa `R`    |
| basic binary operations **a + b**   | binary operator| `a + b`
| homomorphism **h** : **R** -> **S** | method         | `h(::R)::S = ...`
| canonical **h** : **R** -> **S**    | constructor    | `S(::R) = ...`
 

## Usage example

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
12°
julia> z2 = ZZp(17)
-14°
julia> z1 + z2
-2°
julia> z1 * z2
-13°
julia> inv(z1)
13°
julia> 13z1
1°

 # using a big prime as parameter, the class is identified by an arbitrary symbol (:p)

julia> ZZbig = new_class(ZZmod{:p,BigInt}, big(2)^521 - 1)
ZZmod{:p,BigInt}

julia> modulus(ZZbig)
6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
julia> zb = ZZbig(10)
10°
julia> zb^(modulus(ZZbig)-1) # Fermat's little theorem for primes
1°


... # now polynomials with element type of Z/31

julia> P = UnivariatePolynomial{:x,ZZp}
UnivariatePolynomial{:x,ZZmod{31,Int8}}
julia> x = P([0, 1])
x

julia> p = (x + 2)^2 * (x-1)
x^3 + 3°⋅x^2 - 4°
julia> p.coeff
4-element Array{ZZmod{31,Int8},1}:
 -4°
 0°
 3°
 1°
julia> 1 + p
x^3 + 3°⋅x^2 - 3°


julia> gcd(p, x-1)
x - 1°
julia> p / (x-1)
x^2 + 4°⋅x + 4°
julia> p / (x+2)
x^2 + x - 2°


julia> p / (x + 3) * (x + 1)
ERROR: DomainError with (x^3 + 3°⋅x^2 - 4°, x + 3°):
not dividable a/b.

```

## Installation of this WIP version


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
       Testing CommutativeRings
     Resolving package versions...
    Test Summary: | Pass  Total
    ZZ            |   92     92
    Test Summary: | Pass  Total
    ZZmod         |  327    327
    Test Summary: | Pass  Total
    univarpolynom |  187    187
    Test Summary: | Pass  Total
    quotient      |    4      4
       Testing CommutativeRings tests passed
```

## Implementation details

  * ###Classes

| Name            | supertype      | description   | remarks |
|-----------------|----------------|---------------|---------|
| `Ring`          | `Any`          | abstract - supertype of all ring classes|
| `FractionField` | `Ring`         | abstract - ring of fractions over a ring |
| `QuotientRing`  | `Ring`         | abstract - quotient (or factor-) ring of a ring|
| `Polynomial`    | `Ring`         | abstract - polynomials over a ring |
| `ZZ{type}`      | `Ring`         | integer numbers | `type` is an integer Julia type
| `ZZmod{m,type}` | `QuotientRing` | quotient class modulo `m` | `m` is a small integer or a symbol to accomodate `BigInt
| `QQ{type}`      | `FractionField`| rational numbers | essential identical to `Rational{type}`
| `QQ{R}`         | `FractionField`| fractions over a `R`
| `Quotient{m,R}` | `QuotientRing` | also `R/m`, ring modulo `m`| `m` is an element or an ideal of `R`
| `UnivariatePolynomial{X,R}` | `Polynomial`| also `R[X]`, ring of polynomials over `R`|`X` is a symbol like `:x`

 #### class construction

Each complete `Julia` type (with all type parameters specified) defines a singlton algebraic class. Sometimes it is necessary to use distinguishing symbols as a first type parameter if the parameter value cannot be use directly.
For that purpose, there is a special function `new_class`:
```
    m = big"....."
    Zm = new_class(ZZmod{:p,BigInt}, m)

 # as opposed to

    p = Int128(2)^127 - 1
    Zp = ZZmod{p,Int128}
```

For general quotient classes and for polynomials there are convenient constructors, which
look like the typical mathematical notation `R[:x]` and `R / I`:
```
    S = ZZ{Int}
    P = S[:x]
    x = P([0,1])
    Q = P/(x^2 + 1) 
```
The `/` notion is also implemented for `Julia`integer types,
so this works:
```
    Z31 = Int8 / 31    # equivalent to ZZmod{31,Int8}
    Zbig = BigInt / (big"2"^521-1) # equivalent to new_class(ZZmod{gensym(),BigInt}, m)
```


* ### Constructors for elements

The class names of all concrete types serve also as constructor names.
Typically the last type parameters may be omitted.
The names may be assigned to variables or constants to be easily re-used.


| Name | remarks
|------|-------|
|ZZ{


* ### Mathematical operations

| operation | operator |remarks|
|-----------|:--------:|-------|
| add       | + ||
| subtract  | - | also unary |
| multiply  | * |
| integer power | ^ | use `Base.power_by_squares`|
| divide    | / | only if dividable without remainder|
| divrem    || complete integer division
| div       |÷|quotient integer division
| rem       |%|remainder integer division
| gcd       ||classical Euclid's algorithm
| gcdx      ||extended Euclid's algorithm
| pdivrem   ||pseudo division for polynomials over rings `d, r = divrem(p, q) => q * d + r = f * p` where`f` is in the base ring
| pgcd      ||pseudo gcd `g, f = pgcd(p, q) => 
| pgcdx     ||pseudo gcdx `g, u, v, f = pgcdx(p, q) => p * u + q * v = g * f` where f is in base ring
| iszero    ||test if element is zero-element of its ring
| isone     ||test if element is one-element of its ring
| isunit    ||test if element is invertible in its ring
| deg       || degree of polynomial, `-1` for zero. For non-polynomials always `0`.
| lc        ||leading coefficient of polynomial, otherwise identity
| ismonomial|| short for `isone(lc(x))`
| ismonic   || polynomials of the form `c * x^k` for `c` in th base ring, k >= 0 integer

  * ###Associated classes

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



