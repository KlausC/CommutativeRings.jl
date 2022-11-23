# CommutativeRings.jl

[![Build Status][gha-img]][gha-url]     [![Coverage Status][codecov-img]][codecov-url]

W.I.P

## Introduction

This software is the start of a computer algebra system specialized to
discrete calculations in the area of integer numbers `ℤ`, modular arithmetic `ℤ/m`
fractional `ℚ`, polynomials `ℤ[x]`. Also multivariate polynomials `ℤ[x,y,...]` and Galois fields `GF(p^r)` are supported.
The polynomials may be extended to quotient rings like `ℤ[:x] / (x^2 + 1)`.

This package is not seen as a replacement of `Nemo.jl` or `AbstractAlgebra.jl`, which should be used for serious work.
It is understood more like a sandbox to try out a simpler API.

It is important, that rings may be freely combined, for example `(ℤ/p)[x]` (polynomials over the quotient ring for a prime number `p`),
`Frac(ℤ[x])`, the rational functions with integer coefficients, or `GF(64)[:x]`, polynomials over the Galois field.
The quotient rings include `Ideal`s, which are of major importance with multivariate polynomials.

The mentioned examples are elementary examples for ring structures. The can be
liberately combined to fractional fields, quotient rings, and polynomials of previously defined structures.

So it is possible to work with rational functions, which are fractions of polynomials, where the polynomial coefficients are in `ℤ/p`,
for example.
In the current standard library we have modules `Rational` and `Polynomial` besides the numeric subtypes of `Number` and some support for modular calculations with integers.

The original motivation for writing this piece of sofware, when I tried to handle polynomials over a quotient ring. There was no obvious way of embedding my ring elements
into the `Julia` language and for example exploit polynomial calculations from the `Polynomial` package for that. There seems to be a correspondence between `Julia` types and structures and the algebraic stuctures I want to work with. So the idea was born to define
abstract and concrete types in `Julia`, the objects of those types representing the ring
elements to operate on. As types are first class objects in `Julia` it was also possible to
define combinations in a language affine way. Also `ring homomorphisms`, i.e. strucure-respecting mappings between rings (of differnt kind) find a natural representation as one-argument-functions or methods with corresponding domains. The typical canonical homomorphisms, can be conveniently implemented as constructors.

The exploitation of the julia structures is in contrast to the alternative package [AbstractAlgebra](https://github.com/Nemocas/AbstractAlgebra.jl), which defines separate types for ring elements and the ring classes themselves, the elements keeping an explicit link to the owner structure.

To distinct variants of rings, we use type parameters, for example the `m` in `ℤ/m` or the `x` in `ℤ[:x]`. Other type parameters may be used to specify implementation restictions, for
example typically the integer types used for the representation of the objects.

Correspondence between algebraic and Julia categories:

| algebraic                            | Julia          | example
|-------------------------------------|----------------|------------------------------|
| category **Ring**                   |abstract type   | `abstract type Ring ...`
| algebraic structure **ℤ/m**         |concrete type   | `struct ZZmod{m,Int} == ZZ/m`  
| specialisation **ℤ** is a **Ring**  | type inclusion | `ZZ{Int] <: Ring`
| ring element **a** of **R**         | object         | `a` isa `R`
| basic binary operations **a + b**   | binary operator| `a + b`
| homomorphism **h** : **R** -> **S** | method         | `h(::R)::S = ...`
| canonical **h** : **R** -> **S**    | constructor    | `S(::R) = ...`

## Usage example

``` julia
julia> using CommutativeRings

 # starting with some calculation in the quotient field Z/31

julia> m = 31
31
julia> ZZp = ZZ/m
ZZmod{31,Int8}
julia> modulus(ZZp)
31
julia> z1 = ZZp(12)
12°
julia> z2 = ZZp(17)
17°
julia> z1 + z2
29°
julia> z1 * z2
18°
julia> inv(z1)
13°
julia> 13z1
1°

 # using a big prime number as parameter, the class is identified by an arbitrary symbol (:p)

julia> ZZbig = ZZ / (big(2)^521 - 1)
ZZmod{Symbol("686479766013060971498190079908139321726943530014330540939446345918554318339765
              6052122559640661454554977296311391480858037121987999716643812574028291115057151"), BigInt}

julia> modulus(ZZbig)
686479766013060971498190079908139321726943530014330540939446345918554318339765
6052122559640661454554977296311391480858037121987999716643812574028291115057151
julia> zb = ZZbig(10)
10°
julia> zb^(modulus(ZZbig)-1) # Fermat's little theorem for primes
1°


... # now polynomials with element type of ZZ/31

julia> P = ZZp[:x]
UnivariatePolynomial{ZZmod{31, Int8}, :x}
julia> x = monom(P)
x

julia> p = (x + 2)^2 * (x - 1)
x^3 + 3°*x^2 + 27°
julia> p.coeff
4-element Array{ZZmod{31,Int8},1}:
 -4°
 0°
 3°
 1°
julia> 1 + p
x^3 + 3°*x^2 + 28°


julia> gcd(p, x-1)
x + 30°
julia> p / (x-1)
x^2 + 4°⋅x + 4°
julia> p / (x+2)
x^2 + x + 29°


julia> p / (x + 3) * (x + 1)
ERROR: DomainError with (x^3 + 3°*x^2 + 27°, x + 3°):
cannot divide a / b
Stacktrace:

```

## Installation of this WIP version

``` julia

    # press "]"
    (@v1.8) pkg> add CommutativeRings
    Updating registry at `~/.julia/registries/General.toml`
   Resolving package versions...
  No Changes to `~/.julia/environments/v1.8/Project.toml`
  No Changes to `~/.julia/environments/v1.8/Manifest.toml`
     # press backspace

julia> using CommutativeRings
[ Info: Precompiling CommutativeRings [a6d4fa9c-9e0b-4795-89f3-f481b7b5e384]

(CommutativeRings) pkg> test
    Testing CommutativeRings

Test Summary: | Pass  Total
generic       |   23     23
Test Summary: | Pass  Total
typevars      |    8      8
Test Summary: | Pass  Total
ZZ            |  113    113
Test Summary: | Pass  Total
QQ            |   42     42
Test Summary: | Pass  Total
ZZmod         |  271    271
Test Summary: | Pass  Total
univarpolynom |  256    256
Test Summary:   | Pass  Total
multivarpolynom |  151    151
Test Summary: | Pass  Total
ideal         |   21     21
Test Summary: | Pass  Total
fraction      |   32     32
Test Summary: | Pass  Total
quotient      |   24     24
Test Summary: | Pass  Total
factorization |   20     20
Test Summary: | Pass  Total
galoisfields  |   99     99
Test Summary: | Pass  Total
numbertheory  |   24     24
Test Summary: | Pass  Total
enumerations  |   31     31
Test Summary: | Pass  Total
linearalgebra |   23     23
    Testing CommutativeRings tests passed  

```

## Implementation details

### Classes

| Name            | supertype      | description / constructor | remarks |
|-----------------|----------------|---------------------------|---------|
| `Ring`          | `Any`          | abstract - supertype of all ring classes|
| `FractionField` | `Ring`         | abstract - ring of fractions over a ring |
| `QuotientRing`  | `Ring`         | abstract - quotient (or factor-) ring of a ring|
| `Polynomial`    | `Ring`         | abstract - polynomials over a ring |
| `ZZ{type}`      | `Ring`         | integer numbers | `type` is an integer Julia type
| `ZZmod{M,type}` | `QuotientRing` | `ZZ / m` quotient class modulo `m` | `m` is an integer Julia value of type `M`
| `QQ{type}`      | `FractionField`| rational numbers over integer | like `Rational{type}` - supports integer Julia and integer Rings
| `Frac{R}`       | `FractionField`| fractions over a `R` typically polynomials |
| `Quotient{m,R}` | `QuotientRing` | also `R/m`, ring modulo `m`| `m` is an element or an ideal of `R`
| `UnivariatePolynomial{X,R}`  |`Polynomial`| also `R[:x]`, ring of polynomials over `R`|`X` is a symbol like `:x`
| `MultivariatePolynomial{X,R}`|`Polynomial`| also `R[:x,:y,...]` | `X` is a list of distinct variable names
| `GaloisField`   | `QuotientRing` | `GF(p^r)` - efficient implementation of Galois fields | more details see below

### class construction

Each complete `Julia` type (with all type parameters specified) defines a singleton algebraic class.

``` julia
    p = Int128(2)^127 - 1
    Zp = ZZmod{p,Int128}
```

For general quotient classes and for polynomials there are convenient constructors, which
look like the typical mathematical notation `R[:x,:y,...]` and `R / I`.
Here the symbols `:x, :y` define the name of the variables of a uni-
or multivariate polynomial ring over `R`. `I` is an ideal of R or an element of
`R`, which represents the corresponding principal ideal.

``` julia
    S = ZZ{Int}
    P = S[:x]
    x = monom(P, 1) # same as P([0,1])
    Q = P / (x^2 + 1)
```

The `/` notion is not implemented for `Julia` integer types (would be type piracy)
so this doesn't work:

``` julia
    julia> Int / 31
ERROR: MethodError: no method matching /(::Type{Int64}, ::Int64)
```

### Ideals

Ideals are can be denoted as `Ideal([a, ...])` where `a,` ... are elements of `R` or
`Ideal(a)`. For convenience, principal ideals support also `a * R == Ideal(a)` and
`p*R == Ideal(R(p))`, where `p` is an integer.

``` julia
    Z = ZZ{Int8}
    Z1 = Z/31
    Z2 = Z/Z(31)
    Z3 = Z/31Z
    Z4 = Z/Ideal(Z(31))

    Z1 == Z2 == Z3 == Z4
```

It may be noted, that `0R` is the zero ideal (containing only the zero element of `R`) and `u*R == R` for all unit elements `u` of `R`.
Currently the expression `R / I` works only for polynomial rings `R`.

If there is one generating element of an ideal, `a * R`, internally a
unit multiple of `a` is stored to achieve a standard form, for
example a monic univariate polynomial.

In the case of multiple generating elements, `a, b...`, an attempt
is made to standardize and reduce the stored base. For example if
`R` is a unique factorization domain, then `gcd(a, b...)` is stored.

Ideals are most useful with multivariate polynomials, when they
are best represented by a minimal base - see below.

### Constructors for elements

The class names of all concrete types serve also as constructor names.
That means, if `R` is a class name, then `R(a)` is an element of `R` for all
`a`, which are integers or elements of (other) rings, which can be natuarally
embedded into `R`.

For polynomial rings `P`, the method call `monom(P, i)` constructs the monic
monomials `x^i` for non-negative integers `i`. That is extended to multivariate
cases `monom(P, i, j, ...)`.

### Mathematical operations

| operation | operator |remarks|
|-----------|:--------:|-------|
| add       | + | operations with `Base.BitIntegers` throw upon overflow|
| subtract  | - | also unary |
| multiply  | * |
| integer power | ^ | use `Base.power_by_squares`|
| divide    | / | only if dividable without remainder|
| divrem    || complete integer division
| div       |÷| quotient integer division
| rem       |%| remainder integer division
| gcd       || classical Euclid's algorithm
| gcdx      || extended Euclid's algorithm
| pdivrem   || pseudo division for polynomials over rings `d, r, f = pdivrem(p, q) => q * d + r = f * p` where `f` is in the base ring
| pgcd      || pseudo gcd `g, f = pgcd(p, q)`
| pgcdx     || pseudo gcdx `g, u, v, f = pgcdx(p, q) => p * u + q * v = g * f` where f is in base ring
| iszero    || test if element is zero-element of its ring
| zero      || zero element of ring
| isone     || test if element is one-element of its ring
| one       || one element of ring
| isunit    || test if element is invertible in its ring
| deg       || degree of polynomial, `-1` for zero. For non-polynomials always `0`.
| ord       || order of univariate polynomial (power of first nozero term)
| LC        || leading coefficient of polynomial, otherwise identity
| ismonom   || short for `isone(lc(x))`
| ismonic   || polynomials of the form `c * x^k` for `c != 0` in the base ring, `k` integer
| monom     || return monomial polygon with given degree
| isirreducible || polynomial cannot be split into non-trivial factors
| irreducibles  || generate all irreducible polynomials of given degree
| factor    || factorize univariate polynomials over finite fields or integers
| modulus   || for quotient rings and Galois fields the defining polynomial
| characteristic || of ring: smallest positive integer `c` with `c * one(G) == 0`, otherwise `0`
| dimension || of Galois fields or vector spaces
| order  || of ring: number of all elements of ring; `0` if infinite
| order  || of element `x`: smallest positive integer `c` with `x^c == 1`, otherwise `0`
| basetype || of ring: type of representative. If `basetype(R)` is a ring, it is naturally embedded in `R`.
| depth  || of ring: nesting depth
| value  || representant of element. For `R/I` the stored value from `R`. For Galois fields the polynomial.
| derive || formal derivation of a polynomial or power series
| inv    || inverse: `isunit(a) => inv(a) * a == 1`
| compose_inv || composition inverse in the case of power series. `f(0) == 0 && dervive(f) != 0 => compose_inv(f)(f(x)) == x`
| det    || detminant of a matrix of ring elements
| resultant || resultant of two univariate polynomials
| discriminant || discriminant of a univariate polynomial
| signed_subresultant_polynomials || efficient algorithm for subresultant polynomials
||||

### Associated classes

Each algebraic structure corresponds to a parameterized `Julia` type or struct. For example, to represent `ZZ/m`, there is

``` julia
    abstract type Ring{<:RingClass} end

    struct ZZmod{m,T<:Integer} <: Ring{ZZmodRingClass}; val::T; end
```

The subtypes of `RingClass` are used as containers for constant type variables. It may be necessary to hold values, which are specific for the algebraic structure, and cannot be stored in as type paramters. That happens for example, if the modulus `m` in the example above is a `BigInt` or a polynomial.
In other cases, the classes are unused. The user needs not deal with those types as long as he does not define
own ring structures.

Access to the type variables is used within the implementation by method `gettypevar(::Type{<:Ring}}` which provides the `RingClass` object, when the complete type is known.
The ring types typically provide accessor functions to obtain the type specific values, like `modulus`, `order`, `characteristic`, `dimension`, etc.. Try `@code_typed dimension(GF(25))` to see how efficient the generated code is.

## Univariate Polynomials

For each ring type `R` the class of polynomials over `R` is created like `P = R[:x]` where the symbol `:x` defines the name of the indeterminate.

Polynomials of this class are obtained by the constructor
 `g = UnivariatePolynomial{R,:x}([1, 2, 3])`
or more conveniently by

``` julia
x = monom(P)
g = 3x^2 + 2x + 1  
```

If `R` is a finite Field (that means `ZZ/p` or GaloisField - see below) the following options are available:

Univariate polynomials may be checked by `isirreducible(p)` for their irreducibility
and `factor(g)` delivers the list of irreducible factors of `g`.
The factorization is also implemented for univariate polynomials over the integers (for example of type `ZZ{BigInt}[:x]`)

For finite fields, the function `irreducible(P, r)` delivers the first irreducible polynomial with degree `r`.
All irreducible polynomials of `P` with degree `r` are obtained by `irreducibles(P, r)`
which is an iterator. That allows to apply  `Iterators.filter` or `find` on this list.

While the number of polynomials of degree `r` is `order(R)^r`, the subset of
irreducibles has order `num_irreducibles(P, r)`.

## Galois Fields

All finite fields have order `p^r` where `p` is a prime number and `r >= 1` an integer.
It can be represented as a quotient ring of univariate polynomials over `ZZ/p` by an irreducible monic polynomial `g` of degree `r`.
In short, if `g` is known, we have `(ZZ/p)[:x] / g` as a working implementation of a Galois field.
For `r == 1` this can be identified with `ZZ/p` (using `g(x) = x`). The `modulus` method return the polynomial which is actually used by the implementation.

`g` can be any monic polynomial of degree `r`. When constructing the class `GF(p^r) = GaloisField{p,r}` a brute force search for such polynomials is
performed using an efficient method to detect irreducibility. For `r > 1` the monom `x ∈ (ZZ/p)[:x] / g` together with `0` and `1` generates the field by
applying addition and multiplication operations. Calculated in `GF`, we have always `g(x) = 0`.
We restrict the selection of `g` in order to `x` let generate the multiplicative subgroup of `GF` by multiplication. That is possible for all `p, r`.

Time efficiency of algebraic operations is improved by avoiding the expensive multiplicative calculations in the quotient ring and the use of
logarithmic tables in the size of `p^r`. Each element is represented by an integer in `0:p^r-1`, which corresponds to a polynomial of degree `< r`
in a canonical manner (for example the number `2p^3 + p + 1` maps uniquley to `2x^3 + x + 1`).

### Using Galois Fields

We construct a Galois field conveniently by `GF(p^r)`.

``` julia
julia> p, r = 5, 6; # `p` is prime number, `r` not too big

julia> G = GF(5^6) # GF(5, 6) is also possible
GaloisField{5,6}

julia> g = modulus(G) # the selected irreducible polynomial
α^6 + α + 2° # we use a distinct name for indeterminate

julia> order(G) # `p^r`
15625

julia> x = G[5] # an easy way to obtain the standard monom
{0:0:0:0:1:0%5}

julia> order(x) # `x` generates the multiplicative subgroup
15624

julia> G.(0:p) # the integers are mapped into the field G(5) == 0
6-element Array{GaloisField{5,6},1}:
 {0:0:0:0:0:0%5}
 {0:0:0:0:0:1%5}
 {0:0:0:0:0:2%5}
 {0:0:0:0:0:3%5}
 {0:0:0:0:0:4%5}
 {0:0:0:0:0:0%5}

julia> g(x) # the monom `x` is a root of `g`
{0:0:0:0:0:0%5}

# These are all zeros of g - see also `allzeros`
julia> x.^p.^(0:r-1)
6-element Array{GaloisField{5,6},1}:
 {0:0:0:0:1:0%5}
 {1:0:0:0:0:0%5}
 {1:3:4:2:1:0%5}
 {1:2:4:3:1:0%5}
 {1:1:1:1:1:0%5}
 {1:4:1:4:1:0%5}

julia> g.(x.^p.^(0:r-1)) |> unique
1-element Array{GaloisField{5,6},1}:
 {0:0:0:0:0:0%5}
```

## Linear Algebra

Matrices and vectors of ring elements are supported.
`x - A` is understood as `x * I - A`.

The following methods handle vector spaces und subspaces:

| operation | remarks |
|-----------|---------|
| nullspace | null space (kernel) of matrix
| intersect | instesection of subspaces
| sum       | sum of subspaces
| rank      | rank of matrix

For a square matrix, also the following methods exist:

| operation | remarks |
|-----------|---------|
| inv       | matrix inverse - using generic LU factorization
| det       | determinant - using generic LU factorization
| adjugate  | for regular `A`: `inv(A) * det(A)`
| characteristic_polynomial | `p(A) == 0`
| companion | collides with `Polynomials.companion`

For `inv`, `det`, and `adjugate` if the element type is `P<:Polynomial`, it should be widened to `Frac(P)`.

## Multivariate Polynomials

Some example usage:

``` julia

julia> Z = ZZ / 7
ZZmod{7,Int8}

julia> P = Z[:x,:y]
MultivariatePolynomial{ZZmod{7,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}}

julia> x, y = generators(P);

julia> (x + y)^2
x^2 + 2°*x*y + y^2

julia> (x + y)^7
x^7 + y^7

julia> z = (x + y^2) * (x^2 + y)
x^2*y^2 + x^3 + y^3 + x*y

julia> z^2 / (x^2 + y)^2
y^4 + 2°*x*y^2 + x^2

julia> I = [x+2; (x+1)*y];
2-element Array{MultivariatePolynomial{ZZmod{7,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 x + 2°
 x*y + y

julia> groebnerbase(I)
2-element Array{MultivariatePolynomial{ZZmod{7,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 x + 2°
 y

 julia> P = (ZZ/97)[:x, :y]
MultivariatePolynomial{ZZmod{97,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}}

julia> x, y = generators(P);

julia> I = [x^2*y + x*y; x*y^2 + 1]
2-element Array{MultivariatePolynomial{ZZmod{97,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 x^2*y + x*y
 x*y^2 + 1°

julia> groebnerbase(I)
2-element Array{MultivariatePolynomial{ZZmod{97,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 y^2 + 96°
 x + 1°

# example from [Gröbner Base](https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis)
julia> I = [x^2 - y; x^3 - x]
2-element Array{MultivariatePolynomial{ZZmod{7,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 x^2 - y
 x^3 - x

julia> groebnerbase(I)
3-element Array{MultivariatePolynomial{ZZmod{7,Int8},2,Symbol("8693009651133194268"),Int64,Tuple{2}},1}:
 x^2 - y
 x*y - x
 y^2 - y

```

## Power Series are Laurent Series

For `F` a field with characteristic `0` (for example `QQ`), it is possible to define
a formal power series of a given "precision" over `F`. You can use them like univariate polynomials. Mind the `O(x^n)` terms, which indicate, the precision of the expression. We support "relative precision", that means the number of non-zero coefficients is capped by the precision indicator. Lower degree polynomials are exact.
The inverse is defined for all power series elements the first coefficient of which is invertible. In the case of `QQ`, that means all except `0`. So this implementation actually supports formal Laurent series.

 The `compose_inv` function delivers the power series expansion for functions `f` with `f(0) == 0 and f'(0) != 0`.

``` julia

P = PowerSeries{10,QQ{BigInt},:x}
PowerSeries{10, QQ{BigInt}, :x}

julia> x = monom(P)
x

julia> 1 / (1 + x)
1 - x + x^2 - x^3 + x^4 - x^5 + x^6 - x^7 + x^8 - x^9 + O(x^10)

julia> ex = P(sum((x)^k / factorial(k) for k = 0:13))
1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4 + 1/120*x^5 + 1/720*x^6 + 1/5040*x^7 + 1/40320*x^8 + 1/362880*x^9 + O(x^10)

julia> inv(ex)
1 - x + 1/2*x^2 - 1/6*x^3 + 1/24*x^4 - 1/120*x^5 + 1/720*x^6 - 1/5040*x^7 + 1/40320*x^8 - 1/362880*x^9 + O(x^10)

julia> inv(ex) * ex
1 + O(x^10)

julia> ex / x
x^-1 + 1 + 1/2*x + 1/6*x^2 + 1/24*x^3 + 1/120*x^4 + 1/720*x^5 + 1/5040*x^6 + 1/40320*x^7 + 1/362880*x^8 + O(x^9)

julia> exm1 = P(sum(x^k / factorial(k) for k = 1:11))
x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4 + 1/120*x^5 + 1/720*x^6 + 1/5040*x^7 + 1/40320*x^8 + 1/362880*x^9 + 1/3628800*x^10 + O(x^11)

julia> compose_inv(exm1)
x - 1/2*x^2 + 1/3*x^3 - 1/4*x^4 + 1/5*x^5 - 1/6*x^6 + 1/7*x^7 - 1/8*x^8 + 1/9*x^9 - 1/10*x^10 + O(x^11)

julia> lg = (sum(-(-x)^k / k for k = 1:12))
x - 1/2*x^2 + 1/3*x^3 - 1/4*x^4 + 1/5*x^5 - 1/6*x^6 + 1/7*x^7 - 1/8*x^8 + 1/9*x^9 - 1/10*x^10 + O(x^11)

julia> compose_inv(lg) == exm1
true
```

## Comparison with [AbstractAlgebra]()

``` julia

julia> using CommuatativeRings

julia> using BenchmarkTools

julia> R = GF(7)
ZZmod{7, Int8}

julia> S = R[:y] # S, y = PolynomialRing(R, "y")
UnivariatePolynomial{ZZmod{7, Int8}, :y}

julia> y = monom(S);

julia> T = S / ( y^3 + 3y + 1); # ResidueRing(S, y^3 + 3y + 1)

julia> U = T[:z]; #U, z = PolynomialRing(T, "z")

julia> z = monom(U);

julia> f = (3y^2 + y + 2)*z^2 + (2*y^2 + 1)*z + 4y + 3;

julia> g = (7y^2 - y + 7)*z^2 + (3y^2 + 1)*z + 2y + 1;

julia> s = f^4;

julia> t = (s + g)^4;

julia> @btime resultant(s, t)
  10.442 ms (259556 allocations: 15.48 MiB)
-y^2 + 3°*y + 4° mod(y^3 + 3°*y + 1°)
```

## Acknowledgements

This package was inspired by the `C++` library `CoCoALib`, which can be found
here: [CoCoALib](http://cocoa.dima.unige.it/cocoalib/).

The factorization of integer polynomials follows the D. Knuths infamous book "The Art of Computer Programming" chapter 4.6.2.

The `signed_resultant_polynomials` are from the book "Algorithms and Computation
in Mathematics" of Basu, et. al.

The power series algorithms are partially from this wikipedia article [Formal Power Series](https://en.wikipedia.org/wiki/Formal_power_series)

### Copyright © 2019-2022 by Klaus Crusius. This work is released under The MIT License

[gha-img]: https://github.com/KlausC/CommutativeRings.jl/workflows/CI/badge.svg
[gha-url]: https://github.com/KlausC/CommutativeRings.jl/actions?query=workflow%3ACI

[codecov-img]: https://codecov.io/gh/KlausC/CommutativeRings.jl/branch/main/graph/badge.svg
[codecov-url]: https://codecov.io/gh/KlausC/CommutativeRings.jl
