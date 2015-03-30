# TinyLam

An Embedded DSL for Verifiable Computing

## Build

TinyLam builds with GHC version >= 7.8.3. It may compile with earlier versions as well, but this hasn't been tested. First `cabal install` packages `mtl` and `parallel`. Then do:

```
> cd src
> make
```
## Examples

[Main.hs](https://github.com/gstew5/tinylam/blob/master/src/Main.hs) contains some small TinyLam programs, used for testing purposes. [app/keccak/Main.hs](https://github.com/gstew5/tinylam/blob/master/src/app/keccak/Main.hs), which can be built by

```
> make keccak
```

from the `src` directory, contains an implementation of the Keccak (SHA3) round function. 
[List.hs](https://github.com/gstew5/tinylam/blob/master/src/List.hs), 
[Peano.hs](https://github.com/gstew5/tinylam/blob/master/src/Peano.hs), 
[Lam.hs](https://github.com/gstew5/tinylam/blob/master/src/Lam.hs)
contain programs that make use of inductive types.

## Limitations

TinyLam is a preliminary research prototype undergoing active development. Although the compiler generates rank-1 constraint systems suitable as input to systems like [scipr-lab/libsnark](https://github.com/scipr-lab/libsnark), the connection to `libsnark` hasn't yet been implemented.

## Overview of Main Files

### Languages

* [Syntax.hs](https://github.com/gstew5/tinylam/blob/master/src/Syntax.hs): Shallowly embedded source language

* [TExpr.hs](https://github.com/gstew5/tinylam/blob/master/src/TExpr.hs): A simple embedded intermediate language (statically typed)

* [Expr.hs](https://github.com/gstew5/tinylam/blob/master/src/Expr.hs): Like `TExpr` but types have been erased

* [Constraints.hs](https://github.com/gstew5/tinylam/blob/master/src/Constraints.hs): The intermediate arithmetic constraint language

* [R1CS.hs](https://github.com/gstew5/tinylam/blob/master/src/R1CS.hs): Rank-1 constraint systems

### Compiler Phases

#### `Source`

* `Source` to `TExpr` [Syntax.hs](https://github.com/gstew5/tinylam/blob/master/src/Syntax.hs)

#### `TExpr`

* `TExpr` to `Expr` [TExpr.hs](https://github.com/gstew5/tinylam/blob/master/src/Compile.hs)

#### `Expr`

* `Expr` to `Constraints` [Compile.hs](https://github.com/gstew5/tinylam/blob/master/src/Compile.hs)

#### `Constraints`

* `Constraint Minimization` [Simplify.hs](https://github.com/gstew5/tinylam/blob/master/src/Simplify.hs)

* `Dataflow Analysis` [Dataflow.hs](https://github.com/gstew5/tinylam/blob/master/src/Dataflow.hs)

* `Renumbering` [Constraints.hs](https://github.com/gstew5/tinylam/blob/master/src/Constraints.hs)

* `Constraints` to `R1CS` [Constraints.hs](https://github.com/gstew5/tinylam/blob/master/src/Constraints.hs)

#### `R1CS`
