# Snårkl 

An Embedded DSL for Verifiable Computing

## Build

Snårkl ("Snorkel") builds with GHC version >= 7.8.3 and Cabal version >= 1.22. It may compile with earlier versions as well, but this hasn't been tested. 

To build, from the root directory do:

``` 
> ./prepare-depends.sh
``` 

to download, build, and locally install the 'libsnark' library.

Then do 

```
> make
```

to build Snårkl in a cabal sandbox.

To run the unit tests, do:

```
> make test
```

To run the benchmarks, do: 

```
> make bench
```

The benchmarks target is known not to run on `cygwin`.

## Limitations

Snårkl is a preliminary research prototype undergoing active development.

## Directory Structure

```
snarkl/
  cppsrc/              -- a C++ wrapper around 'libsnark'
  scripts/             -- shell scripts
  src/                 
    Toplevel.hs        -- compiler
    ... 
    examples/          -- some example Snårkl programs that exercise inductive types
     Peano.hs          
     List.hs
     Lam.hs   
     Keccak.hs
    tests/
      testsuite/       -- unit tests
      benchmarks/      -- microbenchmarks
```

## Compiler Overview

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
