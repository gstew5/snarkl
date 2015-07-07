# Snårkl 

An Embedded DSL for Verifiable Computing

# Background

Snårkl ("Snorkel") is a high-level language and compiler for verifiable computing. For an introduction to verifiable computing (VC), see the fine [ACM review article](http://cacm.acm.org/magazines/2015/2/182636-verifying-computations-without-reexecuting-them/fulltext) by Walfish and Blumberg. For details on [libsnark](https://github.com/scipr-lab/libsnark), the C++ library targeted by the Snårkl compiler, see, e.g. [SNARKs for C](http://eprint.iacr.org/2013/507) by Ben-Sasson et al.  

# Quickstart


```
git clone https://github.com/gstew5/snarkl.git snarkl
cd snarkl
./prepare-depends.sh
make
```

Dependencies: 

* GHC version >= 7.10.1;
* Cabal version >= 1.22.2.

Things may work with earlier versions, but this hasn't been tested.

# Limitations

Snårkl is a preliminary research prototype undergoing active development. Pull requests welcome!

# Directory Structure

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
     Tree.hs
     Lam.hs   
     Keccak.hs
    tests/
      testsuite/       -- unit tests
      benchmarks/      -- microbenchmarks
```

# Compiler Overview

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

# Development Environment

Snårkl programs are shallowly embedded in Haskell through the use of 

* Snårkl's `Syntax` and `SyntaxMonad` modules, which define the combinators of the Snårkl language, and 
* the Snårkl `Toplevel`, which exposes the API of the Snårkl compiler.
 
The easiest way to interact with these libraries is in Emacs, using [Haskell's Interactive Mode](https://github.com/haskell/haskell-mode/wiki/Haskell-Interactive-Mode-Setup). Assuming you have a modern `cabal`, set your REPL to `cabal-repl` by adding the following to your `.emacs`:

```
(custom-set-variables
  '(haskell-process-type 'cabal-repl))
```

Navigate to the source directory of the repository and open one of the Snårkl examples:

```
emacs src/examples/Basic.hs
```

Type `C-c C-l` and follow the prompts. In the bottom-left status bar of your Emacs window, you should see a bunch of libraries compiling, followed by `OK.` If you don't see `OK`, something is probably misconfigured.

# Programming 

The Snårkl source language supports a number of expressive features, including: higher-order functions and parametric polymorphism (via the embedding in Haskell) as well as user-defined inductive datatypes. 
In this section, we'll step through `src/examples/Basic.hs` and `src/examples/Tree.hs`, which give examples of many of these features in action. 

## Preliminaries

From the base of the Snårkl repository, start `emacs` and open `src/examples/Basic.hs` (`C-x C-f src/examples/Basic.hs`).

At the top of the file, you'll see the declarations: 

```
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
```

These turn on two [GHC](https://www.haskell.org/ghc/) Haskell extensions required by Snårkl. They must appear in every Snårkl program.

* `RebindableSyntax` gives us a clean slate to re-implement basic Haskell syntax (e.g., Haskell's monadic `>>=` bind). This way, we're able to overload Haskell's monadic `do` (examples below).
* `DataKinds` facilitates the use of Snårkl's GADT-style typed expression language (`src/TExpr.hs`). The details here are unimportant.  

Next comes the `module` declaration and imports:

```
module Basic where

import Prelude hiding
  ( (>>), (>>=), (+), (-), (*), (/), (&&)
  , return, fromRational, negate
  )

import Syntax
import SyntaxMonad
import TExpr
import Toplevel                                                         
```

When importing the Haskell `Prelude` we hide the standard definitions of functions re-implemented by Snårkl (you'll find the definitions of these functions in `Syntax` and `SyntaxMonad`). `TExpr` gives the deeply embedded typed expression language manipulated by high-level Snårkl programs. `Toplevel` imports the Snårkl compiler and its API.

## Builtin Types

Out of the box, Snårkl supports arithmetic over (bounded) rationals. The following program

```
mult_ex :: TExp 'TField Rational -> TExp 'TField Rational-> Comp 'TField
mult_ex x y = return (x * y)
```

takes two Snårkl expressions as arguments (`TExp 'TField Rational` is the type of Snårkl expressions of type `'TField` ["field element"], specialized to underlying field `Rational`) and returns their product. The naked expression `x * y`, of type `TExp 'TField Rational` is wrapped inside a `return`, coercing it to a Snårkl computation (`Comp 'TField` ["Snårkl computation returning a field element"]). 

Snårkl also supports array-structured computation: 

```
arr_ex :: TExp 'TField Rational -> Comp 'TField
arr_ex x = do
  a <- arr 2
  forall [0..1] (\i -> set (a,i) x)
  y <- get (a,0)
  z <- get (a,1)
  return $ y + z
```

Here we sequence imperative computation steps using Haskell's `do` notation. 

* The first line `a <- arr 2` allocates an array of size `2`, bound in the rest of the computation to variable `a`. 
* `forall [0..1] (\i -> set (a,i) x)` assigns the expression `x` to every index of the array. In general, the `forall` combinator takes as arguments a list of integers `l`, which may or may not be contiguous, and a function from integers to Snårkl computations.
* `y <- get (a,0)` dereferences the array at index `0`.
* And likewise for `z <- ...` at `1`.
* Finally, we return the sum of `y` and `z`.

## Desugaring

The `Toplevel` provides support for "desugaring" high-level Snårkl computations. 

```
p1 = arr_ex 1.0
λ> texp_of_comp p1
TExpPkg {comp_num_vars = 4, comp_input_vars = [], comp_texp = var 2 := 1 % 1; var 3 := 1 % 1; var 2+var 3}

```

Calling `texp_of_comp` on a Snårkl computation (e.g., of type `Comp 'TField`) produces a `TExpPkg` record that gives: 

* the number of variables generated during desugaring;
* the number of "input" variables (these are variables that must be instantiated by the user when the expression is compiled to R1CS form);
* the resulting expression.  

In the case of `p1 = arr_ex 1.0`, the expression assigns `var 2 := 1 % 1` (`1 % 1` is Haskell syntax for the rational `1/1`), `var 3 := 1 % 1`, and returns the result of `var 2 + var 3`.

## Interpreter

Snårkl computations can also be interpreted.

```
λ> comp_interp p1 []
2 % 1
```

Under the hood, `comp_interp` desugars the computation (e.g., `p1`) and interprets the resulting `TExp`. The second (here the empty list `[]`) is the sequence of input values to be assigned to the program's input variables (if any).

## R1CS Inputs

Snårkl computations may require inputs (`fresh_input`), in addition to function arguments. At the R1CS-level, inputs correspond to constraint variables that are instantiated by the user.

```
p2 = do
  x <- fresh_input
  return $ x + x
```

When desugared, `p2` generates the `TExpPkg`

```
TExpPkg {comp_num_vars = 1, comp_input_vars = [0], comp_texp = var 0+var 0}
```

in which variable `0` is marked as an explicit input. When interpreting an expression with inputs, it's necessary to supply values for each input variable.

```
λ> comp_interp p2 []
*** Exception: unbound var 0 in environment fromList []
λ> comp_interp p2 [256]
512 % 1
```

# Compiling and Evaluating Rank-1 Constraints

The Snårkl toplevel makes it relatively easy to compile a Snårkl computation to R1CS-form (using `r1cs_of_comp`) and then to "execute" the result (`snarkify_comp`). 

For example,

```
λ> r1cs_of_comp p2
([fromList [(-1,1 % 1)]*fromList [(-1,0 % 1),(0,2 % 1),(1,(-1) % 1)]==fromList [(-1,0 % 1)]],2,[0],[1])
```

compiles `p2` to the R1CS whose serialization reads: `1 * (0 + 2*x_0 - 1*x_1) = 0`: 
* `x_0` is the input variable; 
* `x_1` is the result; 
* `x_1 = x_0 + x_0` if and only if the equation (on polynomials) `1 * (0 + 2*x_0 - 1*x_1) = 0` is satisfiable. (For a detailed introduction to rank-1 constraints, see [libsnark](https://github.com/scipr-lab/libsnark) and associated papers.)

Running `p2` through [libsnark](https://github.com/scipr-lab/libsnark) yields success! 

```
λ> snarkify_comp "p2" p2 [1.0]
Verification Succeeded.
ExitSuccess
```

The effect of this command is to 
* compile `p2` to Snårkl's internal R1CS abstract syntax;
* serialize the resulting R1CS into a text file that [libsnark](https://github.com/scipr-lab/libsnark) understands;
* use `libsnark` to generate, from the input R1CS configuration, a proving key and a verification key;
* calculate a satisfying assignment for the R1CS;
* use `libsnark` to generate a cryptographic proof for the R1CS, given the satisfying assignment; 
* finally, run the `libsnark` verifier on the resulting proof object and report the result.

Most of the `libsnark`-related steps above are carried out by a `scripts/run-r1cs.sh`.

# Advanced Features

## User-Defined Inductive Types

The Snårkl repository contains a number of examples of user-defined inductive types (`src/examples/Peano.hs`, `src/examples/List.hs`, `src/examples/Tree.hs`). In each of these files, the inductive types (for natural numbers, lists, and trees, respectively) are built against the following pattern:

* Encode the generating functor of the inductive type as a (deeply embedded) type-level function.
* Define the inductive type as the least fixed point (LFP) of the generating functor.
* Define introduction and elimination forms, for interacting with values of the inductive type.

### Generating Functors

For example, the following type `TF` defines the generating functor of the type of binary rational trees.

```
type TF = 'TFSum ('TFConst 'TUnit) ('TFProd ('TFConst 'TField) ('TFProd 'TFId 'TFId))
```

In more standard notation:

```
TF(T) = unit + (Rational x (T x T))
```

The deeply embedded syntax of type-level functions is given by:

```
data TFunct where
  TFConst :: Ty -> TFunct
  TFId :: TFunct
  TFProd :: TFunct -> TFunct -> TFunct
  TFSum :: TFunct -> TFunct -> TFunct
  TFComp :: TFunct -> TFunct -> TFunct
  deriving Typeable
```

`TFComp` is functor composition.

### Least Fixed Points

To take the LFP, we use Snårkl's μ (`'TMu`) type constructor:

```
type RatTree = 'TMu TF
``` 

We can also define polymorphic inductive types, as Haskell type-level functions:

```
type TF' a = 'TFSum ('TFConst 'TUnit) ('TFProd ('TFConst a) ('TFProd 'TFId 'TFId))

type TTree a = 'TMu (TF' a)

type Rat    = TExp 'TField Rational
type Tree a = TExp (TTree a) Rational
```

This pattern is especially convenient when writing libraries.

### Introduction and Elimination Forms

To construct and destruct values of the inductive type, we define

* the constructors of the new type (the introduction forms); 
* elimination, or case-analysis functions, which make it possible to use values of the inductive type.

#### Constructors

For example, here is the `leaf` constructor for the type `TTree` given above:

```
leaf :: Typeable a => Comp (TTree a)
leaf = do
  t <- inl unit
  roll t 
```

The polymorphic version of this type has mathematical form: 

```
TF'(α, T) = unit + (α x (T x T))
```

The type itself is the LFP of the functor `TF'`, or `'TMu TF'`. To construct a "leaf" value (of type unit), we:

* use the `inl` constructor of the sum type to take a value of type `unit` to a value of type `unit + (α x (TTree α x TTree α))`;
* "roll" this value to type `TTree α` using Snårkl's `roll` combinator, which has type 

```
roll :: (Typeable f, Typeable (Rep f ('TMu f)))
     => TExp (Rep f ('TMu f)) Rational
     -> Comp ('TMu f)
``` 

In more standard notation, `roll` takes a value of type `F (μ F)`, for generating functor `F`, and produces a value of type `μ F`. There is also the symmetric `unroll`, which takes a value of type `μ F` and produces a value of type `F (μ F)`.

The `node` constructor is similar to `leaf`, except we take three arguments instead of none: `v` the node value, `t1` the left subtree, and `t2` the right subtree.

```
node :: Typeable a => TExp a Rational -> Tree a -> Tree a -> Comp (TTree a)
node v t1 t2 = do
  p  <- pair t1 t2
  p' <- pair v p 
  t  <- inr p'
  roll t
```

Instead of `inl`, we use the symmetric `inr` sum-type constructor to build a value of the right-side type `(α x (TTree α x TTree α))`. `pair` is the standard constructor for product types.

#### Eliminators

The following is the sole eliminator for trees.

```
case_tree :: ...
          => Tree a 
          -> Comp a1
          -> (TExp a Rational -> Tree a -> Tree a -> Comp a1)
          -> Comp a1
case_tree t f_leaf f_node = do
  t' <- unroll t
  case_sum (\_ -> f_leaf) go t'
  where go p' = do
          v  <- fst_pair p'
          p  <- snd_pair p'
          t1 <- fst_pair p
          t2 <- snd_pair p
          f_node v t1 t2
```

It takes three arguments: 
* the tree `t`;
* a computation `f_leaf` to run when `t` has form `leaf`;
* a computation `f_node` to run, on arguments `v`, `t1`, and `t2`, when `t` has form `node v t1 t2`.

The implementation of the function is in terms of the eliminators of the underlying representation types: `case_sum`, for eliminating values of sum type (to distinguish between leaves and nodes), and `fst_pair` and `snd_pair` for products (to further destruct node values).   

The eliminator `case_tree` comes in handy when defining higher-level functions on trees, such as `fmap`:

```
map_tree :: ...
         => (TExp a Rational -> State Env (TExp a1 Rational))
         -> TExp (TTree a) Rational
            -> Comp (TTree a1)
map_tree f t
  = fix go t
  where go self t0 = do 
          case_tree t0
            leaf
            (\v t1 t2 -> do
                v'  <- f v
                t1' <- self t1
                t2' <- self t2
                node v' t1' t2') 
```

`fix` is Snårkl's fixpoint combinator. It has type:

```
Typeable ty2 => ((TExp ty1 Rational -> Comp ty2) -> TExp ty1 Rational -> Comp ty2)
             -> TExp ty1 Rational 
             -> Comp ty2
```
