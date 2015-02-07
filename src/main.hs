{-# LANGUAGE RebindableSyntax #-}

module Main where

import Prelude hiding 
  ( ifThenElse 
  , (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , return
  , fromRational
  )
import qualified Prelude as P  

import Syntax
import Lang

-- 1. a standalone "program" in the expression language
prog1 x y z
  = do { u <- ret (if x + y then y else z)
       ; v <- ret (if z then x else y)
       ; w <- ret (if x then y else z)
       ; ret $ x + u*z - w*u*u*y*y*v }

-- 2. we can also mix Haskell code with R1CS expressions, by defining
-- combinators over R1CS-producing functions.

-- for example, the following code calculates the R1CS expression
--   n + n-1 + n-2 + ... + n-(n-1) + e
-- with e an input expression.
prog2 e n
  = do { let f i = exp_of_int i + e
       ; ret $ summate n f }

-- 3. declare 'a' an array of size 5. initialize slot 3 to e.
-- initialize slot 4 to e*e. return a[3]*a[4]. 
prog3 e
  = do { a <- arr 5
       ; set a 3 e
       ; set a 4 (e*e)         
       ; x <- get a 3
       ; y <- get a 4
       ; ret (x*y) }
         
-- do_check:
-- (1) compile to R1CS
-- (2) generate a satisfying assignment, w
-- (3) check whether 'w' satisfies the constraint system produced in (1)
do_check prog = putStrLn $ show $ check prog []

main = do_check (prog3 (fromRational 8))

