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
prog1 
  = do { x <- var
       ; y <- var
       ; z <- var
       ; u <- ret (if x + y then y else z)
       ; v <- ret (if z then x else y)
       ; w <- ret (if x then y else z)
       ; ret $ x + u*z - w*u*u*y*y*v }

-- 2. we can also mix Haskell code with R1CS expressions, by defining
-- combinators over R1CS-producing functions.

-- for example, the following code calculates the R1CS expression
--   n + n-1 + n-2 + ... + n-(n-1) + x
-- with x an input variable.
prog2 n
  = do { x <- var
       ; let f i = exp_of_int i + x
       ; ret $ summate n f }

-- 3. and this little program sums over an "array"...
prog3 
  = do { x <- var
       ; a <- arr 5                       -- an array of size 5
       ; y <- ret (summate 5 (arr_get a)) -- sum the elements of the array
       ; ret $ y - x  }                   -- and output the result, minus x

do_check prog w = putStrLn $ show $ check prog w

main = do_check prog3 [1,1,2,3,4,5]

