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
  = do { x <- input
       ; let f i = exp_of_int i + x
       ; ret $ summate n f }

-- 3. declare 'a' an array of size 5. the second 'x <- get ...' reads
-- from 'a' at index 4, storing the result in variable 'x' (and shadowing
-- whichever value is assigned to 'x' at input).
prog3 
  = do { x <- input
       ; a <- arr 5           
       ; x <- get a 4
       ; ret x  }

prog4
  = do { a <- arr 5
       ; x <- get a 0
       ; set a 1 x
       ; y <- get a 1
       ; ret y }

-- 4. ...
{- prog4
  = do { x  <- var
       ; w  <- var
       ; a  <- arr 5                    -- an array of size 5
       ; a' <- set a 3 5 w
       ; z  <- ret (summate 5 (get a')) -- sum the elements of the array
       ; ret $ z - x  }                 -- and output the result, minus x
-}

{- prog5
  = do { x <- var
       ; a <- arr 1
       ; a' <- set a 0 1 x
       ; ret $ get a' 0 } -}

-- do_check:
-- (1) compile to R1CS
-- (2) generate a satisfying assignment, w, corresponding to input x
-- (3) check whether 'w' satisfies the constraint system produced in (1)
do_check prog x = putStrLn $ show $ check prog x

main = do_check prog3 [1,1,2,3,4,5]

