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
  , negate    
  )
import qualified Prelude as P

import Syntax
import Lang

-- | 1. A standalone "program" in the expression language
prog1 x y z
  = do { u <- ret (if x + y then y else z)
       ; v <- ret (if z then x else y)
       ; w <- ret (if x then y else z)
       ; ret $ x + u*z - w*u*u*y*y*v }

-- | 2. We can also mix Haskell code with R1CS expressions, by defining
-- combinators over R1CS-producing functions.
-- 
-- For example, the following code calculates the R1CS expression
--   (n+e) + (n-1+e) + (n-2+e) + ... + (n-(n-1)+e)
-- with e an input expression.
prog2 e n
  = do { let f i = exp_of_int i + e
       ; ret $ bigsum n f }

-- | 3. Declare 'a' an array of size 5. initialize slot 3 to e.
-- initialize slot 4 to e*e. return a[3]*a[4]. 
prog3 e
  = do { a <- arr 5
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | 4. Identical to 3, except allocates larger array
prog4 e
  = do { a <- arr 1000
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | 5. Identical to 4, except with more constraints
pow :: Int -> Exp Rational -> Exp Rational
pow 0 e = 1.0
pow n e = e*(pow (dec n) e)

prog5 e
  = do { a <- arr 1000
       ; set (a,3) e
       ; set (a,4) (pow 100 e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, w.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check that results match.
run_test (prog,res) =
  case check prog [] of
    r@(Result True vars constrs res') ->
      case res == res' of
        True  ->  putStrLn (show r)
        False ->  putStrLn $ show $ "error: results don't match: "
                  ++ "expected " ++ show res ++ " but got " ++ show res'
    r@(Result False vars constrs res') ->
      putStrLn "error: witness failed to satisfy constraints"

tests
  = [ (prog1 1.0 0.0 1.0, 0)

    , (prog2 0.0 4, 10)
    , (prog2 1.0 4, 15)
    , (prog2 2.0 4, 20)      
    , (prog2 10.0 10, 165)            

    , (prog3 8.0, 512)
    , (prog3 16.0, 4096)
    , (prog3 0.0, 0)
    , (prog3 (-1.0), 1)            

    , (prog4 8.0, 512)
    , (prog4 16.0, 4096)
    , (prog4 0.0, 0)
    , (prog4 (-1.0), 1)            

    , (prog5 8.0, 8^101)
    , (prog5 16.0, 16^101)
    , (prog5 0.0, 0)
    , (prog5 (-1.0), 1)            
    ]

main = mapM_ run_test tests

