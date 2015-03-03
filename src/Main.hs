{-# LANGUAGE RebindableSyntax,DataKinds #-}

module Main where

import Prelude hiding 
  ( (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , (&&)        
  , return
  , fromRational
  , negate    
  )
import qualified Prelude as P

import Syntax
import Source

-- | 1. A standalone "program" in the expression language
prog1 
  = do { x <- input -- bool
       ; y <- input -- int
       ; z <- input -- bool
       ; u <- ret $ y + 2.0
       ; v <- ret (if z then y else y)
       ; w <- ret (if x then y else y)
       ; ret $ u*u - w*u*u*y*y*v }

-- | 2. We can also mix Haskell code with R1CS expressions, by defining
-- combinators over R1CS-producing functions.
-- 
-- For example, the following code calculates the R1CS expression
--   (n+e) + (n-1+e) + (n-2+e) + ... + (n-(n-1)+e)
-- with e an input expression.
prog2 n
  = do { e <- input
       ; let f i = exp_of_int i + e
       ; ret $ bigsum n f }

-- | 3. Declare 'a' an array of size 5. initialize slot 3 to e.
-- initialize slot 4 to e*e. return a[3]*a[4]. 
prog3 
  = do { e <- input
       ; a <- arr 5
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | 4. Identical to 3, except allocates larger array
prog4 
  = do { e <- input
       ; a <- arr 1000
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | 5. Identical to 4, except with more constraints
pow :: Int -> TExp TField Rational -> TExp TField Rational
pow 0 _ = 1.0
pow n e = e*(pow (dec n) e)

prog5 
  = do { e <- input
       ; a <- arr 1000
       ; set (a,3) e
       ; set (a,4) (pow 100 e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y) }

-- | 6. 'times' test
prog6 
  = do { e <- input
       ; a <- arr 100
       ; times 1 (set (a,3) e)
       ; x <- get (a,3)
       ; ret x }

-- | 7. 'forall' test
prog7 
  = do { a <- arr 100
       ; forall [0..99] (\i -> set (a,i) 0.0)              
       ; forall [0..99] (\i -> set (a,i) (exp_of_int i))
       ; x <- get (a,49)
       ; y <- get (a,51)              
       ; ret $ x + y }

-- | 8. 'forall_pairs' test
prog8 
  = do { a <- arr 25
       ; forall [0..24] (\i -> set (a,i) 0.0)              
       ; let index i j = (P.+) ((P.*) 5 i) j
       ; forall_pairs ([0..4],[0..4]) (\i j ->
           set (a,index i j) (exp_of_int $ index i j))
       ; x <- get (a,5)  -- 5
       ; y <- get (a,24) -- 24
       ; ret $ x + y }

-- | 9. 'and' test
bool_prog9 
  = do { e1 <- input
       ; e2 <- input
       ; ret (e1 && e2) }

-- | 10. 'xor' test
bool_prog10 
  = do { e1 <- input
       ; e2 <- input
       ; ret (e1 `xor` e2) }

-- | 11. are unused input variables treated properly?
prog11
  = do { _ <- input
       ; b <- input
       ; ret b }

-- | 12. does boolean 'a' equal boolean 'b'?
bool_prog12
  = do { a <- input
       ; b <- input
       ; ret (a `eq` b)
       }

-- | 13. multiplicative identity
prog13
  = do { a <- input
       ; ret $ 1.0 * a
       }

-- | 14. opt: 0x * 3y = out ~~> out=0
prog14
  = do { x <- input
       ; y <- input
       ; ret $ (0.0*x) * (3.0*y)
       }

-- | 15. exp_binop smart constructor: 3 - (2 - 1) = 2
prog15
  = do { ret $ 3.0 - (2.0 - 1.0)
       }

-- | 16. const_prop 
prog16
  = do { a <- arr 20
       ; set (a,3) true
       ; b <- get (a,3)
       ; ret $ if b then 5.0 else 0.0
       }


-- tests :: [(Comp ty,[Rational],Rational)]
tests
  = [ (prog1, map fromIntegral [(1::Int),0,1], 0)

    , (prog2 4, [fromIntegral (0::Int)], 10)
    , (prog2 4, [fromIntegral (1::Int)], 15)
    , (prog2 4, [fromIntegral (2::Int)], 20)      
    , (prog2 10, [fromIntegral (10::Int)], 165)

    , (prog3, [fromIntegral (8::Int)], 512)
    , (prog3, [fromIntegral (16::Int)], 4096)
    , (prog3, [fromIntegral (0::Int)], 0)
    , (prog3, [fromIntegral (dec 0::Int)], fromIntegral $ dec 0)            

    , (prog4, [fromIntegral (8::Int)], 512)
    , (prog4, [fromIntegral (16::Int)], 4096)
    , (prog4, [fromIntegral (0::Int)], 0)
    , (prog4, [fromIntegral (dec 0::Int)], fromIntegral $ dec 0)            

    , (prog5, [fromIntegral (8::Int)], 8^(101::Int))
    , (prog5, [fromIntegral (16::Int)], 16^(101::Int))
    , (prog5, [fromIntegral (0::Int)], 0)
    , (prog5, [fromIntegral (dec 0::Int)], fromIntegral $ dec 0)

    , (prog6, [fromIntegral (8::Int)], 8)

    , (prog7, [], 100)

    , (prog8, [], 29)

    , (prog11, map fromIntegral [1::Int,1], 1)

    , (prog13, map fromIntegral [1::Int], 1)

    , (prog14, map fromIntegral [3::Int,4], 0)

    , (prog15, [], 2)

    , (prog16, [], 5)                        
    ]

bool_tests 
  = [ (bool_prog9, map fromIntegral [0::Int,0], 0)
    , (bool_prog9, map fromIntegral [0::Int,1], 0)
    , (bool_prog9, map fromIntegral [1::Int,0], 0)
    , (bool_prog9, map fromIntegral [1::Int,1], 1) 

    , (bool_prog10, map fromIntegral [0::Int,0], 0)
    , (bool_prog10, map fromIntegral [0::Int,1], 1)
    , (bool_prog10, map fromIntegral [1::Int,0], 1)
    , (bool_prog10, map fromIntegral [1::Int,1], 0)

    , (bool_prog12, map fromIntegral [0::Int,0], 1)
    , (bool_prog12, map fromIntegral [0::Int,1], 0)
    , (bool_prog12, map fromIntegral [1::Int,0], 0)
    , (bool_prog12, map fromIntegral [1::Int,1], 1)
    ]

main = (P.>>) (mapM_ run_test tests)
              (mapM_ run_test bool_tests)

