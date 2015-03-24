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
import Peano
import Lam
import List

-- | 1. A standalone "program" in the expression language
prog1 
  = do { x <- input -- bool
       ; y <- input -- int
       ; z <- input -- bool
       ; u <- ret $ y + 2.0
       ; v <- if z then y else y
       ; w <- if x then y else y
       ; ret $ u*u - w*u*u*y*y*v
       }

-- | 2. We can also mix Haskell code with R1CS expressions, by defining
-- combinators over R1CS-producing functions.
-- 
-- For example, the following code calculates the R1CS expression
--   (n+e) + (n-1+e) + (n-2+e) + ... + (n-(n-1)+e)
-- with e an input expression.
prog2 n
  = do { e <- input
       ; let f i = exp_of_int i + e
       ; ret $ bigsum n f
       }

-- | 3. Declare 'a' an array of size 5. initialize slot 3 to e.
-- initialize slot 4 to e*e. return a[3]*a[4]. 
prog3 
  = do { e <- input
       ; a <- arr 5
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y)
       }

-- | 4. Identical to 3, except allocates larger array
prog4 
  = do { e <- input
       ; a <- arr 1000
       ; set (a,3) e
       ; set (a,4) (e*e)         
       ; x <- get (a,3)
       ; y <- get (a,4)
       ; ret (x*y)
       }

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
       ; ret (x*y)
       }

-- | 6. 'times' test
prog6 
  = do { e <- input
       ; a <- arr 100
       ; times 1 (set (a,3) e)
       ; x <- get (a,3)
       ; ret x
       }

-- | 7. 'forall' test
prog7 
  = do { a <- arr 100
       ; forall [0..99] (\i -> set (a,i) 0.0)              
       ; forall [0..99] (\i -> set (a,i) (exp_of_int i))
       ; x <- get (a,49)
       ; y <- get (a,51)              
       ; ret $ x + y
       }

-- | 8. 'forall2' test
prog8 
  = do { a <- arr 25
       ; forall [0..24] (\i -> set (a,i) 0.0)              
       ; let index i j = (P.+) ((P.*) 5 i) j
       ; forall2 ([0..4],[0..4]) (\i j ->
           set (a,index i j) (exp_of_int $ index i j))
       ; x <- get (a,5)  -- 5
       ; y <- get (a,24) -- 24
       ; ret $ x + y
       }

-- | 9. 'and' test
bool_prog9 
  = do { e1 <- input
       ; e2 <- input
       ; ret (e1 && e2)
       }

-- | 10. 'xor' test
bool_prog10 
  = do { e1 <- input
       ; e2 <- input
       ; ret (e1 `xor` e2)
       }

-- | 11. are unused input variables treated properly?
prog11
  = do { _ <- input :: Comp ('TArr 'TField)
       ; b <- input
       ; ret b
       }

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

-- | 16. bool inputs test
bool_prog16
  = do { a <- input_arr 100
       ; forall [0..99] (\i ->
           do b <- get (a,i)
              set (a,i) (b && true))
       ; ret false
       }

-- | 17. array test
bool_prog17
  = do { a  <- arr 2
       ; a' <- arr 2
       ; set (a',0) true
       ; set (a,0) a'
       ; get2 (a,0,0) 
       }

-- | 18. input array test
bool_prog18
  = do { a  <- input_arr3 2 2 2
       ; get3 (a,0,0,1) 
       }

-- | 19. products test
bool_prog19
  = do { x <- input
       ; y <- input
       ; p <- pair x y
       ; c <- fst_pair p
       ; d <- snd_pair p
       ; ret $ c && d
       }

-- | 20. products test 2: snd (fst ((x,y),x)) && x == y && x 
bool_prog20
  = do { x <- input
       ; y <- input
       ; p <- pair x y
       ; q <- pair p x
       ; c <- fst_pair q
       ; d <- snd_pair c
       ; ret $ d && x
       }

-- | 21. products test 3: snd (fst ((x,y),(y,x))) && x == y && x 
bool_prog21
  = do { x <- input
       ; y <- input
       ; p <- pair x y
       ; q <- pair y x              
       ; u <- pair p q
       ; c <- fst_pair u
       ; d <- snd_pair c
       ; ret $ d && x
       }

-- | 22. sums test
bool_prog22
  = do { x1 <- input
       ; x2 <- input
       ; x <- pair x1 x2
       ; y <- (inl x :: Comp (TSum (TProd TBool TBool) TBool))
       ; case_sum
           (\e1 -> snd_pair e1)
           (\e2 -> ret e2)
           y
       }

-- | 23. sums test 2
bool_prog23
  = do { x1 <- input
       ; x2 <- input
       ; x <- pair x1 x2
       ; y <- (inr x :: Comp (TSum (TProd TBool TBool)
                                   (TProd TBool TBool)))
       ; z <- (inl y :: Comp (TSum (TSum (TProd TBool TBool)
                                         (TProd TBool TBool))
                                   (TProd TBool TBool))) 
       ; case_sum
           (case_sum
              fst_pair
              fst_pair)
           fst_pair           
           z
       }

-- | 24. peano test 1
bool_prog24
  = do { n2 <- nat_of_int 3
       ; n3 <- nat_of_int 3
       ; nat_eq 4 n2 n3
       }

-- | 25. lam test 1
bool_prog25
  = do { t <- term1
       ; t' <- shift 2 (exp_of_int 2) t
       ; is_lam t'
       }

-- | 26. list test 1
prog26
  = do { l <- list1 
       ; head_list (exp_of_int 0) l
       }

-- | 27. list test 2
prog27
  = do { l <- list2
       ; head_list (exp_of_int 0) l
       }

-- | 28. list test 3
prog28 
  = do { l <- list2
       ; l' <- tail_list l
       ; head_list (exp_of_int 0) l'
       }

-- | 29. list test 4
prog29 
  = list_comp3

-- | 30. list test 5
prog30
  = list_comp4

tests :: [(Comp 'TField,[Int],Integer)]
tests
  = [ (prog1, [1,0,1], 0)

    , (prog2 4, [0], 10)
    , (prog2 4, [1], 15)
    , (prog2 4, [2], 20)      
    , (prog2 10, [10], 165)

    , (prog3, [8], 512)
    , (prog3, [16], 4096)
    , (prog3, [0], 0)
    , (prog3, [dec 0], fromIntegral $ dec 0)            

    , (prog4, [8], 512)
    , (prog4, [16], 4096)
    , (prog4, [0], 0)
    , (prog4, [dec 0], fromIntegral $ dec 0)            

    , (prog5, [8], 8^(101::Int))
    , (prog5, [16], 16^(101::Int))
    , (prog5, [0], 0)
    , (prog5, [dec 0], fromIntegral $ dec 0)

    , (prog6, [8], 8)

    , (prog7, [], 100)

    , (prog8, [], 29)

    , (prog11, [1,1], 1)

    , (prog13, [1], 1)

    , (prog14, [3,4], 0)

    , (prog15, [], 2)

    , (prog26, [], 33)

    , (prog27, [], 34)

    , (prog28, [], 24)

    , (prog29, [1], 24)

    , (prog30, [], 24)      
    ]

bool_tests :: [(Comp 'TBool,[Int],Integer)]
bool_tests 
  = [ (bool_prog9, [0,0], 0)
    , (bool_prog9, [0,1], 0)
    , (bool_prog9, [1,0], 0)
    , (bool_prog9, [1,1], 1) 

    , (bool_prog10, [0,0], 0)
    , (bool_prog10, [0,1], 1)
    , (bool_prog10, [1,0], 1)
    , (bool_prog10, [1,1], 0)

    , (bool_prog12, [0,0], 1)
    , (bool_prog12, [0,1], 0)
    , (bool_prog12, [1,0], 0)
    , (bool_prog12, [1,1], 1)

    , (bool_prog16, take 100 $ repeat 1, 0)

    , (bool_prog17, [], 1)

    , (bool_prog18, [0,1,0,1,0,1,0,1], 1)

    , (bool_prog19, [1,1], 1)

    , (bool_prog20, [1,1], 1)

    , (bool_prog21, [0,1], 0)

    , (bool_prog22, [0,1], 1)

    , (bool_prog23, [0,1], 0)

    , (bool_prog24, [], 1)

    , (bool_prog25, [], 1)                        
    ]

main
  = (P.>>)
      (mapM_ test bool_tests)    
      (mapM_ test tests)

