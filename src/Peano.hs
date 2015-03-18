{-# LANGUAGE RebindableSyntax
           , DataKinds
           , ScopedTypeVariables
  #-}

module Peano where

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

import Syntax
import Source

nat_zero :: Comp (TMu (TSum TUnit))
nat_zero
  = do { x <- inl unit
       ; fold x
       }

nat_succ :: TExp (TMu (TSum TUnit)) Rational -> Comp (TMu (TSum TUnit))
nat_succ n
  = do { x <- inr n
       ; fold x
       }

nat_eq :: Int
       -> TExp (TMu (TSum TUnit)) Rational
       -> TExp (TMu (TSum TUnit)) Rational
       -> Comp TBool
nat_eq level n m
  | level > 0
  = do { n' <- unfold n
       ; m' <- unfold m
       ; case_sum
         (const $ case_sum (const $ ret true) (const $ ret false) m')
         (\n'' -> case_sum
                  (const $ ret false)
                  (\m'' -> nat_eq (dec level) n'' m'')
                  m')
         n' 
       }

  | otherwise
  = return false

nat_of_int :: Int -> Comp (TMu (TSum TUnit))
nat_of_int 0 = nat_zero
nat_of_int n 
  = do { x <- nat_of_int (dec n)
       ; nat_succ x
       }
    
             
