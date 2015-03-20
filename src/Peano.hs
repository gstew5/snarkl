{-# LANGUAGE RebindableSyntax
           , DataKinds
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

type TF = TFSum (TFConst TUnit) TFId 

type TNat = TMu TF

nat_zero :: Comp TNat
nat_zero 
  = do { x <- inl unit 
       ; roll x
       }

nat_succ :: TExp TNat Rational -> Comp TNat
nat_succ n
  = do { x <- inr n
       ; roll x
       }

nat_eq :: Int
       -> TExp TNat Rational
       -> TExp TNat Rational
       -> Comp TBool
nat_eq level n m
  | level > 0
  = do { n' <- privately $ unroll n
       ; m' <- unroll m
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

nat_of_int :: Int -> Comp TNat
nat_of_int 0 = nat_zero
nat_of_int n 
  = do { x <- nat_of_int (dec n)
       ; nat_succ x
       }
            
