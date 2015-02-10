{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Field where

import Data.Ratio

class (Show a,Eq a,Ord a) => Field a where
  zero :: a
  one  :: a
  add  :: a -> a -> a
  mult :: a -> a -> a
  neg  :: a -> a
  inv  :: a -> a

instance Field Rational where 
  zero = 0
  one  = 1
  add  = (+)
  mult = (*)
  neg  = \n -> -n
  inv  = \n -> denominator n % numerator n



