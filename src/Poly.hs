{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Poly where

import Common
import Field

data Poly a where
  Poly :: Field a => [a] -> Poly a

instance Show a => Show (Poly a) where
  show (Poly l) = show l

-- | The constant polynomial over 'nw' variables, equal 'c'
const_poly :: Field a => Int -> a -> Poly a
const_poly nw c = Poly $ c : take nw (repeat zero)

-- | The polynomial over 'nw' variables, equal variable 'x'
var_poly :: Field a
         => Int -- ^ Number of variables
         -> (Bool,Var) -- ^ Variable, with polarity
         -> Poly a -- ^ Resulting polynomial
var_poly nw (pos,x)
  | x < nw
  = let c   = if pos then one else neg one
        f y = if x == y then c else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error $ "variable " ++ show x ++ " exceeds bound of " ++ show nw

-- | The polynomial over 'nw' variables, equal 'c + x + y'
cxy_poly :: Field a
         => Int -- ^ Number of variables
         -> a -- ^ Constant a
         -> (Bool,Var) -- ^ Polarity of x, along with x
         -> (Bool,Var) -- ^ Polarity of y, along with y
         -> Poly a -- ^ Resulting polynomial
cxy_poly nw c (pos_x,x) (pos_y,y)
  | x < nw
  , y < nw  
  = let c_x = if pos_x then one else neg one
        c_y = if pos_y then one else neg one
        f z = if x == z then c_x
              else if y == z then c_y
              else zero
    in Poly $ c : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- | The polynomial over 'nw' variables, equal 'c + y'
cy_poly :: Field a => Int -> a -> (Bool,Var)-> Poly a
cy_poly nw c (pos_y,y) = cxy_poly nw c (pos_y,y) (True,-1)

-- | The polynomial over 'nw' variables, equal 'x + y'
add_poly :: Field a => Int -> (Bool,Var) -> (Bool,Var) -> Poly a
add_poly nw x y = cxy_poly nw zero x y

-- | The polynomial over 'nw' variables, equal 'x - y'
sub_poly :: Field a => Int -> (Bool,Var) -> (Bool,Var) -> Poly a
sub_poly nw x (pos_y,y) = add_poly nw x (if pos_y then False else True,y)
