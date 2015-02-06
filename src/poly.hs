{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Poly where

import Common
import Field

data Poly a where
  Poly :: Field a => [a] -> Poly a

instance Show a => Show (Poly a) where
  show (Poly l) = show l

-- the constant polynomial over 'nw' variables, equal 'c'
const_poly :: Field a => Int -> a -> Poly a
const_poly nw c = Poly $ c : take nw (repeat zero)

-- the polynomial over 'nw' variables, equal variable 'x'
var_poly :: Field a => Int -> Var -> Poly a
var_poly nw x
  | x < nw
  = let f y = if x == y then one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- the polynomial over 'nw' variables, equal 'x + y'
add_poly :: Field a => Int -> Var -> Var -> Poly a
add_poly nw x y
  | x < nw
  , y < nw  
  = let f z = if x == z || y == z then one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- the polynomial over 'nw' variables, equal 'x - y'
sub_poly :: Field a => Int -> Var -> Var -> Poly a
sub_poly nw x y
  | x < nw
  , y < nw  
  = let f z = if x == z then one else if y == z then neg one else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"
