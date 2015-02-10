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
var_poly :: Field a => Int -> Atom -> Poly a
var_poly nw x
  | var_of_atom x < nw
  = let f y = if var_of_atom x == y then
                if is_pos x then one else neg one
              else zero
    in Poly $ zero : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- the polynomial over 'nw' variables, equal 'c + x + y'
cxy_poly :: Field a => Int -> a -> Atom -> Atom -> Poly a
cxy_poly nw c x y
  | var_of_atom x < nw
  , var_of_atom y < nw  
  = let f z = if var_of_atom x == z then
                if is_pos x then one else neg one
              else if var_of_atom y == z then 
                if is_pos y then one else neg one
              else zero
    in Poly $ c : take nw (map f [0..])

  | otherwise  
  = error "variable exceeds bound"

-- the polynomial over 'nw' variables, equal 'c + y'
cy_poly :: Field a => Int -> a -> Atom -> Poly a
cy_poly nw c y = cxy_poly nw c y (Pos (-1))

-- the polynomial over 'nw' variables, equal 'x + y'
add_poly :: Field a => Int -> Atom -> Atom -> Poly a
add_poly nw x y = cxy_poly nw zero x y

-- the polynomial over 'nw' variables, equal 'x - y'
sub_poly :: Field a => Int -> Atom -> Atom -> Poly a
sub_poly nw x y = add_poly nw x (neg_atom y)
