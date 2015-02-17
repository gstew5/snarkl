{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Poly where

import qualified Data.Map.Strict as Map

import Common
import Field

data Poly a where
  Poly :: Field a => Map.Map Var a -> Poly a

instance Show a => Show (Poly a) where
  show (Poly m) = show m

-- | The constant polynomial equal 'c'
const_poly :: Field a => a -> Poly a
const_poly c = Poly $ Map.insert (-1) c Map.empty

-- | The polynomial equal variable 'x'
var_poly :: Field a
         => (Bool,Var) -- ^ Variable, with polarity
         -> Poly a -- ^ Resulting polynomial
var_poly (pos,x)
  = let c = if pos then one else neg one
    in Poly $ Map.insert x c Map.empty    

-- | The polynomial equal 'c + x + y'
cxy_poly :: Field a
         => a -- ^ Constant a
         -> (Bool,Var) -- ^ Polarity of x, along with x
         -> (Bool,Var) -- ^ Polarity of y, along with y
         -> Poly a -- ^ Resulting polynomial
cxy_poly c (pos_x,x) (pos_y,y)
  = let c_x = if pos_x then one else neg one
        c_y = if pos_y then one else neg one
    in Poly
       $ Map.insert x c_x
       $ Map.insert y c_y
       $ Map.insert (-1) c Map.empty

-- | The polynomial equal 'c + y'
cy_poly :: Field a => a -> (Bool,Var)-> Poly a
cy_poly c (pos_y,y)
  = let c_y = if pos_y then one else neg one
    in Poly
       $ Map.insert y c_y 
       $ Map.insert (-1) c Map.empty       

-- | The polynomial equal 'x + y'
add_poly :: Field a => (Bool,Var) -> (Bool,Var) -> Poly a
add_poly x y = cxy_poly zero x y

-- | The polynomial equal 'x - y'
sub_poly :: Field a => (Bool,Var) -> (Bool,Var) -> Poly a
sub_poly x (pos_y,y) = add_poly x (if pos_y then False else True,y)
