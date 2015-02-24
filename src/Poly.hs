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
         => (a,Var) -- ^ Variable, with coeff
         -> Poly a -- ^ Resulting polynomial
var_poly (coeff,x)
  = Poly $ Map.insert x coeff Map.empty    
