{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}

module Basic where

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
import SyntaxMonad
import TExpr
import Compile
import Toplevel

mult_ex ::
     TExp 'TField Rational
  -> TExp 'TField Rational
  -> Comp 'TField
mult_ex x y = return $ x * y

arr_ex :: TExp 'TField Rational -> Comp 'TField
arr_ex x = do
  a <- arr 2
  forall [0..1] (\i -> set (a,i) x)
  y <- get (a,0)
  z <- get (a,1)
  return $ y + z

p1 = arr_ex 1.0

desugar1 = texp_of_comp p1

interp1  = comp_interp p1 []

p2 = do
  x <- fresh_input
  return $ x + x

desugar2 = texp_of_comp p2

interp2  = comp_interp p2 []
interp2' = comp_interp p2 [256]

compile1 = r1cs_of_comp Simplify p1

run1 = snarkify_comp "example" Simplify p1 []

comp1 = inl false

comp2 = inr 0.0

test1 = do
  b <- fresh_input
  z <- if return b then comp1 else comp2
  case_sum (\x0 -> return x0) (\_ -> return false) z
