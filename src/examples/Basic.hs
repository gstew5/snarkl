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

compile1 = r1cs_of_comp p1

run1 = snarkify_comp "example" p1 []

  
