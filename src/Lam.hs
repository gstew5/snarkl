{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module Lam where

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

import Data.Typeable

import Syntax
import Source

type TF = TFSum (TFConst TField) (TFSum TFId (TFProd TFId TFId))

type TTerm = TMu TF

varN :: TExp TField Rational
     -> Comp TTerm
varN e
  = do { v <- inl e
       ; fold v
       }

varN' :: Int
     -> Comp TTerm
varN' i
  = do { v <- inl (exp_of_int i)
       ; fold v
       }

lam :: TExp TTerm Rational
    -> Comp TTerm 
lam t
  = do { t' <- inl t
       ; v <- inr t'
       ; fold v
       }

app :: TExp (TProd TTerm TTerm) Rational
    -> Comp TTerm
app t
  = do { t' <- inr t
       ; v <- inr t'
       ; fold v
       }

-- \x y -> x
term1 :: Comp TTerm
term1
  = do { x <- varN' 1
       ; t <- lam x
       ; lam t
       }

case_term :: ( Typeable ty
             , Zippable ty
             )
          => TExp TTerm Rational
          -> (TExp TField Rational -> Comp ty)
          -> (TExp TTerm Rational -> Comp ty)
          -> (TExp (TProd TTerm TTerm) Rational -> Comp ty)          
          -> Comp ty
case_term t f_var f_lam f_app
  = do { t' <- unfold t
       ; case_sum f_var (case_sum f_lam f_app) t'
       }

is_lam :: TExp TTerm Rational -> Comp TBool
is_lam t
  = case_term t
     (const $ ret false)
     (const $ ret true)
     (const $ ret false)

shift :: TExp TField Rational
      -> TExp TTerm Rational
      -> Comp TTerm
shift n t
  = case_term t
      (\m -> varN (n + m))
      lam
      app
