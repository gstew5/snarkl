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
       ; roll v
       }

varN' :: Int
     -> Comp TTerm
varN' i
  = do { v <- inl (exp_of_int i)
       ; roll v
       }

lam :: TExp TTerm Rational
    -> Comp TTerm 
lam t
  = do { t' <- inl t
       ; v <- inr t'
       ; roll v
       }

app :: TExp TTerm Rational
    -> TExp TTerm Rational
    -> Comp TTerm
app t1 t2
  = do { t <- pair t1 t2
       ; t' <- inr t
       ; v <- inr t'
       ; roll v
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
          -> (TExp TTerm Rational -> TExp TTerm Rational -> Comp ty)
          -> Comp ty
case_term t f_var f_lam f_app
  = do { t' <- unroll t
       ; case_sum f_var (case_sum f_lam go) t'
       }
  where go p
          = do { e1 <- fst_pair p
               ; e2 <- fst_pair p
               ; f_app e1 e2
               }

is_lam :: TExp TTerm Rational -> Comp TBool
is_lam t
  = case_term t
     (const $ ret false)
     (const $ ret true)
     (\_ _ -> ret false)

shift :: Int
      -> TExp TField Rational
      -> TExp TTerm Rational
      -> Comp TTerm
shift level n t
  | level > 0
  = case_term t 
      (\m -> varN (n + m))
      (\t' ->
        do { t'' <- shift (dec level) n t'
           ; lam t''
           })
      (\t1 t2 ->
        do { t1' <- shift (dec level) n t1
           ; t2' <- shift (dec level) n t2
           ; app t1' t2'
           })

  | otherwise
  = ret t


-- Explicit Substitutions
-- \sigma ::= Shift n + (Term * \sigma)

type TFSubst = TFSum (TFConst TField) (TFProd (TFConst TTerm) TFId)
    
type TSubst = TMu TFSubst

subst_nil n
  = do { n' <- inl n
       ; roll n' :: Comp TSubst
       }

subst_cons t sigma
  = do { p <- pair t sigma
       ; p' <- inr p
       ; roll p' :: Comp TSubst
       }

case_subst sigma f_shift f_cons
  = do { sigma' <- unroll (sigma :: TExp TSubst Rational)
       ; case_sum f_shift go sigma'
       }
  where go p
          = do { t <- fst_pair p
               ; sigma' <- snd_pair p
               ; f_cons t sigma'
               }

-- subst_term sigma t
--   = case_term t
--       -- Var(n)
--       (\n -> case_subst t
--                (\m -> varN $ n+m)
--                (\t' sigma' -> ...
