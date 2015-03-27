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
import TExpr

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

shift :: TExp TField Rational
      -> TExp TTerm Rational
      -> Comp TTerm
shift n t = fix go t
  where go self t0 
          = case_term t0 
            (\m -> varN (n + m))
            (\t' ->
              do { t'' <- self t'
                 ; lam t''
                 })
            (\t1 t2 ->
              do { t1' <- self t1
                 ; t2' <- self t2
                 ; app t1' t2'
                 })


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

subst_term sigma t 
  = do { p <- pair sigma t :: Comp (TProd TSubst TTerm)
       ; fix go p
       }
  where go self p0
          = do { sigma0 <- fst_pair p0
               ; t0 <- snd_pair p0
               ; case_term t0
                 -- Var(n)
                 (\n -> case_subst sigma0
                        (\m -> varN $ n+m)
                        (\t' sigma' -> 
                           do { self' <- 
                                  do { n' <- varN (n - 1.0)
                                     ; p' <- pair sigma' n'
                                     ; self p'
                                     }
                              ; if zeq n then t' else self'
                              }))
                 -- TODO: Lam t1
                 (\t1 -> ret t1)
                 -- TODO: App t1 t2
                 (\t1 _ -> ret t1)
               }
