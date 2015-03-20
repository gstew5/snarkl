{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module List where

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

type TF = TFSum (TFConst TUnit) (TFProd (TFConst TField) TFId)

type TList = TMu TF

nil :: Comp TList
nil = do { t <- inl unit
         ; roll t
         }

cons :: TExp TField Rational -> TExp TList Rational -> Comp TList
cons f t
  = do { p <- pair f t
       ; t' <- inr p
       ; roll t'
       }

case_list :: ( Typeable ty
             , Zippable ty
             )
          => TExp TList Rational
          -> Comp ty
          -> (TExp (TProd TField TList) Rational -> Comp ty)
          -> Comp ty
case_list t f_nil f_cons
  = do { t' <- unroll t
       ; case_sum (\_ -> f_nil) f_cons t'
       }

head_list :: TExp TField Rational -> TExp TList Rational -> Comp TField
head_list def l
  = case_list l
      (ret def)
      fst_pair

map_list :: Int
    -> (TExp TField Rational -> Comp TField)
    -> TExp TList Rational
    -> Comp TList
map_list level f l
  | level > 0
  = case_list l
      nil
      (\p -> do { hd <- fst_pair p
                ; tl <- snd_pair p
                ; hd' <- f hd
                ; tl' <- map_list (dec level) f tl
                ; cons hd' tl'
                })

  | otherwise
  = ret l    

list1
  = do { tl <- nil
       ; cons (exp_of_int 23) tl
       }

inc_elem e = ret $ exp_of_int 1 + e

list2 level
  = do { l <- list1
       ; map_list level inc_elem l
       }
