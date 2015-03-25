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
import TExpr

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
          -> (TExp TField Rational -> TExp TList Rational -> Comp ty)
          -> Comp ty
case_list t f_nil f_cons
  = do { t' <- unroll t
       ; case_sum (\_ -> f_nil) go t'
       }
  where go p
          = do { e1 <- fst_pair p
               ; e2 <- snd_pair p
               ; f_cons e1 e2
               }

head_list :: TExp TField Rational -> TExp TList Rational -> Comp TField
head_list def l
  = case_list l
      (ret def)
      (\hd _ -> ret hd)

tail_list :: TExp TList Rational -> Comp TList
tail_list l
  = case_list l
      nil
      (\_ tl -> ret tl)

map_list :: (TExp TField Rational -> Comp TField)
         -> TExp TList Rational
         -> Comp TList
map_list f l
  = fix go l
  where go self l0
          = case_list l0
            nil
            (\hd tl ->
              do { hd' <- f hd
                 ; tl' <- self tl
                 ; cons hd' tl'
                 })

last_list :: TExp TField Rational
          -> TExp TList Rational
          -> Comp TField
last_list def l
  = fix go l
  where go self l0
          = case_list l0
            (ret def)
            (\hd tl ->
              case_list tl
              (ret hd)
              (\_ _ -> self tl))

list1
  = do { tl <- nil
       ; tl' <- cons (exp_of_int 23) tl
       ; cons (exp_of_int 33) tl'
       }

inc_elem e = ret $ exp_of_int 1 + e

list2 
  = do { l <- list1
       ; map_list inc_elem l
       }

list_comp3
  = do { b <- input
       ; l <- nil
       ; l' <- cons 23.0 l
       ; l'' <- cons 33.0 l'
       ; l2 <- if b then l'' else l
       ; l3 <- map_list inc_elem l2
       ; l4 <- tail_list l3
       ; head_list 0.0 l4
       }

list_comp4
  = do { l <- list2
       ; last_list 0.0 l
       }
