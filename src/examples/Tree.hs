{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module Tree where

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
import SyntaxMonad
import TExpr

type TF a = 'TFSum ('TFConst 'TUnit) ('TFProd ('TFConst a) ('TFProd 'TFId 'TFId))

type TTree a = 'TMu (TF a)

type Rat    = TExp 'TField Rational
type Tree a = TExp (TTree a) Rational

leaf :: Typeable a => Comp (TTree a)
leaf = do
  t <- inl unit
  roll t

node :: Typeable a => TExp a Rational -> Tree a -> Tree a -> Comp (TTree a)
node v t1 t2 = do
  p  <- pair t1 t2
  p' <- pair v p 
  t  <- inr p'
  roll t

case_tree :: ( Typeable a
             , Typeable a1
             , Zippable a1
             )
          => Tree a
          -> Comp a1
          -> (TExp a Rational -> Tree a -> Tree a -> Comp a1)
          -> Comp a1
case_tree t f_leaf f_node = do
  t' <- unroll t
  case_sum (\_ -> f_leaf) go t'
  where go p' = do
          v  <- fst_pair p'
          p  <- snd_pair p'
          t1 <- fst_pair p
          t2 <- snd_pair p
          f_node v t1 t2

map_tree :: ( Typeable a
            , Typeable a1
            , Zippable a1
            , Derive a1
            )
         => (TExp a Rational -> State Env (TExp a1 Rational))
         -> TExp (TTree a) Rational
            -> Comp (TTree a1)
map_tree f t
  = fix go t
  where go self t0 = do 
          case_tree t0
            leaf
            (\v t1 t2 -> do
                v'  <- f v
                t1' <- self t1
                t2' <- self t2
                node v' t1' t2') 

{------------------------------------------------
 Test cases
 ------------------------------------------------}

tree1 = do
  l1 <- leaf
  l2 <- leaf
  t1 <- node 77.0 l1 l2
  l3 <- leaf
  t2 <- node 2.0 t1 l3
  return t2

tree_test1 = do
  t <- tree1
  case_tree t (return 99.0) (\_ tl _ -> do
    case_tree tl (return 88.0) (\v _ _ -> do
      return v))                                   
