{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module Queue where

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

import SyntaxMonad
import Syntax
import TExpr
--import Toplevel
import List
import Stack

type TQueue a = 'TProd (TStack a) (TStack a)

type Queue a = TExp (TQueue a) Rational

empty_queue :: Typeable a => Comp (TQueue a)
empty_queue = do
  l <- empty_stack
  r <- empty_stack
  pair l r

enqueue :: (Zippable a, Derive a, Typeable a)
           => TExp a Rational -> Queue a -> Comp (TQueue a)
enqueue v q = do
  l  <- fst_pair q
  r  <- snd_pair q
  l' <- push_stack v l
  pair l' r

dequeue :: (Zippable a, Derive a, Typeable a)
           => Queue a -> TExp a Rational -> Comp ('TProd a (TQueue a))
dequeue q def = do
  l <- fst_pair q
  r <- snd_pair q
  l_empty <- is_empty_stack l
  r_empty <- is_empty_stack r
  if return r_empty then
    if return l_empty then do
      pair def q
      else do
        l' <- nil
        pre_r <- rev_list l
        h <- top_stack def pre_r
        r' <- pop_stack pre_r
        q' <- pair l' r'
        pair h q'
    else do
      h <- top_stack def r
      r' <- pop_stack r
      p <- pair l r'
      pair h p

dequeue_rec :: (Zippable a, Derive a, Typeable a)
           => Queue a -> TExp a Rational -> Comp ('TProd a (TQueue a))
dequeue_rec q def = fix go q
  where go self q0 = do
          l <- fst_pair q0
          r <- snd_pair q0
          l_empty <- is_empty_stack l
          r_empty <- is_empty_stack r
          if return r_empty then
            if return l_empty then do
              pair def q0
            else do
              l' <- nil
              r' <- rev_list l
              p' <- pair l' r' 
              self p'
          else do
            h <- top_stack def r
            r' <- pop_stack r
            p <- pair l r'
            pair h p
