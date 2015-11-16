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
dequeue q def = fix go q
  where go self q0 = do 
          l  <- fst_pair q0
          r  <- snd_pair q0
          l_empty <- is_empty_stack r
          r_empty <- is_empty_stack r

          p1 <- pair l r
          p2 <- pair def p1

          new_l1 <- nil
          new_r1 <- rev_list l
          p3 <- pair new_l1 new_r1
          p4 <- self p3

          a <- top_stack def r
          new_r2 <- pop_stack r
          p5 <- pair l new_r2
          p6 <- pair a p5

          p7 <- if l_empty then p2 else p4

          if r_empty then p7 else p6
{-
          if r_empty then
            if l_empty then do p  <- pair l r
                               pair def p
            else do new_l <- nil
                    new_r <- rev_list l
                    p <- pair new_l new_r
                    self p def
          else do a <- top_stack def r
                  new_r <- pop_stack r
                  p <- pair l new_r
                  pair a p
-}
  
