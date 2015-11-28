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
import Toplevel
import Compile
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

is_empty q = do
  l <- fst_pair q
  r <- snd_pair q
  case_list l
    (case_list r
      (return true)
      (\ _ _ -> return false))
    (\ _ _ -> return false)

last_queue :: (Zippable a, Derive a, Typeable a)
           => Queue a -> TExp a Rational -> Comp a
last_queue q def = fixN 100 go q
  where go self p = do
          p_pair <- dequeue p def
          p_queue <- snd_pair p_pair
          p_top <- fst_pair p_pair
          b <- is_empty p_queue
          if return b
            then return p_top
            else self p_queue

map_queue f q = do
  lq <- fst_pair q
  rq <- snd_pair q
  lq' <- map_list f lq
  rq' <- map_list f rq
  pair lq' rq'
-----------------------------------------
--Simple Examples------------------------
-----------------------------------------

--queue with {nonempty stack, nonempty stack}
queue1
   = do {
        ; s1 <- stack1
        ; s2 <- stack2
        ; pair s1 s2
        }

--queue with {nonempty stack, empty stack}
queue2
   = do {
        ; s1 <- stack1
        ; s2 <- pop_stack s1
        ; s3 <- pop_stack s2
        ; s4 <- stack2
        ; pair s4 s3
        }

queue_comp1
   = do {
        ; q1 <- queue1
        ; q2 <- enqueue 1.0 q1
        ; q3 <- enqueue 3.4 q2
        ; sx <- fst_pair q3
        ; top_stack 0.0 sx
        }

--dequeue where input is queue with {nonempty, nonempty}
queue_comp2
   = do {
        ; q1 <- queue1
        ; sx <- dequeue q1 0.0
        ; fst_pair sx
        }

--dequeue where input is queue with {nonempty, empty}
queue_comp3
   = do {
        ; q1 <- queue2
        ; sx <- dequeue q1 0.0
        ; fst_pair sx
        }


queueN n = fixN 100 go n
  where go self n0 = do
           x <- fresh_input
           tl <- self (n0 - 1.0)
           if return (eq n0 0.0)
             then empty_queue
             else enqueue x tl

test_queueN = do
  n <- fresh_input
  q1 <- queueN n
  q2 <- map_queue inc_elem q1
  last_queue q2 105.0  
