{-# LANGUAGE RebindableSyntax #-}

module Keccak where

import Prelude hiding 
  ( (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , (&&)        
  , not
  , return
  , fromRational
  , negate
  )
import qualified Prelude as P

import Syntax
import Lang

index_of i j = (P.+) (((P.*) 5 i) `mod` 5) (j `mod` 5)

num_lanes :: Int
num_lanes = (P.*) 5 5

-- | At w=1, rotation has no effect
rot :: (Exp Rational,Int) -> Exp Rational
rot (e,_) = e

-- TODO: rotation table
rot_tbl _ _ = 1

round1 :: Exp Rational -> Comp
round1 rc
  = do { a <- arr num_lanes
       ; b <- arr num_lanes
       ; c <- arr 5
       ; d <- arr 5
       ; forall [0..24] (\i -> set (a,i) 1.0)
       ; forall [0..24] (\i -> set (b,i) 0.0)
       ; forall [0..4]  (\i -> set (c,i) 0.0)
       ; forall [0..4]  (\i -> set (c,i) 0.0)          
       ; forall [0..4] (\x ->
           do q <- get (a,index_of x 0)
              u <- get (a,index_of x 1)
              v <- get (a,index_of x 2)
              w <- get (a,index_of x 3)
              z <- get (a,index_of x 4)
              let e = q `xor` u `xor` v `xor` w `xor` z
              set (c,x) e)
       ; forall [0..4] (\x ->
           do q <- get (a,dec x `mod` 5)
              u <- get (a,inc x `mod` 5)
              let e = q `xor` rot (u,1)
              set (d,x) e)
       ; forall_pairs ([0..4],[0..4]) (\x y ->
           do q <- get (a,index_of x y)
              u <- get (d,x)
              set (a,index_of x y) (q `xor` u))
       ; forall_pairs ([0..4],[0..4]) (\x y ->
           do q <- get (a,index_of x y)
              let e = rot (q,rot_tbl x y)
              set (b,index_of y ((P.+) ((P.*) 2 x) ((P.*) 3 y))) e)
       ; forall_pairs ([0..4],[0..4]) (\x y ->
           do q <- get (b,index_of x y)
              u <- get (b,index_of (inc x) y)
              v <- get (b,index_of ((inc . inc) x) y)
              let e = q `xor` (not u && v)
              set (a,index_of x y) e)
       ; do q <- get (a,index_of 0 0)
            set (a,index_of 0 0) (q `xor` rc)
       }
           
