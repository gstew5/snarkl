{-# LANGUAGE RebindableSyntax #-}

module Keccak where

import Data.Bits hiding (xor)

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

round1 :: Exp Rational -> Exp Rational -> Comp
round1 a rc
  = do { -- | Allocate local array variables [b], [c], [d].
         b <- arr num_lanes; c <- arr 5; d <- arr 5
         -- | Initialize arrays.
       ; forall [0..24] (\i -> set (a,i) 1.0)
       ; forall [0..24] (\i -> set (b,i) 0.0)
       ; forall [0..4]  (\i -> set (c,i) 0.0)
       ; forall [0..4]  (\i -> set (d,i) 0.0)
         -- | \theta step         
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
         -- | \rho and \pi steps         
       ; forall_pairs ([0..4],[0..4]) (\x y ->
           do q <- get (a,index_of x y)
              let e = rot (q,rot_tbl x y)
              set (b,index_of y ((P.+) ((P.*) 2 x) ((P.*) 3 y))) e)
         -- | \chi step         
       ; forall_pairs ([0..4],[0..4]) (\x y ->
           do q <- get (b,index_of x y)
              u <- get (b,index_of (inc x) y)
              v <- get (b,index_of ((inc . inc) x) y)
              let e = q `xor` (not u && v)
              set (a,index_of x y) e)
         -- | \iota step
       ; do q <- get (a,index_of 0 0)
            set (a,index_of 0 0) (q `xor` rc)
       }
           
-- round constants
round_consts :: [Int]
round_consts
  = [ 0x00000001
    , 0x00008082
    , 0x0000808a
    , 0x80008000
    , 0x0000808b
    , 0x80000001
    , 0x80008081
    , 0x00008009
    , 0x0000008a
    , 0x00000088
    , 0x80008009
    , 0x8000000a      
    ]

trunc :: Int -> Int -> Int
trunc _ rc
  = rc .&. 0x1 -- FIXME; this doesn't generalize to larger lane sizes

keccak_f1 num_rounds a 
  = forall [0..dec num_rounds] (\i ->
      round1 a (exp_of_int (trunc 1 $ round_consts !! i)))

keccak1 num_rounds
  = do { a <- input_arr num_lanes
       ; keccak_f1 num_rounds a
       ; v <- get (a,23)
       ; ret v }
