module UnionFind where

{- The code in this file is adapted from the following Gist
     https://gist.github.com/kseo/8693028
   as originally written by Github user kseo -}

import Data.Array.ST
import Control.Monad (liftM2)
import Control.Monad.ST.Safe

import Common

data UnionFind s =
  UnionFind { ids :: STUArray s Var Var
            , sizes :: STUArray s Var Int }

new_uf :: Int -- ^ Number of variables
       -> ST s (UnionFind s)
new_uf nv =
  let new_ids   = newListArray (0,nv-1) [0..nv-1]
      new_sizes = newArray (0,nv-1) 1
  in liftM2 UnionFind new_ids new_sizes

root :: UnionFind s -> Var -> ST s Var
root uf x
  = do { px <- readArray (ids uf) x
       ; if px == x then return x
         else do { gpx <- readArray (ids uf) px
                 ; writeArray (ids uf) x gpx
                 ; root uf px }
       }

unite :: UnionFind s -> Var -> Var -> ST s ()
unite uf x y
  = do { rx <- root uf x
       ; ry <- root uf y
       ; sz_rx <- readArray (sizes uf) rx
       ; sz_ry <- readArray (sizes uf) ry
       ; if sz_rx > sz_ry then 
           do { writeArray (ids uf) y rx
              ; writeArray (sizes uf) x (sz_rx + sz_ry) }
         else
           do { writeArray (ids uf) x ry
              ; writeArray (sizes uf) y (sz_rx + sz_ry) }
       }

find :: UnionFind s -> Var -> Var -> ST s Bool
find uf x y = liftM2 (==) (root uf x) (root uf y)

