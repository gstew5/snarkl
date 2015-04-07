module UnionFind
  ( root
  , unite
  , new_uf
  , extra_of
  , UnionFind(..)
  ) where

import qualified Data.IntMap.Lazy as Map
import Data.Maybe

import Common
import Errors

data UnionFind a =
  UnionFind { ids :: Map.IntMap Var
            , sizes :: Map.IntMap Int
            , extras :: Map.IntMap a }
  deriving Show

new_uf :: UnionFind a
new_uf = UnionFind Map.empty Map.empty Map.empty

id_of :: UnionFind a -> Var -> Var
id_of uf x = fromMaybe x $ Map.lookup x (ids uf)

size_of :: UnionFind a -> Var -> Int
size_of uf x = fromMaybe 1 $ Map.lookup x (sizes uf)

extra_of :: UnionFind a -> Var -> Maybe a
extra_of uf x = Map.lookup x (extras uf)

root :: (Show a,Eq a) => UnionFind a -> Var -> (Var,UnionFind a)
root uf x
  = let px = id_of uf x
    in if px == x then (x,uf)
       else let gpx = id_of uf px
                uf' = merge_extras uf x gpx
            in root (uf' { ids = Map.insert x gpx (ids uf) }) px

merge_extras :: (Show a,Eq a) => UnionFind a -> Var -> Var -> UnionFind a
merge_extras uf x y
  = case (Map.lookup x (extras uf), Map.lookup y (extras uf)) of
      (Nothing,Nothing) -> uf
      (Nothing,Just d) -> uf { extras = Map.insert x d (extras uf) }
      (Just c,Nothing) -> uf { extras = Map.insert y c (extras uf) }
      (Just c,Just d) ->
        if c == d then uf
        else fail_with
             $ ErrMsg ("in UnionFind, extra data doesn't match:\n  "
                       ++ show (x,c) ++ " != " ++ show (y,d))

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
unite :: (Show a,Eq a) => UnionFind a -> Var -> Var -> UnionFind a
unite uf x y
  | x < y
  = go x y
    
  | x > y
  = go y x

  | otherwise
  = uf    

  -- Left-biased: if size x == size y, prefer x as root.
  where go x0 y0
          = let (rx,uf2) = root uf x0
                (ry,uf') = root uf2 y0
                sz_rx = size_of uf' rx
                sz_ry = size_of uf' ry
            in if sz_rx >= sz_ry then
                 uf' { ids = Map.insert y0 rx (ids uf')
                     , sizes = Map.insert x0 (sz_rx + sz_ry) (sizes uf')
                     }
               else 
                 uf' { ids = Map.insert x0 ry (ids uf')
                     , sizes = Map.insert y0 (sz_rx + sz_ry) (sizes uf')
                     }

