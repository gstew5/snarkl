module UnionFind
  ( root
  , unite
  , new_uf
  , extra_of
  , UnionFind(..)
  ) where

import qualified Data.Map.Strict as Map
import Data.Maybe

import Common

data UnionFind a =
  UnionFind { ids :: Map.Map Var Var
            , sizes :: Map.Map Var Int
            , extras :: Map.Map Var a }
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
        else error $ "in UnionFind, extra data doesn't match: "
             ++ show (x,c) ++ " != " ++ show (y,d)

-- | Unify x with y.
-- Left-based: if size x == size y, prefer x as root.
unite :: (Show a,Eq a) => UnionFind a -> Var -> Var -> UnionFind a
unite uf x y
  = let (rx,uf2) = root uf x
        (ry,uf') = root uf2 y
        sz_rx = size_of uf' rx
        sz_ry = size_of uf' ry
    in if sz_rx >= sz_ry then
         uf' { ids = Map.insert y rx (ids uf')
             , sizes = Map.insert x (sz_rx + sz_ry) (sizes uf') }
       else 
         uf' { ids = Map.insert x ry (ids uf')
             , sizes = Map.insert y (sz_rx + sz_ry) (sizes uf') }

