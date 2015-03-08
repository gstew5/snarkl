module HashSet where

import Prelude hiding (filter)

import Data.Hashable
import qualified Data.List as List
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set

data HashSet a
  = HashSet { hashSetMap :: IntMap (Set a)
            , hashSetSize :: Int
            }
  deriving Show

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}
  
-- | Is the set empty?
null :: HashSet a -> Bool
null (HashSet s _) = Map.null s

-- | Number of elements in the set.
size :: HashSet a -> Int
size (HashSet _ sz) = sz

slowSize :: HashSet a -> Int
slowSize (HashSet s _)
  = Map.foldl' (flip ((+) . Set.size)) 0 s

-- | Is the element a member of the set?
member :: (Hashable a, Ord a) => a -> HashSet a -> Bool
member a (HashSet s _) =
  case Map.lookup (hash a) s of
    Nothing -> False
    Just s' -> Set.member a s'

-- | Is the element not a member of the set?
notMember :: (Hashable a, Ord a) => a -> HashSet a -> Bool
notMember k s = not $ member k s

-- | Is this a subset?
isSubsetOf :: Ord a => HashSet a -> HashSet a -> Bool
isSubsetOf (HashSet s1 sz1) (HashSet s2 sz2)
  = if sz1 <= sz2 then Map.isSubmapOfBy (Set.isSubsetOf) s1 s2
    else False

-- | Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf :: Ord a => HashSet a -> HashSet a -> Bool
isProperSubsetOf s1 s2 = isSubsetOf s1 s2 && size s1 < size s2


{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | The empty set.
empty :: HashSet a
empty = HashSet Map.empty 0

-- | A set of one element.
singleton :: Hashable a => a -> HashSet a
singleton a
  = HashSet (Map.singleton (hash a) $ Set.singleton a) 1

-- | Add a value to the set. When the value is already an element of the set,
-- it is replaced by the new one, ie. 'insert' is left-biased.
insert :: (Hashable a, Ord a) => a -> HashSet a -> HashSet a
insert a scrut@(HashSet s sz)
  = let s' = Map.insertWith (\_ -> Set.insert a) (hash a) (Set.singleton a) s
    in HashSet s' (if member a scrut then sz else sz+1)

nonempty :: Set a -> Maybe (Set a)
nonempty m | Set.null m = Nothing
           | otherwise  = Just m

-- | Delete a value in the set. Returns the original set when the value was not
-- present.
delete :: (Hashable a, Ord a) => a -> HashSet a -> HashSet a
delete a scrut@(HashSet s sz)
  = let s' = Map.update (nonempty . Set.delete a) (hash a) s
    in HashSet s' (if member a scrut then sz-1 else sz)

-- | Delete and return an arbitrary value from the set.
deleteFind :: (Hashable a, Ord a) => HashSet a -> (a, HashSet a)
deleteFind (HashSet s sz) = go s
  where go s0 =
          let ((k, sk), rest)  = Map.deleteFindMin s0
          in if Set.null sk then go rest
             else let (given, sk_rest) = Set.deleteFindMin sk
                  in (given, HashSet (Map.insert k sk_rest rest) (sz-1))

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | Convert the set to a list of elements.
toList :: HashSet a -> [a]
toList (HashSet s _) = Map.foldr ((++) . Set.toList) [] s

-- | Create a set from a list of elements.
fromList :: (Hashable a, Ord a) => [a] -> HashSet a
fromList xs = List.foldl' (flip insert) empty xs


{--------------------------------------------------------------------
  Combine
--------------------------------------------------------------------}

-- | The union of two sets.
union :: Ord a => HashSet a -> HashSet a -> HashSet a
union (HashSet s1 _) (HashSet s2 _)
  = let h = HashSet (Map.unionWith Set.union s1 s2) 0
    in h { hashSetSize = slowSize h }

-- | Difference between two sets.
difference :: Ord a => HashSet a -> HashSet a -> HashSet a
difference (HashSet s1 _) (HashSet s2 _)
  = let h = HashSet
            (Map.differenceWith
              (\t1 t2 -> nonempty $ Set.difference t1 t2) s1 s2) 0
    in h { hashSetSize = slowSize h }

delete_empty :: Map.IntMap (Set a) -> Map.IntMap (Set a)
delete_empty = Map.filter (not . Set.null)

-- | The intersection of two sets.
intersection :: Ord a => HashSet a -> HashSet a -> HashSet a
intersection (HashSet s1 _) (HashSet s2 _)
  = let h = HashSet
            (delete_empty
             $ Map.intersectionWith Set.intersection s1 s2) 0
    in h { hashSetSize = slowSize h }


{--------------------------------------------------------------------
  Filter
--------------------------------------------------------------------}
  
-- | Filter all elements that satisfy some predicate.
filter :: Ord a => (a -> Bool) -> HashSet a -> HashSet a
filter p (HashSet s _)
  = let h = HashSet (Map.mapMaybe (nonempty . Set.filter p) s) 0
    in h { hashSetSize = slowSize h }

-- | Partition the set according to some predicate. The first set contains all
-- elements that satisfy the predicate, the second all elements that fail the
-- predicate.
partition :: Ord a => (a -> Bool) -> HashSet a -> (HashSet a, HashSet a)
partition p s = (filter p s, filter (not . p) s)


{--------------------------------------------------------------------
  Map
--------------------------------------------------------------------}
  
-- | @'map' f s@ is the set obtained by applying @f@ to each element of @s@.
--
-- It's worth noting that the size of the result may be smaller if, for some
-- @(x,y)@, @x /= y && f x == f y@
map :: (Hashable b, Ord b) => (a -> b) -> HashSet a -> HashSet b
map f = fromList . foldl' (flip ((:) . f)) []


{--------------------------------------------------------------------
  Fold
--------------------------------------------------------------------}
  
-- | Fold over the elements of a set in an unspecified order.
foldl' :: (b -> a -> b) -> b -> HashSet a -> b
foldl' f z (HashSet s _) = Map.foldl' (Set.foldl' f) z s


