{-# LANGUAGE GADTs
           , TypeSynonymInstances
           , FlexibleInstances
           , BangPatterns
  #-}

module Constraints
  ( CoeffList(..)
  , coeff_insert
  , Constraint(..)
  , cadd
  , ConstraintSet
  , ConstraintSystem(..)
  , r1cs_of_cs
  , renumber_constraints
  , constraint_vars
  ) where

import qualified Data.Set as Set
import qualified Data.IntMap.Lazy as Map
import Control.Monad.State

import Common
import Errors
import Field
import Poly
import R1CS
import SimplMonad

----------------------------------------------------------------
--            Intermediate Constraint Language                
----------------------------------------------------------------

newtype CoeffList k v = CoeffList { asList :: [(k,v)] }
  deriving (Eq)
-- COEFFLIST INVARIANT: no key appears more than once.  Upon duplicate
-- insertion, insert field sum of the values.  Terms with 0 coeff. are
-- implicitly removed. Smart constructor 'cadd' (below) enforces this
-- invariant.

coeff_insert :: (Eq k,Field a) => k -> a -> CoeffList k a -> CoeffList k a
coeff_insert k a l = CoeffList $ go (asList l)
  where go [] = [(k,a)]
        go (scrut@(k',a') : l')
          = if k == k' then (k,add a a') : l'
            else scrut : go l'

coeff_merge :: (Eq k,Field a) => CoeffList k a -> CoeffList k a
coeff_merge l = go (CoeffList []) (asList l)
  where go acc [] = acc
        go acc ((k,a) : l')
          = go (coeff_insert k a acc) l'

remove_zeros :: (Field a) => CoeffList k a -> CoeffList k a
remove_zeros (CoeffList l) = CoeffList $ go [] l
  where go acc [] = acc
        go acc ((_,a) : l')
            | a==zero
            = go acc l'
        go acc (scrut@(_,_) : l')
            | otherwise
            = go (scrut : acc) l'

-- | Constraints are either
--   * 'CAdd a m': A linear combination of the constant 'a' with
--     the variable-coeff. terms given by map 'm : Map.Map Var a'.
--   * 'CMult (c,x) (d,y) (e,mz)': A multiplicative constraint with
--     interpretation cx * dy = e (when mz = Nothing), or
--                    cx * dy = ez (when mz = Just z). 
data Constraint a =
    CAdd !a !(CoeffList Var a)
  | CMult !(a,Var) !(a,Var) !(a, Maybe Var)
  | CMagic Var [Var] ([Var] -> State (SEnv a) Bool)

-- | Smart constructor enforcing CoeffList invariant
cadd :: Field a => a -> [(Var,a)] -> Constraint a
cadd !a !l = CAdd a (remove_zeros $ coeff_merge $ CoeffList l)

type ConstraintSet a = Set.Set (Constraint a)

data ConstraintSystem a =
  ConstraintSystem { cs_constraints :: ConstraintSet a
                   , cs_num_vars :: Int
                   , cs_in_vars :: [Var]                     
                   , cs_out_vars :: [Var]                     
                   }
  deriving (Show)

instance Eq a => Eq (Constraint a) where
  CAdd c m == CAdd c' m'
    = c == c' && m == m'
  CMult cx dy emz == CMult cx' dy' emz'
    = emz == emz'
      && (cx == cx' && dy == dy' || cx == dy' && dy == cx')
  CMagic nm _ _ == CMagic nm' _ _ = nm == nm'
  CAdd _ _ == CMult _ _ _ = False
  CMult _ _ _ == CAdd _ _ = False
  CMagic _ _ _ == _  = False
  _ == CMagic _ _ _  = False

compare_add :: Ord a => Constraint a -> Constraint a -> Ordering
{-# INLINE compare_add #-}
compare_add !(CAdd c m) !(CAdd c' m')
  = if c == c' then compare (asList m) (asList m')
    else if c < c' then LT else GT
compare_add !_ !_
  = fail_with $ ErrMsg "internal error: compare_add"

compare_mult :: Ord a => Constraint a -> Constraint a -> Ordering
{-# INLINE compare_mult #-}
compare_mult
  !(CMult (c,x) (d,y) (e,mz))
  !(CMult (c',x') (d',y') (e',mz'))
  = if x == x' then 
      if y == y' then
        case compare mz mz' of
               EQ -> case compare c c' of
                       EQ -> case compare d d' of
                               EQ -> compare e e'
                               other -> other
                       other -> other
               other -> other
      else if y < y' then LT else GT
    else if x < x' then LT else GT
compare_mult !_ !_
  = fail_with $ ErrMsg "internal error: compare_mult"

compare_constr :: Ord a => Constraint a -> Constraint a -> Ordering
{-# INLINE compare_constr #-}
compare_constr !(CAdd _ _) !(CMult _ _ _) = LT
compare_constr !(CMult _ _ _) !(CAdd _ _) = GT
compare_constr !constr@(CAdd _ _) !constr'@(CAdd _ _)
  = compare_add constr constr'
compare_constr !constr@(CMult {}) !constr'@(CMult {})
  = compare_mult constr constr'
compare_constr !(CMagic nm _ _) !(CMagic nm' _ _) = compare nm nm'
compare_constr !_ !(CMagic _ _ _) = LT
compare_constr !(CMagic _ _ _) !_ = GT

instance Ord a => Ord (Constraint a) where
  {-# SPECIALIZE instance Ord (Constraint Rational) #-}
  compare = compare_constr 

instance Show a => Show (Constraint a) where
  show (CAdd a m) = show a ++ " + " ++ go (asList m)
    where go [] = " == 0"
          go [(x,c)] = show c ++ "x" ++ show x ++ go []
          go ((x,c) : c_xs) = show c ++ "x" ++ show x ++ " + " ++ go c_xs

  show (CMult (c,x) (d,y) (e,mz))
    = let show_term c0 x0 = show c0 ++ "x" ++ show x0
      in show_term c x ++ " * " ++ show_term d y
         ++ " == " 
         ++ case mz of
              Nothing -> show e
              Just z  -> show_term e z

  show (CMagic nm xs _) = "Magic " ++ show (nm,xs)

----------------------------------------------------------------
-- Compilation to R1CS
----------------------------------------------------------------

r1cs_of_cs :: Field a 
           => ConstraintSystem a -- ^ Constraints
           -> (Assgn a -> Assgn a) -- ^ Witness generator
           -> R1CS a
r1cs_of_cs cs
  = R1CS (go $ Set.toList $ cs_constraints cs)
         (cs_num_vars cs)
         (cs_in_vars cs)    
         (cs_out_vars cs)    
  where go [] = []
        go (CAdd a m : cs')
          = R1C ( const_poly one
                , Poly $ Map.insert (-1) a $ Map.fromList (asList m)
                , const_poly zero
                ) : go cs'

        go (CMult cx dy (e,Nothing) : cs')
          = R1C (var_poly cx,var_poly dy,const_poly e) : go cs'

        go (CMult cx dy (e,Just z) : cs')
          = R1C (var_poly cx,var_poly dy,var_poly (e,z)) : go cs'

        go (CMagic _ _ _ : cs') 
          = go cs'


-- | Return the list of variables occurring in constraints 'cs'.
constraint_vars :: ConstraintSet a -> [Var]
constraint_vars cs
  = Set.toList
    $ Set.foldl' (\s0 c -> Set.union (get_vars c) s0) Set.empty cs
  where get_vars (CAdd _ m) = Set.fromList $ map fst (asList m)
        get_vars (CMult (_,x) (_,y) (_,Nothing)) = Set.fromList [x,y]
        get_vars (CMult (_,x) (_,y) (_,Just z))  = Set.fromList [x,y,z]
        get_vars (CMagic _ xs _) = Set.fromList xs


-- | Sequentially renumber term variables '0..max_var'.  Return
--   renumbered constraints, together with the total number of
--   variables in the (renumbered) constraint set and the (possibly
--   renumbered) in and out variables.
renumber_constraints :: Field a
                      => ConstraintSystem a
                      -> ( Var -> Var 
                         , ConstraintSystem a 
                         )
renumber_constraints cs
  = (renum_f,ConstraintSystem new_cs (Map.size var_map) new_in_vars new_out_vars)
  where new_cs       = Set.map renum_constr $ cs_constraints cs
        new_in_vars  = map renum_f $ cs_in_vars cs        
        new_out_vars = map renum_f $ cs_out_vars cs

        var_map
          = Map.fromList
            $ zip (cs_in_vars cs ++ filter isnt_input all_vars) [0..]
          where isnt_input = not . flip Set.member in_vars_set
                in_vars_set = Set.fromList $ cs_in_vars cs
                all_vars = constraint_vars $ cs_constraints cs

        renum_f x
          = case Map.lookup x var_map of
              Nothing ->
                fail_with
                $ ErrMsg ("can't find a binding for variable " ++ show x
                          ++ " in map " ++ show var_map)
              Just x' -> x'

        renum_constr c0 
          = case c0 of
              CAdd a m ->
                cadd a $ map (\(k,v) -> (renum_f k,v)) (asList m)
              CMult (c,x) (d,y) (e,mz) ->
                CMult (c,renum_f x) (d,renum_f y) (e,fmap renum_f mz)
              CMagic nm xs f -> 
                CMagic nm (map renum_f xs) f   
            


            

        
