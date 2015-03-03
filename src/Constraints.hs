{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Constraints where

import qualified Data.Set as Set
import qualified Data.IntMap.Lazy as Map

import Common
import Field
import Poly
import R1CS

----------------------------------------------------------------
--            Intermediate Constraint Language                --
----------------------------------------------------------------

-- | Constraints are either
--   * 'CAdd a m': A linear combination of the constant 'a' with
--     the variable-coeff. terms given by map 'm : Map.Map Var a'.
--   * 'CMult (c,x) (d,y) (e,mz)': A multiplicative constraint with
--     interpretation cx * dy = e (when mz = Nothing), or
--                    cx * dy = ez (when mz = Just z). 
data Constraint a =
    CAdd a (Assgn a)
  | CMult (a,Var) (a,Var) (a, Maybe Var)

type ConstraintSet a = Set.Set (Constraint a)

instance Eq a => Eq (Constraint a) where
  CAdd c m == CAdd c' m'
    = c == c' && m == m'
  CMult cx dy emz == CMult cx' dy' emz'
    = emz == emz'
      && (cx == cx' && dy == dy' || cx == dy' && dy == cx')
  CAdd _ _ == CMult _ _ _ = False
  CMult _ _ _ == CAdd _ _ = False

instance Ord a => Ord (Constraint a) where
  compare (CAdd _ _) (CMult _ _ _) = LT
  compare (CMult _ _ _) (CAdd _ _) = GT
  compare (CAdd c m) (CAdd c' m')
    = case compare c c' of
        EQ -> compare m m'
        LT -> LT
        GT -> GT
  compare (CMult cx dy emz) (CMult cx' dy' emz')
    = case compare cx cx' of
        EQ -> compare (dy,emz) (dy',emz')
        LT -> LT
        GT -> GT

instance Show a => Show (Constraint a) where
  show (CAdd a m) = show a ++ " + " ++ go (Map.toList m)
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

r1cs_of_cs :: Field a 
           => ConstraintSet a -- ^ Constraints
           -> Int -- ^ Total number of variables
           -> [Var] -- ^ Input variables
           -> [Var] -- ^ Output variables
           -> (Assgn a -> Assgn a) -- ^ Witness generator
           -> R1CS a
r1cs_of_cs cs = R1CS $ go $ Set.toList cs
  where go [] = []
        go (CAdd a m : cs')
          = R1C (const_poly one,Poly $ Map.insert (-1) a m,const_poly zero) : go cs'

        go (CMult cx dy (e,Nothing) : cs')
          = R1C (var_poly cx,var_poly dy,const_poly e) : go cs'

        go (CMult cx dy (e,Just z) : cs')
          = R1C (var_poly cx,var_poly dy,var_poly (e,z)) : go cs'


-- | Return the list of variables occurring in constraints 'cs'.
constraint_vars :: ConstraintSet a -> [Var]
constraint_vars cs
  = Set.toList
    $ Set.foldl' (\s0 c -> Set.union (get_vars c) s0) Set.empty cs
  where get_vars (CAdd _ m) = Set.fromList $ Map.keys m
        get_vars (CMult (_,x) (_,y) (_,Nothing)) = Set.fromList [x,y]
        get_vars (CMult (_,x) (_,y) (_,Just z))  = Set.fromList [x,y,z]


-- | Sequentially renumber term variables '0..max_var'.
--   Return renumbered constraints, together with the total number of
--   variables in the (renumberd) constraint set and the
--   (possibly renumbered) out variable (input vars. are always mapped
--   by the identity function).
renumber_constraints :: Field a
                      => [Var] -- ^ Input variables
                      -> ConstraintSet a
                      -> (Int,Var -> Var,ConstraintSet a)
renumber_constraints in_vars cs
  = (num_constraint_vars,renum_f,cs')
  where cs' = Set.map renum_constr cs
        in_vars_set = Set.fromList in_vars
        not_input = filter (not . flip Set.member in_vars_set)
        env = Map.fromList
              $ zip (in_vars ++ not_input (constraint_vars cs)) [0..]
        num_constraint_vars = Map.size env
        renum_f x
          = case Map.lookup x env of
              Nothing ->
                error $ "can't find a binding for variable " ++ show x
              Just x' -> x'

        renum_constr c0 
          = case c0 of
              CAdd a m -> CAdd a $ Map.mapKeys renum_f m
              CMult (c,x) (d,y) (e,mz) ->
                CMult (c,renum_f x) (d,renum_f y) (e,fmap renum_f mz)
            


            

        
