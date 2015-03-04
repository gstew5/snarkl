module Dataflow
       ( remove_unreachable
       ) where

import Data.List (foldl')
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as Map
import Control.Monad.State

import Common
import Constraints

number_constraints :: ConstraintSystem a -> IntMap (Constraint a)
number_constraints cs
  = go 0 Map.empty (Set.toList $ cs_constraints cs)
  where go :: Int -> IntMap (Constraint a) -> [Constraint a] -> IntMap (Constraint a)
        go _ m [] = m
        go n m (c : cs')
          = go (n+1) (Map.insert n c m) cs'

-- |Map variables to the indices of the constraints in which the vars appear.
gather_vars :: Ord a => IntMap (Constraint a) -> IntMap (Set Int)
gather_vars constr_map
  = go Map.empty (Map.toList constr_map)
  where go m [] = m
        go m ((the_id,constr) : cs')
          = let vars = constraint_vars (Set.singleton constr)
            in go (foldl' (\m0 x -> add_var x the_id m0) m vars) cs'

        add_var x the_id m0
          = case Map.lookup x m0 of
              Nothing -> Map.insert x (Set.singleton the_id) m0
              Just s0 -> Map.insert x (Set.insert the_id s0) m0

data DEnv a =
  DEnv { df_roots :: Set Var }

add_root :: Var -> State (DEnv a) ()
add_root x = modify (\s -> s { df_roots = Set.insert x (df_roots s) })

remove_unreachable :: (Show a,Ord a)
                   => ConstraintSystem a
                   -> ConstraintSystem a
remove_unreachable cs
  = let m_constr = number_constraints cs
        m_var    = gather_vars m_constr
        (var_set,_)
          = flip runState (DEnv Set.empty)
            $ do { mapM add_root (cs_out_vars cs)
                 ; explore_vars m_constr m_var (cs_out_vars cs)
                 ; env <- get
                 ; return $ df_roots env
                 }
        new_constrs = lookup_constraints m_constr m_var var_set
    in cs { cs_constraints = new_constrs }

  where lookup_constraints m_constr0 m_var0 var_set0
          = Set.foldl (\s0 x ->
                        case Map.lookup x m_var0 of
                          Nothing -> s0
                          Just s_ids ->
                            constrs_of_idset m_constr0 s_ids `Set.union` s0)
            Set.empty
            var_set0

        constrs_of_idset m_constr0 s_ids
          = Set.foldl (\s0 the_id ->
                        case Map.lookup the_id m_constr0 of
                          Nothing -> s0
                          Just constr -> Set.insert constr s0)
            Set.empty
            s_ids  
                            

explore_vars :: IntMap (Constraint a) -- ^ ConstraintId->Constraint
             -> IntMap (Set Int) -- ^ Var->Set ConstraintId
             -> [Var] -- ^ Roots to explore
             -> State (DEnv a) () 
explore_vars m_constr m_var roots = go roots
  where go [] = return ()
        go (r : roots')
          = case Map.lookup r m_var of
              Nothing -> go roots'
              Just s_ids ->
                do { let vars = get_vars (Set.toList s_ids)
                   ; new_roots <- filterM is_new_root vars
                   ; mapM add_root new_roots
                   ; go (new_roots ++ roots')
                   }

        is_new_root :: Var -> State (DEnv a) Bool
        is_new_root x
          = do { env <- get
               ; return $ not (Set.member x $ df_roots env)
               }

        get_vars [] = []
        get_vars (the_id : ids')
          = case Map.lookup the_id m_constr of
              Nothing -> get_vars ids'
              Just constr ->
                constraint_vars (Set.singleton constr)
                ++ get_vars ids'
