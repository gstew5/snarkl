module Simplify
  ( do_simplify
  , renumber_constraints
  , solve_constraints
  ) where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad.State

import Field
import Common
import Constraints
import UnionFind


----------------------------------------------------------------
--                  Simplifier State Monad                    --
----------------------------------------------------------------

type ConstraintSet a = Set.Set (Constraint a)

data SEnv a =
  SEnv { eqs :: UnionFind a } -- ^ Equalities among variables,
                              -- together with a partial map from variables
                              -- to constants (hidden inside the "UnionFind"
                              -- data structure).
  deriving Show

-- | Unify variables 'x' and 'y'.
unite_vars :: Field a => Var -> Var -> State (SEnv a) ()
unite_vars x y
  = do { modify (\senv -> senv { eqs = unite (eqs senv) x y }) }

-- | Bind variable 'x' to 'c'.
bind_var :: Field a => (Var,a) -> State (SEnv a) ()
bind_var (x,c)
  = do { rx <- root_of_var x
       ; senv <- get
       ; let eqs' = (eqs senv) { extras = Map.insert rx c (extras $ eqs senv) }
       ; put $ senv { eqs = eqs' }
       }

-- | Return 'x''s root (the representative of its equivalence class).
root_of_var :: Field a => Var -> State (SEnv a) Var
root_of_var x 
  = do { senv <- get
       ; let (rx,eqs') = root (eqs senv) x
       ; put (senv { eqs = eqs'})
       ; return rx
       }

-- | Return the binding associated with variable 'x', or 'x''s root
-- if no binding exists.
bind_of_var :: Field a => Var -> State (SEnv a) (Either Var a)
bind_of_var x
  = do { rx <- root_of_var x
       ; senv <- get
       ; case extra_of (eqs senv) rx of
           Nothing -> return $ Left rx
           Just c -> return $ Right c
       }

-- | Construct a partial assignment from 'vars' to field elements.
assgn_of_vars :: Field a => [Var] -> State (SEnv a) (Assgn a)
assgn_of_vars vars
  = do { binds <- mapM bind_of_var vars
       ; return
         $ Map.fromList
         $ concatMap (\(x,ec) -> case ec of
                         Left _ -> []
                         Right c -> [(x,c)])
         $ zip vars binds
       }

----------------------------------------------------------------
--                         Substitution                       --
----------------------------------------------------------------

-- | Return the set of variables occurring in constraints 'cs'.
constraint_vars cs = my_nub $ concatMap get_vars cs
  where my_nub = Set.toList . Set.fromList
        get_vars (CAdd _ m) = Map.keys m
        get_vars (CMult (_,x) (_,y) (_,Nothing)) = [x,y]
        get_vars (CMult (_,x) (_,y) (_,Just z))  = [x,y,z]        

-- | Normalize constraint 'constr', by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.        
subst_constr :: Field a
             => Constraint a
             -> State (SEnv a) (Constraint a)
subst_constr constr = case constr of
  CAdd a m -> 
    do { -- Variables resolvable to constants
         consts' <- mapM (\(x,a0) ->
                           do { var_or_a <- bind_of_var x
                              ; case var_or_a of
                                  Left _ -> return []
                                  Right a' -> return $ [(x,a0 `mult` a')]
                              })
                    $ Map.toList m
       ; let consts     = concat consts'
       ; let const_keys = map fst consts
       ; let const_vals = map snd consts
         -- The new constant folding in all constant constraint variables    
       ; let new_const  = foldl add a const_vals
         -- The linear combination minus
         -- (1) Terms whose variables resolve to constants, and
         -- (2) Terms with coeff 0.    
       ; let less_consts
               = Map.toList
                 $ Map.filterWithKey (\k _ -> not $ elem k const_keys)
                 $ Map.filter (/= zero) m
         -- The new linear combination: 'less_consts' with all variables
         -- replaced by their roots.    
       ; new_map <- mapM (\(x,a0) ->
                           do { rx <- root_of_var x
                              ; return $ (rx,a0)
                              })
                    less_consts
       ; return $ CAdd new_const (Map.fromListWith add new_map)
       }

  CMult (c,x) (d,y) ez ->
    do { bx <- bind_of_var x
       ; by <- bind_of_var y
       ; bz <- bind_of_term ez
       ; case (bx,by,bz) of
           (Left rx,Left ry,Left (e,rz)) ->
             return
             $ CMult (c,rx) (d,ry) (e,Just rz)
           (Left rx,Left ry,Right e) ->
             return
             $ CMult (c,rx) (d,ry) (e,Nothing)
           (Left rx,Right d0,Left (e,rz)) ->
             return
             $ CAdd zero
             $ Map.insertWith add rx (c `mult` d `mult` d0)
             $ Map.insert rz (neg e)
             $ Map.empty
           (Left rx,Right d0,Right e) ->
             return
             $ CAdd (neg e)
             $ Map.insert rx (c `mult` d `mult` d0)
             $ Map.empty
           (Right c0,Left ry,Left (e,rz)) ->
             return
             $ CAdd zero
             $ Map.insertWith add ry (c0 `mult` c `mult` d)
             $ Map.insert rz (neg e)
             $ Map.empty
           (Right c0,Left ry,Right e) ->
             return
             $ CAdd (neg e)
             $ Map.insert ry (c0 `mult` c `mult` d)
             $ Map.empty
           (Right c0,Right d0,Left (e,rz)) ->
             return
             $ CAdd (c `mult` c0 `mult` d `mult` d0)
             $ Map.insert rz (neg e)
             $ Map.empty
           (Right c0,Right d0,Right e) ->
             return
             $ CAdd (c `mult` c0 `mult` d `mult` d0 `add` (neg e))
             $ Map.empty
       }

    where bind_of_term (e,Nothing)
            = return $ Right e
          bind_of_term (e,Just z)
            = do { var_or_a <- bind_of_var z
                 ; case var_or_a of
                     Left rz -> return $ Left (e,rz)
                     Right e0 -> return $ Right (e `mult` e0)
                 }
          
        
            

----------------------------------------------------------------
--                  Constraint Minimization                   --
----------------------------------------------------------------

-- | Is 'constr' a tautology?
is_taut :: Field a
        => Constraint a 
        -> State (SEnv a) Bool
is_taut constr  
  = do { constr' <- subst_constr constr
       ; case constr' of
           CAdd _ m -> return $ Map.size m == 0
           CMult _ _ _ -> return False
       }

-- | Remove tautologous constraints.
remove_tauts :: Field a => [Constraint a] -> State (SEnv a) [Constraint a]
remove_tauts sigma
  = do { sigma_taut <-
            mapM (\t -> do { b <- is_taut t
                           ; return (b,t) }) sigma
       ; return $ map snd $ filter (not . fst) sigma_taut
       }

-- | Learn bindings and variable equalities from constraint 'constr'.
learn :: Field a
      => Constraint a
      -> State (SEnv a) ()
learn constr 
  = do { constr' <- subst_constr constr
       ; go constr'
       }

  where go (CAdd a m)
          | Map.size m == 1
          = let [(x,c)] = Map.toList m
            in if c == zero then return ()
               else bind_var (x,neg a `mult` inv c)

        go (CAdd a m)
          | Map.size m == 2 && a==zero
          = let [(x,c),(y,d)] = Map.toList m
            in if c == neg d then unite_vars x y
               else return ()
            
        go (CAdd _ _)
          | otherwise
          = return ()

        go constr'@(CMult (c,_) (d,_) (e,Nothing))
          | c==zero || d==zero
          = if e==zero then return ()
            else error $ "expected " ++ show e ++ " to equal 0 "
                 ++ " in equation: " ++ show constr'
        go (CMult (c,_) (d,_) (e,Just z))
          | (c==zero || d==zero) && e/= zero
          = bind_var (z,zero)

        go (CMult (c,x) (d,y) (e,Just z))
          | (c,x)==(e,z) && (c,x)/=(d,y) && c/=zero && d/=zero
          = bind_var (z,one `mult` inv d)            

        go (CMult (c,x) (d,y) (e,Just z))
          | (d,y)==(e,z) && (c,x)/=(d,y) && c/=zero && d/=zero
          = bind_var (z,one `mult` inv c)

        go _ | otherwise = return ()


do_simplify :: Field a
            => [Var] -- ^ Pinned variables (e.g., outputs).
                     -- These should not be optimized away.
            -> Assgn a -- ^ Initial variable assignment
            -> [Constraint a] -- ^ Constraint set to be simplified 
            -> (Assgn a,[Constraint a])
                -- ^ Resulting assignment, simplified constraint set
do_simplify pinned_vars env cs
  = fst $ runState g (SEnv (new_uf { extras = env }))
  where g = do { sigma' <- simplify_until_fixpoint pinned_vars $ Set.fromList cs
                 -- NOTE: In the next line, it's OK that 'pinned_vars' may
                 -- overlap with 'constraint_vars cs'. 'assgn_of_vars' may
                 -- just do a bit of duplicate work (to look up the same
                 -- key more than once).          
               ; assgn <- assgn_of_vars (pinned_vars ++ constraint_vars cs)
               ; return (assgn,Set.toList sigma')
               }


simplify_until_fixpoint :: Field a
                        => [Var]
                        -> ConstraintSet a
                        -> State (SEnv a) (ConstraintSet a)
simplify_until_fixpoint pinned_vars sigma
  = do { sigma' <- simplify pinned_vars sigma
       ; if Set.difference sigma sigma' `Set.isSubsetOf` Set.empty then
           return sigma'
         else simplify_until_fixpoint pinned_vars sigma'
       }
            

simplify :: Field a
         => [Var] 
         -> ConstraintSet a
         -> State (SEnv a) (ConstraintSet a)
simplify pinned_vars sigma  
  = do { sigma2 <- simplify_rec sigma
       ; sigma3 <- mapM subst_constr $ Set.toList sigma2
       ; sigma4 <- remove_tauts sigma3
       ; sigma_pinned <- add_pin_eqns sigma4
       ; return $ Set.fromList sigma_pinned
       }

  where -- NOTE: We handle pinned variables 'x' as follows:
        --  (1) Look up the term associated with
        --      the pinned variable, if any (call it 't').
        --  (2) If there is no such term (other than 'x' itself),
        --      do nothing (clauses containing the pinned
        --      variable must still contain the pinned variable).
        --  (3) Otherwise, introduce a new equation 'x = t'.
        add_pin_eqns sigma0
          = do { pinned_terms <-
                    mapM (\x -> do { var_or_a <- bind_of_var x
                                   ; return (x,var_or_a)
                                   }) pinned_vars
               ; let pin_eqns
                       = map (\(x,var_or_a) ->
                               case var_or_a of
                                 Left rx ->
                                   CAdd zero $ Map.fromList [(x,one),(rx,neg one)]
                                 Right c ->
                                   CAdd (neg c) $ Map.fromList [(x,one)])
                         $ filter (\(x,rx) -> Left x /= rx) pinned_terms
               ; return $ pin_eqns ++ sigma0
               }

simplify_rec :: Field a
             => ConstraintSet a -- ^ Initial constraint set
             -> State (SEnv a) (ConstraintSet a)
                -- ^ Resulting simplified constraint set
simplify_rec sigma
  = do { sigma' <- simplify_once sigma
       ; if Set.size sigma' < Set.size sigma then
           simplify_rec sigma'
         else return sigma'
       }
  where simplify_once :: Field a
                     => ConstraintSet a -- ^ Initial constraint set
                     -> State (SEnv a) (ConstraintSet a)
                     -- ^ Resulting simplified constraint set
        simplify_once sigma0
          = do { sigma2 <- g Set.empty sigma0
               ; sigma' <- remove_tauts (Set.toList sigma2)
               ; return $ Set.fromList sigma'
               }
        g ws us
          | Set.size us == 0 = return ws
        g ws us
          | otherwise
          = let (given,us') = choose us
            in do { given_taut <- is_taut given
                  ; if given_taut then g ws us'
                    else do
                      learn given
                      let ws' = Set.insert given ws
                      g ws' us'
                  }

        -- NOTE: Assumes input set is nonempty
        choose s = Set.deleteFindMin s 


-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve_constraints :: Field a
                  => [Var] -- ^ Pinned variables
                  -> [Constraint a] -- ^ Constraints to be solved
                  -> Assgn a -- ^ Initial assignment
                  -> Assgn a -- ^ Resulting assignment
solve_constraints pinned_vars cs env = 
  let (assgn,cs') = do_simplify pinned_vars env cs
  in if all_assigned pinned_vars assgn then assgn
     else error $ "some variables are unassigned, "
          ++ "in assignment context " ++ show assgn ++ ", "
          ++ "in pinned-variable context " ++ show pinned_vars ++ ", "
          ++ "in optimized-constraint context " ++ show cs' ++ ", "
          ++ "in constraint context " ++ show cs          

  where all_assigned vars0 assgn = all id $ map (is_mapped assgn) vars0
        is_mapped assgn x
          = case Map.lookup x assgn of
              Nothing -> False
              Just _ -> True


-- | Sequentially renumber term variables '0..max_var'.
--   Return renumbered constraints, together with the total number of
--   variables in the (renumberd) constraint set and the
--   (possibly renumbered) out variable (input vars. are always mapped
--   by the identity function).
renumber_constraints :: Field a
                      => [Var] -- ^ Input variables
                      -> [Constraint a]
                      -> (Int,Var -> Var,[Constraint a])
renumber_constraints in_vars cs = (num_vars,renum_f,cs')
  where cs' = map renum_constr cs
        not_input = filter (not . flip elem in_vars)
        env = Map.fromList
              $ zip (in_vars ++ not_input (constraint_vars cs)) [0..]
        num_vars = Map.size env
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

