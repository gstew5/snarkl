{-# LANGUAGE BangPatterns
  #-}

module Simplify
  ( do_simplify
  ) where

import Data.List (foldl')
import qualified Data.Set as Set
import Control.Monad.State

import Common
import Errors
import Field
import Constraints
import UnionFind
import SimplMonad

----------------------------------------------------------------
--                         Substitution                       --
----------------------------------------------------------------
        
-- | Normalize constraint 'constr', by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.        
subst_constr :: Field a
             => Constraint a
             -> State (SEnv a) (Constraint a)
subst_constr !constr = case constr of
  CMagic !_ !xs !mf -> 
    do { solve <- solve_mode_flag
       ; if solve then  
           do { b <- mf xs
              ; if b then return $ cadd zero []
                else return constr
              }
         else return constr
       }

  CAdd a m -> 
    do { -- Variables resolvable to constants
         consts' <- mapM (\(x,a0) ->
                           do { var_or_a <- bind_of_var x
                              ; case var_or_a of
                                  Left _ -> return []
                                  Right a' -> return $! [(x,a0 `mult` a')]
                              })
                    $! asList m
       ; let consts     = concat consts'
       ; let const_keys = map fst consts
       ; let const_vals = map snd consts
         -- The new constant folding in all constant constraint variables 
       ; let new_const  = foldl' add a const_vals
         -- The linear combination minus
         -- (1) Terms whose variables resolve to constants, and
         -- (2) Terms with coeff 0.    
       ; let less_consts
               = filter (\(k,v) -> not (elem k const_keys) && v/=zero)
                 $! asList m
         -- The new linear combination: 'less_consts' with all variables
         -- replaced by their roots.    
       ; new_map <- mapM (\(x,a0) ->
                           do { rx <- root_of_var x
                              ; return $! (rx,a0)
                              })
                    less_consts
       ; return $! cadd new_const new_map
       }

  CMult !(c,x) !(d,y) !ez ->
    do { bx <- bind_of_var x
       ; by <- bind_of_var y
       ; bz <- bind_of_term ez
       ; case (bx,by,bz) of
           (Left rx,Left ry,Left (e,rz)) ->
             return
             $! CMult (c,rx) (d,ry) (e,Just rz)
           (Left rx,Left ry,Right e) ->
             return
             $! CMult (c,rx) (d,ry) (e,Nothing)
           (Left rx,Right d0,Left (e,rz)) ->
             return
             $! cadd zero [(rx,c `mult` d `mult` d0),(rz,neg e)]
           (Left rx,Right d0,Right e) ->
             return
             $! cadd (neg e) [(rx,c `mult` d `mult` d0)]
           (Right c0,Left ry,Left (e,rz)) ->
             return
             $! cadd zero [(ry,c0 `mult` c `mult` d),(rz,neg e)]
           (Right c0,Left ry,Right e) ->
             return
             $! cadd (neg e) [(ry,c0 `mult` c `mult` d)]
           (Right c0,Right d0,Left (e,rz)) ->
             return
             $! cadd (c `mult` c0 `mult` d `mult` d0) [(rz,neg e)]
           (Right c0,Right d0,Right e) ->
             return
             $! cadd (c `mult` c0 `mult` d `mult` d0 `add` (neg e)) []
       }

    where bind_of_term (e,Nothing)
            = return $! Right e
          bind_of_term (e,Just z)
            = do { var_or_a <- bind_of_var z
                 ; case var_or_a of
                     Left rz -> return $! Left (e,rz)
                     Right e0 -> return $! Right (e `mult` e0)
                 }
          
        

----------------------------------------------------------------
--                 Constraint Set Minimization                --
----------------------------------------------------------------

-- | Is 'constr' a tautology?
is_taut :: Field a
        => Constraint a 
        -> State (SEnv a) Bool
is_taut constr  
  = do { constr' <- subst_constr constr
       ; case constr' of
           CAdd _ (CoeffList []) -> return True
           CAdd _ (CoeffList (_ : _)) -> return False
           CMult _ _ _ -> return False
           CMagic _ xs mf -> mf xs
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

  where go (CAdd a (CoeffList [(x,c)]))
          = if c == zero then return ()
            else case inv c of
                   Nothing -> 
                     fail_with 
                     $ ErrMsg (show c ++ " not invertible")
                   Just c' -> bind_var (x,neg a `mult` c')

        go (CAdd a (CoeffList [(x,c),(y,d)]))
          | a==zero
          = if c == neg d then unite_vars x y else return ()
            
        go (CAdd _ _)
          | otherwise
          = return ()

        go _ | otherwise = return ()


do_simplify :: Field a
            => Bool -- ^ Solve mode? If 'True', use Magic. 
            -> Assgn a -- ^ Initial variable assignment
            -> ConstraintSystem a -- ^ Constraint set to be simplified 
            -> (Assgn a,ConstraintSystem a)
                -- ^ Resulting assignment, simplified constraint set
do_simplify in_solve_mode env cs
    -- NOTE: Pinned vars include:
    -- * input vars
    -- * output vars
    -- * magic vars (those that appear in magic constraints, used to 
    --   resolve nondeterministic inputs)   
    -- Pinned vars are never optimized away.
  = let pinned_vars = cs_in_vars cs ++ cs_out_vars cs ++ magic_vars (cs_constraints cs)
        new_state   = SEnv (new_uf { extras = env }) in_solve_mode
    in fst $ runState (go pinned_vars) new_state
  where go pinned_vars
          = do { sigma' <- simplify pinned_vars $ cs_constraints cs
                 -- NOTE: In the next line, it's OK that 'pinned_vars'
                 -- may overlap with 'constraint_vars cs'. 
                 -- 'assgn_of_vars' might do a bit of duplicate
                 -- work (to look up the same key more than once).
               ; assgn <- assgn_of_vars
                          $ pinned_vars
                            ++ constraint_vars (cs_constraints cs)
               ; return (assgn,cs { cs_constraints = sigma' })
               }
        magic_vars cs0 
          = Set.fold (\c0 acc -> 
                          case c0 of 
                            CMagic _ xs _ -> xs ++ acc
                            _ -> acc
                     ) [] cs0

simplify :: Field a
         => [Var] 
         -> ConstraintSet a
         -> State (SEnv a) (ConstraintSet a)
simplify pinned_vars sigma  
  = do { sigma' <- simplify_rec sigma
       ; sigma_subst <- mapM subst_constr $ Set.toList sigma'
       ; sigma_no_tauts <- remove_tauts sigma_subst
       ; sigma_pinned <- add_pin_eqns sigma_no_tauts
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
                                   cadd zero [(x,one),(rx,neg one)]
                                 Right c ->
                                   cadd (neg c) [(x,one)])
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
         else if Set.difference sigma sigma'
                 `Set.isSubsetOf` Set.empty then return sigma'
              else simplify_rec sigma'
       }
  where simplify_once :: Field a
                      => ConstraintSet a -- ^ Initial constraint set
                      -> State (SEnv a) (ConstraintSet a)
                      -- ^ Resulting simplified constraint set
        simplify_once sigma0
          = do { sigma2 <- go Set.empty sigma0
               ; sigma' <- remove_tauts (Set.toList sigma2)
               ; return $ Set.fromList sigma'
               }

        go ws us
          | Set.size us == 0
          = return ws
        go ws us
          | otherwise
          = let (given,us') = choose us
            in do { given_taut <- is_taut given
                  ; if given_taut then go ws us'
                    else do
                      learn given
                      let ws' = Set.insert given ws
                      go ws' us'
                  }

        -- NOTE: Assumes input set is nonempty
        choose s = Set.deleteFindMin s 




