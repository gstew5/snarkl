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
constraint_vars cs = my_nub $ concatMap get_var cs
  where my_nub = Set.toList . Set.fromList
        get_var (CBinop _ (tx,ty,tz)) = concatMap get_term_var [tx,ty,tz]
        get_term_var (TConst _) = []
        get_term_var (TVar _ x) = [x]


subst_term :: Field a
           => COp -- ^ In operator context 'op',
           -> Term a -- ^ For input term 't',
           -> State (SEnv a) (Term a) -- ^ Return canonicalized term 't'',
                                      -- under the equalities and partial 
                                      -- assignment currently recorded.
subst_term op t = case t of
  TConst _ -> return t
  TVar pos_x x ->
    do { var_or_a <- bind_of_var x
       ; case var_or_a of
           Left rx -> return (TVar pos_x rx)
           Right c -> if pos_x then return $ TConst c
                      else return $ TConst $ inv_op op c
       }

-- | Canonicalize constraint 'constr', with respect to the current state.
subst_constr :: Field a
             => Constraint a
             -> State (SEnv a) (Constraint a)
subst_constr constr = case constr of
  CBinop op (tx,ty,tz) ->
    do { tx' <- subst_term op tx
       ; ty' <- subst_term op ty
       ; tz' <- subst_term op tz
       ; return $ CBinop op (tx',ty',tz')
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
           CBinop op (TConst c,TConst d,TConst e) ->
             if interp_op op c d /= e then
               error $ "in is_taut, "
               ++ show c ++ show op ++ show d ++ " != " ++ show e
               ++ " in constraint " ++ show constr
             else return True
           _ -> return False }

-- | Remove tautologous constraints.
remove_tauts :: Field a => [Constraint a] -> State (SEnv a) [Constraint a]
remove_tauts sigma
  = do { sigma_taut <-
            mapM (\t -> do { b <- is_taut t
                           ; return (b,t) }) sigma
       ; return $ map snd $ filter (not . fst) sigma_taut }

-- | Learn bindings and variable equalities from constraint 'constr'.
learn :: Field a
      => Constraint a
      -> State (SEnv a) ()
learn constr
  = do { constr' <- subst_constr constr
       ; case constr' of
           CBinop op (tx,ty,tz) -> learn_arith op (tx,ty,tz) }
  where learn_arith :: Field a
                    => COp
                    -> (Term a,Term a,Term a)
                    -> State (SEnv a) ()
        learn_arith op (tx,ty,tz) = case (op,tx,ty,tz) of
          -- variable equalities
          -- 0+y = z ==> y = z  
          (CAdd,TConst zero_val,TVar pos_y y,TVar pos_z z) 
            | pos_y == pos_z, zero_val == zero -> unite_vars y z
          -- x+0 = z ==> x = z
          (CAdd,TVar pos_x x,TConst zero_val,TVar pos_z z)
            | pos_x == pos_z, zero_val == zero -> unite_vars x z
          -- 1*y = z ==> y = z
          (CMult,TConst one_val,TVar pos_y y,TVar pos_z z)
            | pos_y == pos_z, one_val == one -> unite_vars y z
          -- x*1 = z ==> x = z
          (CMult,TVar pos_x x,TConst one_val,TVar pos_z z)
            | pos_x == pos_z, one_val == one -> unite_vars x z

          -- arithmetic simplifications
          -- x - x = z ==> z = 0
          (CAdd,TVar pos_x x,TVar pos_y y,TVar _ z)
            | pos_x == not pos_y, x == y -> bind_var (z,zero)
          -- c - c = z ==> z = 0
          (CAdd,TConst c,TConst d,TVar _ z)
            | c == neg d -> bind_var (z,zero)
          -- x / x = z ==> z = 1 (we never generate constraints n / 0)
          (CMult,TVar pos_x x,TVar pos_y y,TVar _ z)
            | pos_x == not pos_y, x == y -> bind_var (z,one)
          -- c / c = z ==> z = 1 
          (CMult,TConst c,TConst d,TVar pos_z z)
            | c == inv_op CMult d, d /= zero
           -> bind_var (z,if pos_z then one else neg one)
          -- 0 * y = z ==> z = 0 
          (CMult,TConst zero_val,_,TVar _ z)
            | zero_val == zero -> bind_var (z,zero)
          -- x * 0 = z ==> z = 0 
          (CMult,_,TConst zero_val,TVar _ z)
            | zero_val == zero -> bind_var (z,zero)
   
          (_,_,_,_) -> solve_equation op (tx,ty,tz)

        solve_equation :: Field a
                      => COp 
                      -> (Term a,Term a,Term a)
                      -> State (SEnv a) ()
        solve_equation op (tx,ty,tz) =
         let fop    = interp_op op
             invert = inv_op op
         in case (tx,ty,tz) of
           -- no unknowns 
           (TConst c,TConst d,TConst e) -> assert op (c,d,e)

           -- one unknown
           -- NOTE: We must be careful here when either c or d is zero,
           -- and op = CMult, in which case the equation is still unsolvable.
           (TVar pos_x x,TConst d,TConst e)
             | if op == CMult then d /= zero else True
            -> let v = invert d `fop` e
               in bind_var (x,if pos_x then v else invert v)
           (TVar _ _,TConst _,TConst _)
             | otherwise -> return ()
           (TConst c,TVar pos_y y,TConst e)
             | if op == CMult then c /= zero else True    
            -> let v = invert c `fop` e
               in bind_var (y,if pos_y then v else invert v)
           (TConst _,TVar _ _,TConst _)
             | otherwise -> return ()
           (TConst c,TConst d,TVar pos_z z) ->
             let v = c `fop` d
             in bind_var (z,if pos_z then v else invert v)

           -- two or more unknowns
           (_,_,_) -> return ()


do_simplify :: Field a
            => [Var] -- ^ Pinned variables (e.g., outputs).
                     -- These should not be optimized away.
            -> Assgn a -- ^ Initial variable assignment
            -> [Constraint a] -- ^ Constraint set to be simplified 
            -> (Assgn a,[Constraint a])
                -- ^ Resulting assignment, simplified constraint set
do_simplify pinned_vars env cs
  = fst $ runState g (SEnv (new_uf { extras = env }))
  where g = do { sigma' <- simplify pinned_vars $ Set.fromList cs
               ; assgn <- assgn_of_vars (constraint_vars cs)
               ; return (assgn,Set.toList sigma')
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
                    mapM (\x -> do { tx <- subst_term CMult (TVar True x)
                                   ; return (x,tx) }) pinned_vars
               ; let pin_eqns
                       = map (\(x,tx) -> CBinop CMult (TConst one,TVar True x,tx))
                         $ pinned_terms 
               ; return $ pin_eqns ++ sigma0 }

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
        g ws us | Set.size us == 0 = return ws
        g ws us | otherwise
          = let (given,us') = choose us
            in do { given_taut <- is_taut given
                  ; if given_taut then g ws us'
                    else do
                      learn given
                      let ws' = Set.insert given ws
                      g ws' us'
                  }

        choose s -- Assumes input set is nonempty
          = let l = Set.toList s
            in (head l,Set.fromList $ tail l)


format_err :: Field a 
           => [Constraint a]
           -> Assgn a
           -> COp
           -> (a,a,a)
           -> String
format_err cs env op (c,d,e)
  = show c ++ show op ++ show d ++ " == " ++ show e
    ++ ": inconsistent assignment, in constraint context: " ++ show cs
    ++ ", in partial assignment context: " ++ show env

assert :: Field a => COp -> (a,a,a) -> State (SEnv a) ()
assert op (c,d,e) =
  let fop = interp_op op
  in if c `fop` d == e then return ()
     else error $ format_err [] Map.empty op (c,d,e)


-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve_constraints :: Field a
                  => [Constraint a] -- ^ Constraints to be solved
                  -> Assgn a -- ^ Initial assignment
                  -> Assgn a -- ^ Resulting assignment
solve_constraints cs env = 
  let (assgn,cs') = do_simplify [] env cs
      vars = constraint_vars cs
  in if all_assigned vars assgn then assgn
     else error $ "some variables are unassigned, "
          ++ "in assignment context " ++ show assgn ++ ", "
          ++ "in variable context " ++ show vars ++ ", "
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
        env = Map.fromList $ zip (in_vars ++ not_input (constraint_vars cs)) [0..]
        num_vars = Map.size env
        renum_f x
          = case Map.lookup x env of
              Nothing -> error $ "can't find a binding for var. " ++ show x
              Just x' -> x'

        renum_constr c0 
          = case c0 of
              CBinop op (tx,ty,tz) ->
                CBinop op (renum_term tx,renum_term ty,renum_term tz)

        renum_term tm@(TConst _) = tm
        renum_term (TVar pos_x x)
          = case Map.lookup x env of
              Nothing -> error $ "in renumber_constraints, variable " ++ show x
                         ++ " not found in environment " ++ show env
              Just y -> TVar pos_x y                         
