module Simplify where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.ST.Safe

import Field
import Common
import Constraints
import UnionFind

type ConstraintSet a = Set.Set (Constraint a)

data SimplState s a =
  SimplState { passgn :: Assgn a -- ^ Partial map from variables to constants
             , eqs :: UnionFind s } -- ^ Equalities among variables

{-

Maintain:
-eqs: Var -> Var -> Bool
-pi: Var -> Maybe a

Simplify'(eqs,pi,working,unselected):
  if unselected is empty then
    (eqs,pi,working)
  else (given,unselected') <- choose unselected 
       if is_taut(eqs,pi,given) then
         Simplify'(eqs,pi,given,unselected')
       else 
         (eqs',pi') <- Learn(eqs,pi,given)
         Simplify'(eqs',pi',working \cup {given}, unselected')

Simplify(sigma):
  (eqs,pi,sigma') <- Simplify'([],[],{},sigma)
  filter (not . is_taut(eqs,pi)) (map (Subst eqs pi) sigma')

-}

new_simplstate :: Int -> ST s (SimplState s a)
new_simplstate nv
  = do { uf <- new_uf nv
       ; return $ SimplState Map.empty uf }

do_simplify :: Field a
            => [Var] -- ^ Pinned variables (e.g., outputs)
                     -- These should not be optimized away.
            -> Int -- ^ Number of variables
            -> [Constraint a] -- ^ Constraint set to be simplified 
            -> [Constraint a]
do_simplify pinned_vars nv sigma
  = let sigma' = Set.fromList sigma
    in Set.toList $ g (5 :: Int) sigma' sigma'
  where g budget s_prev s
        -- ^ budget: the number of nonmonotonic iterations
          | Set.size s >= Set.size s_prev
          = if budget == 0 then s
            else g (budget-1) s (simplify pinned_vars nv s)  
        g budget _ s
          | otherwise
          = g budget s (simplify pinned_vars nv s)


simplify :: Field a
         => [Var] 
         -> Int 
         -> ConstraintSet a
         -> ConstraintSet a
simplify pinned_vars nv sigma
  = runST $ do { st <- new_simplstate nv
               ; (st',sigma') <- simplify_aux st (Set.empty,sigma)
               ; sigma'' <- mapM (subst_constr st') $ Set.toList sigma'
               ; sigma_taut <-
                   mapM (\t -> do { b <- is_taut st' t
                                  ; return (b,t) }) sigma''
               ; let sigma''' = map snd $ filter (not . fst) sigma_taut
               ; -- NOTE: We handle pinned vars. [x] as follows:
                 --  (1) Look up the term associated with
                 --      the pinned variable, if any (call it [t]).
                 --  (2) If there is no such term (other than x itself),
                 --      do nothing (clauses containing the pinned
                 --      variable must still contain the pinned variable).
                 --  (3) Otherwise, introduce a new equation [x = t].
                 pinned_terms <-
                   mapM (\x -> do { tx <- subst_term st' CMult (TVar True x)
                                  ; return (x,tx) }) pinned_vars
               ; let pin_eqns
                       = map (\(x,tx) ->
                               CBinop CMult (TConst one,TVar True x,tx))
                         $ pinned_terms
               ; return $ Set.fromList $ pin_eqns ++ sigma''' }

simplify_aux :: Field a
             => SimplState s a
             -> (ConstraintSet a,ConstraintSet a)
             -> ST s (SimplState s a,ConstraintSet a)
simplify_aux st (working,unselected) = g working unselected
  where g ws us | Set.size us == 0 = return (st,ws)
        g ws us | otherwise
          = let (given,us') = choose us
            in do { given_taut <- is_taut st given
                  ; if given_taut then
                      simplify_aux st (ws,us')
                    else do
                      st' <- learn st given
                      let ws' = Set.insert given ws
                      simplify_aux st' (ws',us') }

        choose s -- ^ Assumes input set is nonempty
          = let l = Set.toList s
            in (head l,Set.fromList $ tail l)

subst_term :: Field a
            => SimplState s a -- ^ In state st
            -> COp -- ^ In operator context op
            -> Term a -- ^ For term t
            -> ST s (Term a) -- ^ Return canonicalized term t',
                             -- under equalities and partial assignment
                             -- recorded in state st.
subst_term st op t = case t of
  TConst _ -> return t
  TVar pos_x x ->
    do { rx <- root (eqs st) x
       ; case Map.lookup rx (passgn st) of
           Nothing -> return (TVar pos_x rx)
           Just c -> if pos_x then return $ TConst c
                     else return $ TConst $ inv_op op c }

subst_constr :: Field a
             => SimplState s a
             -> Constraint a
             -> ST s (Constraint a)
subst_constr st constr = case constr of
  CBinop op (tx,ty,tz) ->
    do { tx' <- subst_term st op tx
       ; ty' <- subst_term st op ty
       ; tz' <- subst_term st op tz
       ; return $ CBinop op (tx',ty',tz') }

bind_var :: SimplState s a -- ^ In state st
         -> (Var,a) -- ^ Bind variable x to c
         -> ST s (SimplState s a)
bind_var st (x,c)
  = do { rx <- root (eqs st) x
       ; return $ st { passgn = Map.insert rx c (passgn st) }
       }

is_taut :: Field a
        => SimplState s a -- ^ In state st
        -> Constraint a -- ^ Is constr a tautology?
        -> ST s Bool
is_taut st constr  
  = do { constr' <- subst_constr st constr
       ; case constr' of
           CBinop op (TConst c,TConst d,TConst e) ->
             if interp_op op c d /= e then
               error $ show c ++ show op ++ show d
                       ++ " != " ++ show e
             else return True
           _ -> return False }

learn :: Field a
      => SimplState s a
      -> Constraint a
      -> ST s (SimplState s a)
learn st constr =
  do { constr' <- subst_constr st constr
     ; case constr' of
         -- variable equalities
         -- 0+y = z ==> y = z
         CBinop CAdd (TConst zero_val,TVar pos_y y,TVar pos_z z)
           | pos_y == pos_z
           , zero_val == zero  
          -> do { unite (eqs st) y z
                ; return st }

         -- x+0 = z ==> x = z
         CBinop CAdd (TVar pos_x x,TConst zero_val,TVar pos_z z)
           | pos_x == pos_z
           , zero_val == zero
          -> do { unite (eqs st) x z
                ; return st }

         -- 1*y = z ==> y = z
         CBinop CMult (TConst one_val,TVar pos_y y,TVar pos_z z)
           | pos_y == pos_z
           , one_val == one
          -> do { unite (eqs st) y z
                ; return st }

         -- x*1 = z ==> x = z
         CBinop CMult (TVar pos_x x,TConst one_val,TVar pos_z z)
           | pos_x == pos_z
           , one_val == one
          -> do { unite (eqs st) x z
                ; return st }


         -- arithmetic simplifications
         -- x - x = z ==> z = 0
         CBinop CAdd (TVar pos_x x,TVar pos_y y,TVar _ z)
           | pos_x == not pos_y
           , x == y
          -> bind_var st (z,zero)

         -- c - c = z ==> z = 0
         CBinop CAdd (TConst c,TConst d,TVar _ z)
           | c == neg d
          -> bind_var st (z,zero)

         -- x / x = z ==> z = 1 (we never generate constraints n / 0)
         CBinop CMult (TVar pos_x x,TVar pos_y y,TVar _ z)
           | pos_x == not pos_y
           , x == y
          -> bind_var st (z,one)

         -- c / c = z ==> z = 1 
         CBinop CMult (TConst c,TConst d,TVar pos_z z)
           | c == inv_op CMult d
           , d /= zero
          -> bind_var st (z,if pos_z then one else neg one)

         -- 0 * y = z ==> z = 0 
         CBinop CMult (TConst zero_val,_,TVar _ z)
           | zero_val == zero
          -> bind_var st (z,zero)

         -- x * 0 = z ==> z = 0 
         CBinop CMult (_,TConst zero_val,TVar _ z)
           | zero_val == zero
          -> bind_var st (z,zero)

         -- variable--constant equalities
         -- c `op` d = z, d == 0
         CBinop op (TConst c,TConst d,TVar pos_z z) ->
           let z_val = if pos_z then interp_op op c d
                       else inv_op op (interp_op op c d)
           in bind_var st (z,z_val)

         -- c `op` y = e
         CBinop op (TConst c,TVar pos_y y,TConst e) ->
           let y_val = if pos_y then interp_op op e (inv_op op c)
                       else inv_op op (interp_op op e (inv_op op c))
           in bind_var st (y,y_val)

{-         -- x `op` d = e
         CBinop op (TVar pos_x x,TConst d,TConst e) ->
           let x_val = if pos_x then interp_op op e (inv_op op d)
                       else inv_op op (interp_op op e (inv_op op d))
           in bind_var st (x,x_val)
-}
         CBinop _ (_,_,_) -> return st }

