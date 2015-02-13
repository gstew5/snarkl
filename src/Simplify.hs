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

new_simplstate :: Int -> Assgn a -> ST s (SimplState s a)
new_simplstate nv env
  = do { uf <- new_uf nv
       ; return $ SimplState env uf }

build_assgn :: SimplState s a -> Int -> ST s (Assgn a)
build_assgn st nv = 
  do { bindings <- mapM g [0..nv-1]
     ; return $ Map.fromList $ concat bindings }
  where g x = do { rx <- root (eqs st) x
                 ; case Map.lookup rx (passgn st) of
                      Nothing -> return []
                      Just c -> return [(x,c)] }

do_simplify :: Field a
            => [Var] -- ^ Pinned variables (e.g., outputs)
                     -- These should not be optimized away.
            -> Int -- ^ Number of variables
            -> Assgn a -- ^ Initial variable assignment
            -> [Constraint a] -- ^ Constraint set to be simplified 
            -> (Assgn a,[Constraint a])
                -- ^ Resulting assignment, simplified constraint set
do_simplify pinned_vars nv env sigma
  = let sigma' = Set.fromList sigma
        (assgn,sigma'') = g Set.empty (Map.empty,sigma')
    in (assgn,Set.toList sigma'')
  where g s_prev (assgn,s)
          | Set.size s == Set.size s_prev
          = if Set.difference s s_prev `Set.isSubsetOf` Set.empty then (assgn,s)
            else g s (simplify pinned_vars nv env s)  
        g _ (_,s)
          | otherwise
          = g s (simplify pinned_vars nv env s)

simplify :: Field a
         => [Var] 
         -> Int
         -> Assgn a
         -> ConstraintSet a
         -> (Assgn a,ConstraintSet a)
simplify pinned_vars nv env sigma = runST $
  do { st <- new_simplstate nv env
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
     ; asgn <- build_assgn st' nv
     ; return (asgn,Set.fromList $ pin_eqns ++ sigma''') }

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
learn st constr
  = do { constr' <- subst_constr st constr
       ; case constr' of
           CBinop op (tx,ty,tz) -> learn_arith st op (tx,ty,tz) }

learn_arith :: Field a
            => SimplState s a
            -> COp
            -> (Term a,Term a,Term a)
            -> ST s (SimplState s a)
learn_arith st op (tx,ty,tz) = case (op,tx,ty,tz) of
   -- variable equalities
   -- 0+y = z ==> y = z  
  (CAdd,TConst zero_val,TVar pos_y y,TVar pos_z z) 
    | pos_y == pos_z
    , zero_val == zero 
   -> do { unite (eqs st) y z; return st }
   -- x+0 = z ==> x = z
  (CAdd,TVar pos_x x,TConst zero_val,TVar pos_z z)
    | pos_x == pos_z
    , zero_val == zero
   -> do { unite (eqs st) x z; return st }
   -- 1*y = z ==> y = z
  (CMult,TConst one_val,TVar pos_y y,TVar pos_z z)
    | pos_y == pos_z
    , one_val == one
   -> do { unite (eqs st) y z; return st }
   -- x*1 = z ==> x = z
  (CMult,TVar pos_x x,TConst one_val,TVar pos_z z)
    | pos_x == pos_z
    , one_val == one
   -> do { unite (eqs st) x z; return st }

   -- arithmetic simplifications
   -- x - x = z ==> z = 0
  (CAdd,TVar pos_x x,TVar pos_y y,TVar _ z)
   | pos_x == not pos_y
   , x == y
   -> bind_var st (z,zero)
   -- c - c = z ==> z = 0
  (CAdd,TConst c,TConst d,TVar _ z)
   | c == neg d
   -> bind_var st (z,zero)
   -- x / x = z ==> z = 1 (we never generate constraints n / 0)
  (CMult,TVar pos_x x,TVar pos_y y,TVar _ z)
   | pos_x == not pos_y
   , x == y
   -> bind_var st (z,one)
   -- c / c = z ==> z = 1 
  (CMult,TConst c,TConst d,TVar pos_z z)
   | c == inv_op CMult d
   , d /= zero
   -> bind_var st (z,if pos_z then one else neg one)
   -- 0 * y = z ==> z = 0 
  (CMult,TConst zero_val,_,TVar _ z)
   | zero_val == zero
   -> bind_var st (z,zero)
   -- x * 0 = z ==> z = 0 
  (CMult,_,TConst zero_val,TVar _ z)
   | zero_val == zero
   -> bind_var st (z,zero)
  
  (_,_,_,_) -> return st

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

assert :: Field a => SimplState s a -> COp -> (a,a,a) -> ST s (SimplState s a)
assert st op (c,d,e) =
  let fop = interp_op op
  in if c `fop` d == e then return st
     else error $ format_err [] Map.empty op (c,d,e)

solve_equation :: Field a
               => SimplState s a
               -> COp 
               -> (Term a,Term a,Term a)
               -> ST s (SimplState s a)
solve_equation st op (tx,ty,tz) =
  let fop    = interp_op op
      invert = inv_op op
  in case (tx,ty,tz) of
    -- no unknowns 
    (TConst c,TConst d,TConst e)
      -> assert st op (c,d,e)

    -- one unknown
    -- NOTE: We must be careful here when either c or d is zero,
    -- and op = CMult, in which case the equation is still unsolvable.
    (TVar pos_x x,TConst d,TConst e)
      | if op == CMult then d /= zero else True
     -> let v = invert d `fop` e
        in bind_var st (x,if pos_x then v else invert v)
    (TVar _ _,TConst _,TConst _)
      | otherwise
      -> return st
    (TConst c,TVar pos_y y,TConst e)
      | if op == CMult then c /= zero else True    
     -> let v = invert c `fop` e
        in bind_var st (y,if pos_y then v else invert v)
    (TConst _,TVar _ _,TConst _)
      | otherwise 
     -> return st
    (TConst c,TConst d,TVar pos_z z) ->
      let v = c `fop` d
      in bind_var st (z,if pos_z then v else invert v)

    -- two or more unknowns
    (_,_,_) -> return st

-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve_constraints :: Field a
                  => Int -- ^ Number of variables
                  -> [Constraint a] -- ^ Constraints to be solved
                  -> Assgn a -- ^ Initial assignment
                  -> Assgn a -- ^ Resulting assignment
solve_constraints nv cs env
  = 


