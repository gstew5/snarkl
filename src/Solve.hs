module Solve where

import qualified Data.Map as Map

import Common
import Field
import Constraints

solve_equation :: Field a
               => [Constraint a]
               -> Assgn a
               -> COp 
               -> (Term a,Term a,Term a) -- ^ Three terms, with zero or one unknowns
               -> Assgn a
solve_equation cs env op (tx,ty,tz) =
  let fop    = interp_op op
      invert = inv_op op
  in case (tx,ty,tz) of
    -- no unknowns 
    (TConst c,TConst d,TConst e) -> assert cs env (-1) op (c,d,e)

    -- one unknown
    -- NOTE: We must be careful here when either c or d is zero,
    -- and op = CMult, in which case the equation is still unsolvable.
    (TVar pos_x x,TConst d,TConst e)
      | if op == CMult then d /= zero else True
     -> case Map.lookup x env of
          Nothing -> 
            let v = invert d `fop` e
            in Map.insert x (if pos_x then v else invert v) env
          Just c -> assert cs env x op (if pos_x then c else invert c,d,e)
    (TVar _ _,TConst _,TConst _)
      | otherwise
      -> env
    (TConst c,TVar pos_y y,TConst e)
      | if op == CMult then c /= zero else True    
     -> case Map.lookup y env of
          Nothing -> 
            let v = invert c `fop` e
            in Map.insert y (if pos_y then v else invert v) env
          Just d -> assert cs env y op (c,if pos_y then d else invert d,e)
    (TConst _,TVar _ _,TConst _)
      | otherwise 
     -> env
    (TConst c,TConst d,TVar pos_z z) ->
      case Map.lookup z env of
        Nothing -> 
          let v = c `fop` d
          in Map.insert z (if pos_z then v else invert v) env
        Just e -> assert cs env z op (c,d,if pos_z then e else invert e)

    -- two or more unknowns
    (_,_,_) -> error "expected equation with no greater than one unknown"


lookup_term :: Field a => Assgn a -> COp -> Term a -> Term a
lookup_term env op t = case t of
  TConst _ -> t
  TVar pos_x x ->
    case Map.lookup x env of
      Nothing -> t
      Just c -> TConst $ if pos_x then c else inv_op op c

-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve_constraints :: Field a
                  => [Constraint a] -- ^ Constraints to be solved
                  -> Assgn a -- ^ Initial assignment
                  -> Assgn a -- ^ Resulting assignment
solve_constraints cs env0 = g env0 cs
  where g env [] = env
        g env (c0@(CBinop op (tx,ty,tz)) : cs')
          = case ( lookup_term env op tx
                 , lookup_term env op ty
                 , lookup_term env op tz
                 ) of
              -- no unknowns
              trip@(TConst _,TConst _,TConst _) ->
                g (solve_equation cs env op trip) cs'
              -- one unknown
              trip@(TVar _ _,TConst _,TConst _) ->
                g (solve_equation cs env op trip) $ cs' ++ [c0]
              trip@(TConst _,TVar _ _,TConst _) ->
                g (solve_equation cs env op trip) $ cs' ++ [c0]
              trip@(TConst _,TConst _,TVar _ _) ->
                g (solve_equation cs env op trip) $ cs' ++ [c0]
              -- can't learn anything...two or more unknowns
              _ -> g env $ cs' ++ [c0]
