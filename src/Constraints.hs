{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Constraints where

import qualified Data.Map as Map

import Common
import Field
import Poly
import R1CS

----------------------------------------------------------------
--            Intermediate Constraint Language                --
----------------------------------------------------------------

data COp = CAdd | CMult
  deriving (Eq,Ord)

instance Show COp where
  show CAdd  = "+"
  show CMult = "*"

interp_op :: Field a => COp -> a -> a -> a
interp_op op = case op of
  CAdd -> add
  CMult -> \x y -> if x == zero || y == zero then zero else mult x y

inv_op :: Field a => COp -> a -> a
inv_op op = case op of
  CAdd -> neg 
  CMult -> \x -> if x == zero then zero else inv x

data Constraint a =
  CBinop COp (Term a,Term a,Term a) -- x `op` y = z
  deriving (Eq,Ord)

instance Show a => Show (Constraint a) where
  show (CBinop op (x,y,z))
    = show x ++ show op ++ show y ++ "==" ++ show z

type Assgn a = Map.Map Var a

format_err :: Field a => [Constraint a] -> Assgn a -> Var -> COp -> (a,a,a) -> String
format_err cs env x op (c,d,e)
  = show c ++ show op ++ show d ++ " == " ++ show e
    ++ ": inconsistent assignment, in constraint context: " ++ show cs
    ++ ", in solved-variable context: " ++ show x    
    ++ ", in partial assignment context: " ++ show env

assert :: Field a => [Constraint a] -> Assgn a -> Var -> COp -> (a,a,a) -> Assgn a
assert cs env x op (c,d,e) =
  let fop = interp_op op
  in if c `fop` d == e then env else error $ format_err cs env x op (c,d,e)

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

-- | Interpret a single IL constraint as a rank-1 constraint
r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw constr = case constr of
  -- no unknowns
  -- c `op` d = e
  CBinop op (TConst c,TConst d,TConst e) ->
    let cd = interp_op op c d
    in if cd == e then
         R1C (const_poly nw zero,const_poly nw zero,const_poly nw zero)
       else error $ "not satisfiable: " ++ show c ++ show op ++ show d
            ++ " == " ++ show e
  
  -- one unknown
  -- c + d = z
  CBinop CAdd (TConst c,TConst d,TVar pos_z z) ->
    R1C (const_poly nw one,const_poly nw (c `add` d),var_poly nw (pos_z,z))
  -- c + y = e
  CBinop CAdd (TConst c,TVar pos_y y,TConst e) ->
    R1C (const_poly nw one,cy_poly nw c (pos_y,y),const_poly nw e)
  -- x + d = e
  CBinop CAdd (TVar pos_x x,TConst d,TConst e) ->
    R1C (const_poly nw one,cy_poly nw d (pos_x,x),const_poly nw e)

  -- c * d = z
  CBinop CMult (TConst c,TConst d,TVar pos_z z) ->
    R1C (const_poly nw c,const_poly nw d,var_poly nw (pos_z,z))
  -- c * y = e
  CBinop CMult (TConst c,TVar pos_y y,TConst e) ->
    R1C (const_poly nw c,var_poly nw (pos_y,y),const_poly nw e)
  -- x * d = e
  CBinop CMult (TVar pos_x x,TConst d,TConst e) ->
    R1C (var_poly nw (pos_x,x),const_poly nw d,const_poly nw e)

  -- two unknowns
  -- c + y = z
  CBinop CAdd (TConst c,TVar pos_y y,TVar pos_z z) ->
    R1C (const_poly nw one,cy_poly nw c (pos_y,y),var_poly nw (pos_z,z))
  -- x + d = z    
  CBinop CAdd (TVar pos_x x,TConst d,TVar pos_z z) ->
    R1C (const_poly nw one,cy_poly nw d (pos_x,x),var_poly nw (pos_z,z))
  -- x + y = e    
  CBinop CAdd (TVar pos_x x,TVar pos_y y,TConst e) ->
    R1C (const_poly nw one,cxy_poly nw zero (pos_x,x) (pos_y,y),const_poly nw e)

  -- c * y = z
  CBinop CMult (TConst c,TVar pos_y y,TVar pos_z z) ->
    R1C (const_poly nw c,var_poly nw (pos_y,y),var_poly nw (pos_z,z))
  -- x * d = z    
  CBinop CMult (TVar pos_x x,TConst d,TVar pos_z z) ->
    R1C (const_poly nw d,var_poly nw (pos_x,x),var_poly nw (pos_z,z))
  -- x * y = e    
  CBinop CMult (TVar pos_x x,TVar pos_y y,TConst e) ->
    R1C (var_poly nw (pos_x,x),var_poly nw (pos_y,y),const_poly nw e)

  -- three unknowns
  -- x + y = z
  CBinop CAdd (TVar pos_x x,TVar pos_y y,TVar pos_z z)
    | x == y, pos_x == pos_y ->
      R1C (const_poly nw (add one one),var_poly nw (pos_x,x),var_poly nw (pos_z,z)) 
  CBinop CAdd (TVar pos_x x,TVar pos_y y,TVar pos_z z) 
    | x == y, pos_x /= pos_y ->
      R1C (const_poly nw zero,const_poly nw zero,var_poly nw (pos_z,z)) 
  CBinop CAdd (TVar pos_x x,TVar pos_y y,TVar pos_z z) 
    | otherwise ->
      R1C (const_poly nw one,add_poly nw (pos_x,x) (pos_y,y),var_poly nw (pos_z,z))

  -- x * y = z
  CBinop CMult (TVar pos_x x,TVar pos_y y,TVar pos_z z) ->
    R1C (var_poly nw (pos_x,x),var_poly nw (pos_y,y),var_poly nw (pos_z,z))

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs
