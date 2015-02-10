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

unit_of_op :: Field a => COp -> a
unit_of_op op = case op of
  CAdd -> zero
  CMult -> one

interp_op :: Field a => COp -> a -> a -> a
interp_op op = case op of
  CAdd -> add
  CMult -> mult

inv_interp_op :: Field a => COp -> a -> a -> a
inv_interp_op op = case op of
  CAdd -> \a1 a2 -> a1 `add` (neg a2)
  CMult -> \a1 a2 -> if a2 == zero then zero else a1 `mult` (inv a2)

inv_op :: Field a => COp -> a -> a
inv_op op = case op of
  CAdd -> neg
  CMult -> inv

data Constraint a =
  CBinop COp (Term a,Term a,Term a) -- x `op` y = z
  deriving (Eq,Ord)

instance Show a => Show (Constraint a) where
  show (CBinop op (x,y,z))
    = show x ++ show op ++ show y ++ "==" ++ show z

type Assgn a = Map.Map Var a

format_err :: Field a => [Constraint a] -> Assgn a
           -> COp -> a -> a -> a -> String
format_err cs env op c d e
  = show c ++ show op ++ show d ++ " == " ++ show e
    ++ ": inconsistent assignment, in constraint context: "
    ++ show cs ++ ", in partial assignment context: " ++ show env

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
        g env (CBinop op (TConst c,TConst d,TConst e) : cs')
          = let fop = interp_op op
            in if c `fop` d == e then g env cs'
               else error $ format_err cs env op c d e
        g env (c0@(CBinop op (TConst c,TConst d,TVar pos_z z)) : cs')
          = let fop = interp_op op
            in case Map.lookup z env of
              Nothing ->
                let z_val = if pos_z then c `fop` d else inv_op op (c `fop` d)
                in g (Map.insert z z_val env) (cs' ++ [c0])
              Just e  ->
                let z_val = if pos_z then e else inv_op op e
                in if c `fop` d == z_val then g env cs'
                   else error $ format_err cs env op c d z_val
        g env (c0@(CBinop op (TConst c,TVar pos_y y,TConst e)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case Map.lookup y env of
              Nothing ->
                let y_val = if pos_y then e `fop'` c else inv_op op (e `fop'` c)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              Just d ->
                let y_val = if pos_y then d else inv_op op d
                in if c `fop` y_val == e then g env cs'
                   else error $ format_err cs env op c y_val e
        g env (c0@(CBinop op (TConst c,TVar pos_y y,TVar pos_z z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup y env,Map.lookup z env) of
              -- (y   ,   z)
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just e) ->
                let z_val = if pos_z then e else inv_op op e
                    y_val = if pos_y then z_val `fop'` c
                            else inv_op op (z_val `fop'` c)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              (Just d,Nothing) ->
                let y_val = if pos_y then d else inv_op op d
                    z_val = if pos_z then (c `fop` y_val)
                            else inv_op op (c `fop` y_val)
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just d,Just e) ->
                let y_val = if pos_y then d else inv_op op d
                    z_val = if pos_z then e else inv_op op e
                in if c `fop` y_val == z_val then g env cs'
                   else error $ format_err cs env op c y_val z_val
        g env (c0@(CBinop op (TVar pos_x x,TConst d,TConst e)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case Map.lookup x env of
              -- x
              Nothing -> 
                let x_val = if pos_x then e `fop'` d else inv_op op (e `fop'` d)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              Just c ->
                let x_val = if pos_x then c else inv_op op c
                in if x_val `fop` d == e then g env cs'
                   else error $ format_err cs env op x_val d e
        g env (c0@(CBinop op (TVar pos_x x,TConst d,TVar pos_z z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup x env,Map.lookup z env) of
              -- (x   ,   z)              
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just e) ->
                let z_val = if pos_z then e else inv_op op e
                    x_val = if pos_x then z_val `fop'` d
                            else inv_op op (z_val `fop'` d)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              (Just c,Nothing) ->
                let x_val = if pos_x then c else inv_op op c
                    z_val = if pos_z then x_val `fop` d
                            else inv_op op (x_val `fop` d)
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just c,Just e) ->
                let x_val = if pos_x then c else inv_op op c
                    z_val = if pos_z then e else inv_op op e
                in if x_val `fop` d == z_val then g env cs'
                   else error $ format_err cs env op x_val d z_val
        g env (c0@(CBinop op (TVar pos_x x,TVar pos_y y,TConst e)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup x env,Map.lookup y env) of
              -- (x   ,   y)              
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just d) ->
                let y_val = if pos_y then d else inv_op op d
                    x_val = if pos_x then e `fop'` y_val
                            else inv_op op (e `fop'` y_val)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              (Just c,Nothing) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then e `fop'` x_val
                            else inv_op op (e `fop'` x_val)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              (Just c,Just d) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then d else inv_op op d
                in if x_val `fop` y_val == e then g env cs'
                else error $ format_err cs env op x_val y_val e
        g env (c0@(CBinop op (TVar pos_x x,TVar pos_y y,TVar pos_z z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup x env,Map.lookup y env,Map.lookup z env) of
              -- (x   ,   y   ,   z)              
              (Nothing,Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Nothing,Just _) -> g env (cs' ++ [c0])
              (Nothing,Just _,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just d,Just e) -> 
                let z_val = if pos_z then e else inv_op op e
                    y_val = if pos_y then d else inv_op op d
                    x_val = if pos_x then z_val `fop'` y_val
                            else inv_op op (z_val `fop'` y_val)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              (Just _,Nothing,Nothing) -> g env (cs' ++ [c0])
              (Just c,Nothing,Just e) ->
                let z_val = if pos_z then e else inv_op op e
                    x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then z_val `fop'` x_val
                            else inv_op op (z_val `fop'` x_val)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              (Just c,Just d,Nothing) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then d else inv_op op d
                    z_val = if pos_z then x_val `fop` y_val
                            else inv_op op (x_val `fop` y_val)
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just c,Just d,Just e) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then d else inv_op op d
                    z_val = if pos_z then e else inv_op op e
                in if x_val `fop` y_val == z_val then g env cs'
                else error $ format_err cs env op x_val y_val e

-- | Interpret a single IL constraint as a rank-1 constraint
r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw constr = case constr of
  -- no unknowns 
  CBinop op (TConst c,TConst d,TConst e) ->
    let cd = interp_op op c d
    in if cd == e then
         R1C (const_poly nw zero,const_poly nw zero,const_poly nw zero)
       else error $ "not satisfiable: " ++ show c ++ show op ++ show d
            ++ " == " ++ show e
  
  -- one unknown
  CBinop op (TConst c,TConst d,TVar pos_z z) ->
    let cd = interp_op op c d
    in R1C (const_poly nw one,var_poly nw (pos_z,z),const_poly nw cd)
  CBinop op (TConst c,TVar pos_y y,TConst e) ->
    r1c_of_c nw (CBinop op
                 ( TConst $ unit_of_op op 
                 , TConst $ inv_interp_op op e c
                 , TVar pos_y y))
  CBinop op (TVar pos_x x,TConst d,TConst e) ->
    r1c_of_c nw (CBinop op
                 ( TConst $ unit_of_op op
                 , TConst $ inv_interp_op op e d
                 , TVar pos_x x))

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
