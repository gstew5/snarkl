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
  CBinop COp (Term a,Term a,Var) -- x `op` y = z
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
        g env (c0@(CBinop op (TConst c,TConst d,z)) : cs')
          = let fop = interp_op op
            in case Map.lookup z env of
              Nothing -> g (Map.insert z (c `fop` d) env) (cs' ++ [c0])
              Just e  -> if c `fop` d == e then g env cs'
                         else error $ format_err cs env op c d e
        g env (c0@(CBinop op (TConst c,TVar pos_y y,z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup y env,Map.lookup z env) of
              -- (y   ,   z)
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just e) ->
                let y_val = if pos_y then e `fop'` c else inv_op op (e `fop'` c)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              (Just d,Nothing) ->
                let y_val = if pos_y then d else inv_op op d
                    z_val = c `fop` y_val
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just d,Just e) ->
                let y_val = if pos_y then d else inv_op op d
                in if c `fop` y_val == e then g env cs'
                   else error $ format_err cs env op c y_val e
        g env (c0@(CBinop op (TVar pos_x x,TConst d,z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup x env,Map.lookup z env) of
              -- (x   ,   z)              
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just e) ->
                let x_val = if pos_x then e `fop'` d else inv_op op (e `fop'` d)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              (Just c,Nothing) ->
                let x_val = if pos_x then c else inv_op op c
                    z_val = x_val `fop` d
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just c,Just e) ->
                let x_val = if pos_x then c else inv_op op c
                in if x_val `fop` d == e then g env cs'
                   else error $ format_err cs env op x_val d e
        g env (c0@(CBinop op (TVar pos_x x,TVar pos_y y,z)) : cs')
          = let fop  = interp_op op
                fop' = inv_interp_op op
            in case (Map.lookup x env,Map.lookup y env,Map.lookup z env) of
              -- (x   ,   y   ,   z)              
              (Nothing,Nothing,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Nothing,Just _) -> g env (cs' ++ [c0])
              (Nothing,Just _,Nothing) -> g env (cs' ++ [c0])
              (Nothing,Just d,Just e) -> 
                let y_val = if pos_y then d else inv_op op d
                    x_val = if pos_x then e `fop'` y_val else inv_op op (e `fop'` y_val)
                in g (Map.insert x x_val env) (cs' ++ [c0])
              (Just _,Nothing,Nothing) -> g env (cs' ++ [c0])
              (Just c,Nothing,Just e) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then e `fop'` x_val else inv_op op (e `fop'` x_val)
                in g (Map.insert y y_val env) (cs' ++ [c0])
              (Just c,Just d,Nothing) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then d else inv_op op d
                    z_val = x_val `fop` y_val
                in g (Map.insert z z_val env) (cs' ++ [c0])
              (Just c,Just d,Just e) ->
                let x_val = if pos_x then c else inv_op op c
                    y_val = if pos_y then d else inv_op op d
                in if x_val `fop` y_val == e then g env cs'
                else error $ format_err cs env op x_val y_val e

-- | Interpret a single IL constraint as a rank-1 constraint
r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw constr = case constr of
  -- one unknown
  CBinop op (TConst c,TConst d,z) ->
    let cd = interp_op op c d
    in R1C (const_poly nw one,var_poly nw (True,z),const_poly nw cd)

  -- two unknowns
  -- c + y = z
  CBinop CAdd (TConst c,TVar pos_y y,z) ->
    R1C (const_poly nw one,cy_poly nw c (pos_y,y),var_poly nw (True,z))
  -- x + d = z    
  CBinop CAdd (TVar pos_x x,TConst d,z) ->
    R1C (const_poly nw one,cy_poly nw d (pos_x,x),var_poly nw (True,z))

  -- c * y = z
  CBinop CMult (TConst c,TVar pos_y y,z) ->
    R1C (const_poly nw c,var_poly nw (pos_y,y),var_poly nw (True,z))
  -- x * d = z    
  CBinop CMult (TVar pos_x x,TConst d,z) ->
    R1C (const_poly nw d,var_poly nw (pos_x,x),var_poly nw (True,z))

  -- three unknowns
  -- x + y = z
  CBinop CAdd (TVar pos_x x,TVar pos_y y,z)
    | x == y, pos_x == pos_y ->
      R1C (const_poly nw (add one one),var_poly nw (pos_x,x),var_poly nw (True,z)) 
  CBinop CAdd (TVar pos_x x,TVar pos_y y,z) 
    | x == y, pos_x /= pos_y ->
      R1C (const_poly nw zero,const_poly nw zero,var_poly nw (True,z)) 
  CBinop CAdd (TVar pos_x x,TVar pos_y y,z) 
    | otherwise ->
      R1C (const_poly nw one,add_poly nw (pos_x,x) (pos_y,y),var_poly nw (True,z))

  -- x * y = z
  CBinop CMult (TVar pos_x x,TVar pos_y y,z) ->
    R1C (var_poly nw (pos_x,x),var_poly nw (pos_y,y),var_poly nw (True,z))

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs
