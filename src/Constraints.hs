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
