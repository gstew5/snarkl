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

data Constraint a where
  CVal   :: Field a => (Var,a)     -> Constraint a -- x = c
  CVar   :: (Var,Var)              -> Constraint a -- x = y
  CBinop :: COp -> (Atom,Atom,Var) -> Constraint a -- x `op` y = z

instance Show a => Show (Constraint a) where
  show (CVal (x,c)) = show x ++ "==" ++ show c
  show (CVar (x,y)) = show x ++ "==" ++ show y
  show (CBinop op (x,y,z))
    = show x ++ show op ++ show y ++ "==" ++ show z    

type Assgn a = Map.Map Var a

format_err :: Field a => [Constraint a] -> Assgn a -> a -> a -> String
format_err cs env c d
  = show c ++ " == " ++ show d
    ++ ": inconsistent assignment, in constraint context: "
    ++ show cs ++ ", in partial assignment context: " ++ show env

-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve_constraints :: Field a => [Constraint a] -- constraints to be solved
                  -> Assgn a -- initial assignment
                  -> Assgn a -- resulting assignment
solve_constraints cs env0 = g env0 cs
  where g env [] = env
        g env (CVal (x,c) : cs') = g (Map.insert x c env) cs'
        g env (c0@(CVar (x,y)) : cs')
          = case (Map.lookup x env,Map.lookup y env) of
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Just c,Nothing)  -> g (Map.insert y c env) cs'
              (Nothing,Just d)  -> g (Map.insert x d env) cs'
              (Just c,Just d)   ->
                if c == d then g env cs' else error $ format_err cs env c d 
        g env (c0@(CBinop op (x,y,z)) : cs')
          = let f_op  = interp_op op
            in case ( Map.lookup (var_of_atom x) env
                    , Map.lookup (var_of_atom y) env
                    , Map.lookup z env) of
              (Just c,Just d,Nothing) ->
                let c' = if is_pos x then c else neg c
                    d' = if is_pos y then d else neg d
                in g (Map.insert z (c' `f_op` d') env) (cs' ++ [c0])
              (Just c,Nothing,Just e) ->
                let c'  = if is_pos x then c else neg c
                    res = if is_pos y then neg c' `f_op` e
                          else neg (neg c' `f_op` e)
                in g (Map.insert (var_of_atom y) res env) (cs' ++ [c0])
              (Nothing,Just d,Just e) ->
                let d'  = if is_pos y then d else neg d 
                    res = if is_pos x then neg d' `f_op` e
                          else neg (neg d' `f_op` e)
                in g (Map.insert (var_of_atom x) res env) (cs' ++ [c0])
              (Just c,Just d,Just e)  ->
                let c' = if is_pos x then c else neg c
                    d' = if is_pos y then d else neg d
                in if e == c' `f_op` d' then g env cs'
                else error $ format_err cs env e (c' `f_op` d') 
              (_,_,_) -> g env (cs' ++ [c0])
                  
r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw c = case c of
  CVal (x,c') -> R1C (const_poly nw one,var_poly nw (Pos x),const_poly nw c')
  CVar (x,y)  -> R1C (const_poly nw one,var_poly nw (Pos x),var_poly nw (Pos y))
  CBinop CAdd  (x,y,z) ->
    if x /= y then R1C (const_poly nw one,add_poly nw x y,var_poly nw (Pos z))
    else R1C (const_poly nw (add one one),var_poly nw x,var_poly nw (Pos z))
  CBinop CMult (x,y,z) ->
    R1C (var_poly nw x,var_poly nw y,var_poly nw (Pos z))

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs
