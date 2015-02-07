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

invert_op :: Op -> Op
invert_op op = case op of
  Add -> Sub
  Sub -> Add
  Mult -> Inv
  Inv -> Mult

interp_op :: Field a => Op -> a -> a -> a
interp_op op = case op of
  Add -> add
  Sub -> \a1 a2 -> a1 `add` (neg a2)
  Mult -> mult
  Inv -> \a1 a2 -> if a2 == zero then zero else a1 `mult` (inv a2)

data Constraint a where
  CVal   :: Field a => (Var,a)  -> Constraint a -- x = c
  CVar   :: (Var,Var)           -> Constraint a -- x = y
  CBinop :: Op -> (Var,Var,Var) -> Constraint a -- x `op` y = z

instance Show a => Show (Constraint a) where
  show (CVal (x,c)) = show x ++ "==" ++ show c
  show (CVar (x,y)) = show x ++ "==" ++ show y
  show (CBinop op (x,y,z))
    = show x ++ show op ++ show y ++ "==" ++ show z    

type Assgn a = Map.Map Var a

solve_constraints :: Field a => [Constraint a] -- constraints to be solved
                  -> Assgn a -- initial assignment
                  -> Assgn a -- resulting assignment
solve_constraints cs env = g env cs
  where g env [] = env
        g env (CVal (x,c) : cs') = g (Map.insert x c env) cs'
        g env (CVar (x,y) : cs')
          = case (Map.lookup x env,Map.lookup y env) of
              (Nothing,Nothing) -> g env (cs' ++ [CVar (x,y)])
              (Just c,Nothing)  -> g (Map.insert y c env) cs'
              (Nothing,Just d)  -> g (Map.insert x d env) cs'
              (Just c,Just d)   ->
                if c == d then g env cs'
                else error $ show c ++ " == " ++ show d
                             ++ ": inconsistent assignment"
        g env (CBinop op (x,y,z) : cs')
          = let f_op  = interp_op op
                fn_op = interp_op (invert_op op)  
            in case (Map.lookup x env,Map.lookup y env,Map.lookup z env) of
              (Just c,Just d,Nothing) -> g (Map.insert z (c `f_op` d) env) cs'
              (Just c,Nothing,Just e) -> g (Map.insert y (e `fn_op` c) env) cs'
              (Nothing,Just d,Just e) -> g (Map.insert x (e `fn_op` d) env) cs'
              (Just c,Just d,Just e)  ->
                if e == c `f_op` d then g env cs'
                else error $ show c ++ " " ++ show op ++ " " ++ show d
                             ++ "==" ++ show e ++ ": inconsistent assignment"
              (_,_,_) -> g env (cs' ++ [CBinop op (x,y,z)])

r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw c = case c of
  CVal (x,c)    -> R1C (const_poly nw one,var_poly nw x,const_poly nw c)
  CVar (x,y)    -> R1C (const_poly nw one,var_poly nw x,var_poly nw y)
  CBinop Add  (x,y,z) -> R1C (const_poly nw one,add_poly nw x y,var_poly nw z)
  CBinop Sub  (x,y,z) -> R1C (const_poly nw one,sub_poly nw x y,var_poly nw z)  
  CBinop Mult (x,y,z) -> R1C (var_poly nw x,var_poly nw y,var_poly nw z)

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs
