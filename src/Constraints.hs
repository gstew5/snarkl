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

data Constraint a =
    CVal (Var,a)              -- x = c
  | CConst COp (a,Var,Var)    -- c `op` y = z
  | CBinop COp (Atom,Var,Var) -- x `op` y = z
  deriving (Eq,Ord)

instance Show a => Show (Constraint a) where
  show (CVal (x,c)) = show x ++ "==" ++ show c
  show (CConst op (c,y,z))
    = show c ++ show op ++ show y ++ "==" ++ show z  
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
solve_constraints :: Field a => [Constraint a] -- constraints to be solved
                  -> Assgn a -- initial assignment
                  -> Assgn a -- resulting assignment
solve_constraints cs env0 = g env0 cs
  where g env [] = env
        g env (CVal (x,c) : cs') = g (Map.insert x c env) cs'
        g env (c0@(CConst op (c,y,z)) : cs')
          = let f_op  = interp_op op
                fn_op = inv_interp_op op
            in case (Map.lookup y env,Map.lookup z env) of
              (Nothing,Nothing) -> g env (cs' ++ [c0])
              (Just d,Nothing)  -> g (Map.insert z (c `f_op` d) env) cs'
              (Nothing,Just e)  -> g (Map.insert y (e `fn_op` c) env) cs'
              (Just d,Just e)   ->
                if c `f_op` d == e then g env cs'
                else error $ format_err cs env op c d e
        g env (c0@(CBinop op (x,y,z)) : cs')
          = let f_op  = interp_op op
                fn_op = inv_interp_op op
            in case ( Map.lookup (var_of_atom x) env
                    , Map.lookup y env
                    , Map.lookup z env) of
              (Just c,Just d,Nothing) ->
                let c' = if is_pos x then c else neg c
                in g (Map.insert z (c' `f_op` d) env) (cs' ++ [c0])
              (Just c,Nothing,Just e) ->
                let c'  = if is_pos x then c else neg c
                    res = e `fn_op` c'
                in g (Map.insert y res env) (cs' ++ [c0])
              (Nothing,Just d,Just e) ->
                let res  = e `fn_op` d
                    res' = if is_pos x then res else neg res
                in g (Map.insert (var_of_atom x) res' env) (cs' ++ [c0])
              (Just c,Just d,Just e)  ->
                let c' = if is_pos x then c else neg c
                in if e == c' `f_op` d then g env cs'
                else error $ format_err cs env op c' d e 
              (_,_,_) -> g env (cs' ++ [c0])
                  
r1c_of_c :: Field a => Int -> Constraint a -> R1C a
r1c_of_c nw c = case c of
  CVal (x,c') -> R1C ( const_poly nw one
                     , var_poly nw (Pos x)
                     , const_poly nw c')
  CConst CAdd (c',y,z) ->  R1C ( const_poly nw one
                               , cy_poly nw c' (Pos y)
                               , var_poly nw (Pos z))
  CConst CMult (c',y,z) -> R1C ( const_poly nw c'
                               , var_poly nw (Pos y)
                               , var_poly nw (Pos z))
  CBinop CAdd  (x,y,z) -> case x of
    Pos x'
      | x' == y -> R1C ( const_poly nw (add one one)
                       , var_poly nw x
                       , var_poly nw (Pos z))
    Pos _
      | otherwise -> R1C ( const_poly nw one
                       , add_poly nw x (Pos y)
                       , var_poly nw (Pos z))
    Neg x'
      | x' == y -> R1C ( const_poly nw zero
                       , const_poly nw zero
                       , var_poly nw (Pos z))
    Neg _
      | otherwise -> R1C ( const_poly nw one
                       , add_poly nw x (Pos y)
                       , var_poly nw (Pos z))
  CBinop CMult (x,y,z) ->
    R1C (var_poly nw x,var_poly nw (Pos y),var_poly nw (Pos z))

r1cs_of_cs :: Field a => Int -> [Constraint a] -> R1CS a
r1cs_of_cs nw cs = R1CS $ map (r1c_of_c nw) cs
