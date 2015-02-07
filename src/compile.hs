module Compile 
  ( compile_exp 
  ) where

import qualified Data.Map.Strict as Map
import Control.Monad.State

import Common
import Field
import R1CS
import Constraints
import Lang

data CEnv a =
  CEnv { cur_cs   :: [Constraint a]
       , next_var :: Var }

add_constraint :: Constraint a -> State (CEnv a) ()
add_constraint c = modify (\cenv -> cenv {cur_cs = c : cur_cs cenv})

get_constraints :: State (CEnv a) [Constraint a]
get_constraints
  = do { cenv <- get
       ; return (cur_cs cenv) }

get_next_var :: State (CEnv a) Var
get_next_var
  = do { cenv <- get
       ; return (next_var cenv) }

get_num_vars :: State (CEnv a) Int
get_num_vars = get_next_var

set_next_var :: Var -> State (CEnv a) ()
set_next_var next = modify (\cenv -> cenv { next_var = next })

fresh_var :: State (CEnv a) Var
fresh_var
  = do { next <- get_next_var
       ; set_next_var (next + 1)
       ; return next }

-- add constraint 'x \/ y = c'
add_or_constraints :: Field a => (Var,Var,Var) -> State (CEnv a) ()
add_or_constraints (x,y,z)
  = do { x_mult_y <- fresh_var
       ; x_plus_y <- fresh_var
       ; add_constraint (CBinop Mult (x,y,x_mult_y))
       ; add_constraint (CBinop Add (x,y,x_plus_y))
       ; add_constraint (CBinop Sub (x_plus_y,z,x_mult_y)) }

-- add constraint 'b^2 = b'
ensure_boolean :: Field a => Var -> State (CEnv a) ()
ensure_boolean b
  = do { b_sq <- fresh_var
       ; add_constraint (CBinop Mult (b,b,b_sq))
       ; add_constraint (CVar (b_sq,b)) }

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { add_constraint (CVar (out,x)) }
  EVal c ->
    do { add_constraint (CVal (out,c)) }
  EBinop op e1 e2 ->
    do { e1_out <- fresh_var
       ; e2_out <- fresh_var        
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2
       ; add_constraint (CBinop op (e1_out,e2_out,out)) }
  EIf b e1 e2 ->
    do { b_out  <- fresh_var -- b
       ; bn_out <- fresh_var -- (1-b)
       ; e1_out <- fresh_var -- e1
       ; e2_out <- fresh_var -- e2
       ; b_e1   <- fresh_var -- b*e1
       ; bn_e2  <- fresh_var -- (1-b)*e2
         
       ; cs_of_exp b_out b
       ; cs_of_exp bn_out (EBinop Sub (EVal one) b)
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2

       ; ensure_boolean b_out 
       ; add_constraint (CBinop Mult (b_out,e1_out,b_e1))
       ; add_constraint (CBinop Mult (bn_out,e2_out,bn_e2))
       ; add_or_constraints (b_e1,bn_e2,out) }
  EAssign e1 e2 ->
    do { let x = var_of_exp e1
       ; e2_out <- fresh_var
       ; cs_of_exp e2_out e2
       ; add_constraint (CVar (x,e2_out)) }
  ESeq e1 e2 ->
    do { e1_out <- fresh_var
       ; cs_of_exp e1_out e1
       ; cs_of_exp out e2 }
  EUnit ->
    do { return () }

r1cs_of_exp :: Field a => Var -> Exp a
            -> State (CEnv a) (Assgn a -> Assgn a,R1CS a)
r1cs_of_exp out e
  = do { cs_of_exp out e
       ; nv <- get_num_vars
       ; cs <- get_constraints
       ; let f = solve_constraints cs
       ; return $ (f,r1cs_of_cs nv cs) }

compile_exp :: Field a =>
               Int   -- number of inputs variables (determined by frontend)
            -> Int   -- number of variables (determined by frontend)
            -> Exp a -- expression to be compiled
            -> ( [a] -> [a] -- function from inputs to witnesses 
               , R1CS a)    -- the resulting rank-1 constraint system
compile_exp num_inputs nw e
  = let out = nw -- NOTE: variables zero-indexed by frontend
        cenv_init = CEnv [] (out+1) 
        ((f,r1cs),_) = runState (r1cs_of_exp out e) cenv_init
        g w = map snd $ Map.toList $ f $ Map.fromList (zip [0..] w)
    in (g,r1cs)

e1 :: Exp Rational
e1 = EBinop Add (EVal 3) (EVal 5)

e2 :: Exp Rational
e2 = EBinop Sub (EBinop Sub (EVal 3) (EBinop Add (EVal 5) (EVal 3)))
       (EBinop Mult (EVal 8) (EVal 8))

e3 :: Exp Rational
e3 = EBinop Sub (EVal 1) (EVar 0)

e8 :: Exp Rational
e8 = EIf (EVar 0) (EVal 55) (EVal 77)  
