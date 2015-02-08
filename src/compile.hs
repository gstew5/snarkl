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

-- | Add constraint 'b^2 = b'.
ensure_boolean :: Field a => Var -> State (CEnv a) ()
ensure_boolean b  
  = do { b_sq <- fresh_var
       ; add_constraint (CBinop Mult (b,b,b_sq))
       ; add_constraint (CVar (b_sq,b)) } 

-- | Constraint 'x \/ y = z'.
-- The encoding is: x+y - z = x*y; assumes x and y are boolean.
encode_or :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_or (x,y,z)
  = do { x_mult_y <- fresh_var
       ; x_plus_y <- fresh_var
       ; add_constraint (CBinop Mult (x,y,x_mult_y))
       ; add_constraint (CBinop Add (x,y,x_plus_y))
       ; add_constraint (CBinop Sub (x_plus_y,z,x_mult_y)) }

-- | Constraint 'x xor y = z'.
-- The encoding is: x+y - z = 2(x*y); assumes x and y are boolean.
encode_xor :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_xor (x,y,z)
  = do { x_mult_y <- fresh_var
       ; x_plus_y <- fresh_var
       ; two_x_mult_y <- fresh_var
       ; add_constraint (CBinop Mult (x,y,x_mult_y))
       ; add_constraint (CBinop Add (x,y,x_plus_y))
       ; add_constraint (CBinop Add (x_mult_y,x_mult_y,two_x_mult_y))
       ; add_constraint (CBinop Sub (x_plus_y,z,two_x_mult_y)) }

-- | Encode the boolean constraint 'x op y = z'.
-- assumes the caller enforces that x and y are boolean.
encode_binop :: Field a => Op -> (Var,Var,Var) -> State (CEnv a) ()
encode_binop op (x,y,z)
  | is_boolean op
  = let g And = encode_binop Mult (x,y,z)
        g Or  = encode_or (x,y,z)
        g XOr = encode_xor (x,y,z)
        g Add = error "internal error"
        g Sub = error "internal error"
        g Mult = error "internal error"
        g Div = error "internal error"        
    in g op

  | otherwise
  = add_constraint (CBinop op (x,y,z))

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { add_constraint (CVar (out,x)) }
  EVal c ->
    do { add_constraint (CVal (out,c)) }
  EBinop op e1 e2 ->
    do { e1_out <- fresh_var
       ; e2_out <- fresh_var
       ; if is_boolean op
         then do { ensure_boolean e1_out
                 ; ensure_boolean e2_out }
         else return ()
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2
       ; encode_binop op (e1_out,e2_out,out) }
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
       ; encode_binop Or (b_e1,bn_e2,out) }
  EAssign e1 e2 ->
    do { let x = var_of_exp e1
       ; e2_out <- fresh_var
       ; cs_of_exp e2_out e2
       ; add_constraint (CVar (x,e2_out)) }
  ESeq le -> g le 
    where g []   = error "internal error: empty ESeq"
          g [e1] = cs_of_exp out e1
          g (e1 : le')  
            = do { e1_out <- fresh_var
                 ; cs_of_exp e1_out e1
                 ; g le' }
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
               Int   -- ^ Number of variables (determined by frontend)
            -> Exp a -- ^ Expression to be compiled
            -> ( [a] -> [a] -- ^ Function from inputs to witnesses
               , R1CS a)    -- ^ The resulting rank-1 constraint system
compile_exp nv e
  = let out = nv -- NOTE: Variables are zero-indexed by the frontend.
        cenv_init    = CEnv [] (out+1) 
        ((f,r1cs),_) = runState (r1cs_of_exp out e) cenv_init
        nw           = num_vars r1cs
        zero_map         = Map.fromList $ zip (take nw [0..]) (repeat zero)
        input_map inputs = Map.fromList (zip [0..] inputs)
        -- NOTE: Even if some variables appear in none of the
        -- generated constraints, we must assign some (dummy) value in
        -- the witness. The dummies ensure that the witness list has
        -- the required length (we treat witnesses interchangeably as
        -- maps and position-indexed lists in places).
        g inputs
          = let witness_map = f (input_map inputs) `Map.union` zero_map
            in map snd $ Map.toList witness_map
    in (g,r1cs)
