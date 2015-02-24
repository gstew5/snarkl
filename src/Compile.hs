module Compile 
  ( CEnv(CEnv)
  , fresh_var
  , cs_of_exp
  , get_constraints
  , compile_exp
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State

import Common
import Field
import R1CS
import Constraints
import Simplify
import Lang

data CEnv a =
  CEnv { cur_cs   :: Set.Set (Constraint a)
       , next_var :: Var
       }

add_constraint :: Ord a => Constraint a -> State (CEnv a) ()
add_constraint c
  = modify (\cenv -> cenv {cur_cs = Set.insert c $ cur_cs cenv})

get_constraints :: State (CEnv a) [Constraint a]
get_constraints
  = do { cenv <- get
       ; return $ Set.toList $ cur_cs cenv
       }

get_next_var :: State (CEnv a) Var
get_next_var
  = do { cenv <- get
       ; return (next_var cenv)
       }

set_next_var :: Var -> State (CEnv a) ()
set_next_var next = modify (\cenv -> cenv { next_var = next })

fresh_var :: State (CEnv a) Var
fresh_var
  = do { next <- get_next_var
       ; set_next_var (next + 1)
       ; return next
       }

-- | Add constraint 'x = y'
ensure_equal :: Field a => (Var,Var) -> State (CEnv a) ()
ensure_equal (x,y)
  = add_constraint
    $ CAdd zero
    $ Map.fromList [(x,one),(y,neg one)]

-- | Add constraint 'x = c'
ensure_const :: Field a => (Var,a) -> State (CEnv a) ()
ensure_const (x,c)
  = add_constraint
    $ CAdd c
    $ Map.fromList [(x,neg one)]

-- | Add constraint 'b^2 = b'.
ensure_boolean :: Field a => Var -> State (CEnv a) ()
ensure_boolean b  
  = do { b_sq <- fresh_var
       ; encode_binop Mult (b,b,b_sq)
       ; ensure_equal (b_sq,b)
       }

-- | Constraint 'x \/ y = z'.
-- The encoding is: x+y - z = x*y; assumes x and y are boolean.
encode_or :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_or (x,y,z)
  = do { x_mult_y <- fresh_var
       ; encode_binop Mult (x,y,x_mult_y)
       ; add_constraint
         $ CAdd zero
         $ Map.fromList [(x,one),(y,one),(z,neg one),(x_mult_y,neg one)]
       }

-- | Constraint 'x xor y = z'.
-- The encoding is: x+y - z = 2(x*y); assumes x and y are boolean.
encode_xor :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_xor (x,y,z)
  = do { x_mult_y <- fresh_var
       ; encode_binop Mult (x,y,x_mult_y)
       ; add_constraint
         $ CAdd zero
         $ Map.fromList [(x,one),(y,one),(z,neg one)
                        ,(x_mult_y,neg (one `add`one))]
       }

-- | Constraint 'x == y = z' ASSUMING x, y are boolean.
-- The encoding is: x*y + (1-x)*(1-y) = z.
encode_boolean_eq :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_boolean_eq (x,y,z)
  = do { x_mult_y <- fresh_var
       ; neg_x    <- fresh_var
       ; neg_y    <- fresh_var
       ; neg_x_mult_neg_y <- fresh_var
       ; encode_binop Mult (x,y,x_mult_y)
       ; add_constraint (CAdd one $ Map.fromList [(x,neg one),(neg_x,neg one)])
       ; add_constraint (CAdd one $ Map.fromList [(y,neg one),(neg_y,neg one)])   
       ; encode_binop Mult (neg_x,neg_y,neg_x_mult_neg_y)
       ; encode_binop Add (x_mult_y,neg_x_mult_neg_y,z)
       }


-- | Encode the boolean constraint 'x op y = z'.
-- Assumes the caller enforces that x and y are boolean.
encode_binop :: Field a => Op -> (Var,Var,Var) -> State (CEnv a) ()
encode_binop op (x,y,z)
  | is_boolean op
  = let g And = encode_binop Mult (x,y,z)
        g Or  = encode_or (x,y,z)
        g XOr = encode_xor (x,y,z)
        g Eq  = encode_boolean_eq (x,y,z)        
        g Add = error "internal error"
        g Sub = error "internal error"
        g Mult = error "internal error"
        g Div = error "internal error"        
    in g op

  | otherwise
  = let g Add = add_constraint
                $ CAdd zero $ Map.fromList [(x,one),(y,one),(z,neg one)]
        g Sub = add_constraint
                $ CAdd zero $ Map.fromList [(x,one),(y,neg one),(z,neg one)]    
        g Mult = add_constraint
                 $ CMult (one,x) (one,y) (one,Just z)
        g Div = error "division not yet implemented"
        g And = error "internal error"
        g Or  = error "internal error"
        g XOr = error "internal error"
        g Eq = error "internal error"                
    in g op

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { ensure_equal (out,x) }
  EVal c ->
    do { ensure_const (out,c) }
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
       ; encode_binop Mult (b_out,e1_out,b_e1)
       ; encode_binop Mult (bn_out,e2_out,bn_e2)
       ; encode_binop Or (b_e1,bn_e2,out) }
  -- NOTE: when compiling assignments, the naive thing to do is
  -- to introduce a new var, e2_out, bound to result of e2 and
  -- then ensure that e2_out == x. We optimize by passing x to
  -- compilation of e2 directly.
  EAssign e1 e2 ->
    do { let x = var_of_exp e1
       ; cs_of_exp x e2 }
  ESeq le -> g le 
    where g []   = error "internal error: empty ESeq"
          g [e1] = cs_of_exp out e1
          g (e1 : le')  
            = do { e1_out <- fresh_var
                 ; cs_of_exp e1_out e1
                 ; g le' }
  EUnit ->
    do { return () }

-- | Compile a list of arithmetic constraints to a rank-1 constraint
-- system.  Takes as input the constraints, the input variables, and
-- the output variables, and return the corresponding R1CS.
r1cs_of_constraints :: Field a
                    => Var -- ^ Designated output "wire"
                    -> [Var] -- ^ Remaining output variables (observables)
                    -> [Var] -- ^ Input variables
                    -> [Constraint a] -- ^ Constraints
                    -> R1CS a
r1cs_of_constraints out out_vars in_vars cs
  = let pinned_vars = out : out_vars ++ in_vars
         -- Simplify resulting constraint set, with pinned vars 'pinned_vars'.
        (_,cs_simpl) = do_simplify pinned_vars Map.empty cs
         -- Renumber constraint variables sequentially, from 0 to 'max_var'.
         -- * 'nv'' is the new total number of variables in the renumbered system
         -- * 'renumber_f' is a function mapping variables to their
         --   renumbered counterparts.    
        (nv',renumber_f,cs') = renumber_constraints in_vars cs_simpl
        renumber_inputs = Map.mapKeys renumber_f
         -- 'f' is a function mapping input bindings to witnesses.                 
        f = solve_constraints (map renumber_f pinned_vars) cs' . renumber_inputs 
    in r1cs_of_cs cs' nv' (map renumber_f in_vars) (map renumber_f $ out : out_vars) f

-- | Compile an expression to a rank-1 constraint system.  Takes as
-- input the expression, the expression's input variables, and the
-- name of the output variable and returns the corresponding R1CS.
r1cs_of_exp :: Field a
            => Var -- ^ Output variable
            -> [Var] -- ^ Input variables
            -> Exp a -- ^ Expression
            -> State (CEnv a) (R1CS a)
r1cs_of_exp out in_vars e
  = do { -- Compile 'e' to a list of constraints 'cs', with output wire 'out'.
         cs_of_exp out e
       ; cs <- get_constraints
       ; return $ r1cs_of_constraints out [] in_vars cs
       } 

compile_exp :: Field a =>
               Int   -- ^ Number of variables (determined by frontend)
            -> [Var] -- ^ Input variables (determined by frontend)
            -> Exp a -- ^ Expression to be compiled
            -- | Returns the resulting rank-1 constraint system.
            -> R1CS a
compile_exp nv in_vars e
  = let out = nv 
        -- NOTE: Variables are zero-indexed by the frontend.
        cenv_init = CEnv Set.empty (out+1)
    in fst $ runState (r1cs_of_exp out in_vars e) cenv_init

