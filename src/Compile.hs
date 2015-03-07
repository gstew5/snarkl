{-# LANGUAGE GADTs #-}

module Compile 
  ( CEnv(CEnv)
  , fresh_var
  , cs_of_exp
  , get_constraints
  , constraints_of_exp
  , r1cs_of_exp
  ) where

import Data.Typeable
import qualified Data.IntMap.Lazy as Map
import qualified Data.Set as Set
import Control.Monad.State

import Common
import Errors
import Field
import R1CS
import Simplify
import Solve
import Dataflow
import Source
import Expr
import Constraints

----------------------------------------------------------------
--                      Source -> Expr                        --
----------------------------------------------------------------

exp_of_val :: Field a => Val ty a -> Exp a
exp_of_val v = case v of
  VField c -> EVal c
  VTrue -> EVal one
  VFalse -> EVal zero
  VUnit -> EUnit

exp_of_texp :: Field a => TExp ty a -> Exp a
exp_of_texp te = case te of
  TEVar (TVar x) -> EVar x
  TEVal v -> exp_of_val v
  TEBinop (TOp op) te1 te2 ->
    exp_binop op (exp_of_texp te1) (exp_of_texp te2)
  TEIf te1 te2 te3 ->
    EIf (exp_of_texp te1) (exp_of_texp te2) (exp_of_texp te3)
  TEAssign te1 te2 ->
    EAssign (exp_of_texp te1) (exp_of_texp te2)
  TESeq te1 te2 -> exp_seq (exp_of_texp te1) (exp_of_texp te2)


----------------------------------------------------------------
--                      Expr -> Constraints                   --
----------------------------------------------------------------

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
  = encode_binop Mult (b,b,b)

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
       ; add_constraint
           (CAdd one $ Map.fromList [(x,neg one),(neg_x,neg one)])
       ; add_constraint
           (CAdd one $ Map.fromList [(y,neg one),(neg_y,neg one)])  
       ; encode_binop Mult (neg_x,neg_y,neg_x_mult_neg_y)
       ; encode_binop Add (x_mult_y,neg_x_mult_neg_y,z)
       }

-- | Encode the constraint 'x op y = z'.
encode_binop :: Field a => Op -> (Var,Var,Var) -> State (CEnv a) ()
encode_binop op (x,y,z) = g op
  where g And = encode_binop Mult (x,y,z)
        g Or  = encode_or (x,y,z)
        g XOr = encode_xor (x,y,z)
        g Eq  = encode_boolean_eq (x,y,z)        

        g Add
          = add_constraint
            $ CAdd zero $ Map.fromList [(x,one),(y,one),(z,neg one)]

        g Sub
          = add_constraint
            $ CAdd zero $ Map.fromList [(x,one),(y,neg one),(z,neg one)]
            
        g Mult
          = add_constraint
            $ CMult (one,x) (one,y) (one,Just z)

        g Div
          = fail_with $ ErrMsg "div not yet implemented"

encode_linear :: Field a => Var -> [Var] -> State (CEnv a) ()
encode_linear out xs
  = add_constraint
    $ CAdd zero $ Map.fromList $ (out,neg one) : zip xs (repeat one)

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { ensure_equal (out,x)
       }
    
  EVal c ->
    do { ensure_const (out,c)
       }

  EBinop op es ->
    let g [] = return []
        g (e1 : es')
          = do { e1_out <- fresh_var
               ; cs_of_exp e1_out e1
               ; labels <- g es'
               ; return $ e1_out : labels
               }

        h []       = return ()
        h (_ : []) = fail_with $ ErrMsg ("wrong arity in " ++ show e)
        h (l1 : l2 : []) = encode_binop op (l1,l2,out)
        h (l1 : l2 : labels')
          = do { res_out <- fresh_var
               ; h (res_out : labels')
               ; encode_binop op (l1,l2,res_out)
               }
            
    in do { labels <- g es
          ; case op of
              -- Encode x1 + x2 + ... + xn directly as a linear constraint.
              Add -> encode_linear out labels
              -- Otherwise, do the pairwise encoding.
              _ -> h labels
          }
       
  EIf b e1 e2 ->
    do { b_out  <- fresh_var -- b
       ; bn_out <- fresh_var -- (1-b)
       ; e1_out <- fresh_var -- e1
       ; e2_out <- fresh_var -- e2
       ; b_e1   <- fresh_var -- b*e1
       ; bn_e2  <- fresh_var -- (1-b)*e2
         
       ; cs_of_exp b_out b
       ; cs_of_exp bn_out (EBinop Sub [EVal one,b])
       ; cs_of_exp e1_out e1
       ; cs_of_exp e2_out e2

       ; encode_binop Mult (b_out,e1_out,b_e1)
       ; encode_binop Mult (bn_out,e2_out,bn_e2)
       ; encode_binop Or (b_e1,bn_e2,out)
       }
    
  -- NOTE: when compiling assignments, the naive thing to do is
  -- to introduce a new var, e2_out, bound to result of e2 and
  -- then ensure that e2_out == x. We optimize by passing x to
  -- compilation of e2 directly.
  EAssign e1 e2 ->
    do { let x = var_of_exp e1
       ; cs_of_exp x e2
       }

  ESeq le -> g le 
    where g []   = fail_with $ ErrMsg "internal error: empty ESeq"
          g [e1] = cs_of_exp out e1
          g (e1 : le')  
            = do { e1_out <- fresh_var
                 ; cs_of_exp e1_out e1
                 ; g le'
                 }
  EUnit ->
    do { return () }

-- | Compile a list of arithmetic constraints to a rank-1 constraint
-- system.  Takes as input the constraints, the input variables, and
-- the output variables, and return the corresponding R1CS.
r1cs_of_constraints :: Field a
                    => ConstraintSystem a 
                    -> R1CS a
r1cs_of_constraints cs
  = let  -- Simplify resulting constraints.
        (_,cs_simpl) = do_simplify Map.empty cs
        cs_dataflow  = remove_unreachable cs_simpl
         -- Renumber constraint variables sequentially, from 0 to
         -- 'max_var'. 'renumber_f' is a function mapping variables to
         -- their renumbered counterparts.
        (renumber_f,cs') = renumber_constraints cs_dataflow
         -- 'f' is a function mapping input bindings to witnesses.    
        f = solve cs' . Map.mapKeys renumber_f
    in r1cs_of_cs cs' f

-- | Compile an expression to a constraint system.  Takes as input the
-- expression, the expression's input variables, and the name of the
-- output variable.
constraints_of_exp :: Field a
            => Var -- ^ Output variable
            -> [Var] -- ^ Input variables
            -> [Var] -- ^ Boolean input variables            
            -> Exp a -- ^ Expression
            -> ConstraintSystem a
constraints_of_exp out in_vars boolean_in_vars e
  = let cenv_init = CEnv Set.empty (out+1)
        (constrs,_) = runState go cenv_init
    in constrs
  where go = do { -- Compile 'e' to constraints 'cs', with output wire 'out'.
                  cs_of_exp out e
                  -- Add boolean constraints
                ; mapM ensure_boolean boolean_in_vars
                ; cs <- get_constraints
                ; let constraint_set = Set.fromList cs
                ; let num_constraint_vars
                        = length $ constraint_vars constraint_set
                ; return
                  $ ConstraintSystem
                    constraint_set num_constraint_vars in_vars [out]
                } 

-- | Compile an expression 'e' to R1CS.
r1cs_of_exp :: ( Field a
               , Typeable ty
               ) =>
               Var   -- ^ The next free variable (calculated by frontend)
            -> [Var] -- ^ Input variables (determined by frontend)
            -> TExp ty a -- ^ Expression to be compiled
            -- | The resulting rank-1 constraint system.
            -> R1CS a
r1cs_of_exp out in_vars te
  = let boolean_in_vars
          = Set.toList
            $ Set.fromList in_vars
              `Set.intersection` Set.fromList (boolean_vars_of_texp te)
        e = exp_of_texp te
        constrs = constraints_of_exp out in_vars boolean_in_vars e
        r1cs = r1cs_of_constraints constrs
    in r1cs

