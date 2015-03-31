{-# LANGUAGE GADTs #-}

module Compile 
  ( CEnv(CEnv)
  , fresh_var
  , cs_of_exp
  , get_constraints
  , constraints_of_exp
  , r1cs_of_exp
  , exp_of_texp
  ) where

import Data.Typeable
import qualified Data.IntMap.Lazy as Map
import qualified Data.Set as Set
import Control.Monad.State

import Common
import Errors
import Field
import R1CS
import SimplMonad
import Simplify
import Solve
import Dataflow
import TExpr
import Expr
import Constraints


----------------------------------------------------------------
--
-- Expr -> Constraints
--
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
    $ cadd zero [(x,one),(y,neg one)]

-- | Add constraint 'x = c'
ensure_const :: Field a => (Var,a) -> State (CEnv a) ()
ensure_const (x,c)
  = add_constraint
    $ cadd c [(x,neg one)]

-- | Add constraint 'b^2 = b'.
ensure_boolean :: Field a => Var -> State (CEnv a) ()
ensure_boolean b  
  = encode_binop Mult (b,b,b)

-- | Constraint 'x \/ y = z'.
-- The encoding is: x+y - z = x*y; assumes x and y are boolean.
encode_or :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_or (x,y,z) 
  = do { x_mult_y <- fresh_var 
       ; cs_of_exp x_mult_y (EBinop Mult [EVar x,EVar y])
       ; cs_of_exp x_mult_y (EBinop Sub 
                                    [EBinop Add [EVar x,EVar y]
                                    ,EVar z])
       }

-- | Constraint 'x xor y = z'.
-- The encoding is: x+y - z = 2(x*y); assumes x and y are boolean.
encode_xor :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_xor (x,y,z)
  = do { x_mult_y <- fresh_var
       ; encode_binop Mult (x,y,x_mult_y)
       ; add_constraint
         $ cadd zero [(x,one),(y,one),(z,neg one)
                     ,(x_mult_y,neg (one `add`one))]
       }
-- -- The following desugaring is preferable, but generates more constraints.
-- -- Perhaps something to investigate wrt. Simplify.hs.
--   = do { x_mult_y <- fresh_var
--        ; cs_of_exp x_mult_y (EBinop Mult 
--                                     [EVal (one `add` one)
--                                     ,EBinop Mult [EVar x,EVar y]])
--        ; cs_of_exp x_mult_y (EBinop Sub 
--                                     [EBinop Add [EVar x,EVar y]
--                                     ,EVar z])
--        }


-- | Constraint 'x == y = z' ASSUMING x, y are boolean.
-- The encoding is: x*y + (1-x)*(1-y) = z.
encode_boolean_eq :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_boolean_eq (x,y,z) = cs_of_exp z e
  where e = EBinop Add 
            [EBinop Mult [EVar x,EVar y]
            ,EBinop Mult 
                    [EBinop Sub [EVal one,EVar x]
                    ,EBinop Sub [EVal one,EVar y]]]

-- | Constraint 'x == y = z'.
-- The encoding is: z = (x-y == 0).
encode_eq :: Field a => (Var,Var,Var) -> State (CEnv a) ()
encode_eq (x,y,z) = cs_of_exp z e
  where e = EAssert
            (EVar z)
            (EUnop ZEq (EBinop Sub [EVar x,EVar y]))

-- | Constraint 'y = x!=0 ? 1 : 0'.
-- The encoding is:
-- for some m,
--    x*m = y
-- /\ (1-y)*x = 0
-- Cf. p7. of [pinnochio-sp13], which follows [setty-usenix12].
encode_zneq :: Field a => (Var,Var) -> State (CEnv a) ()
encode_zneq (x,y)
  = do { m <- fresh_var
       ; neg_y <- fresh_var
         -- The following 'magic' constraint resolves the value of
         -- nondet witness 'm':
         --   m = 0,      x = 0
         --   m = inv x,  x <> 0
       ; nm <- fresh_var
       ; add_constraint (CMagic nm [x,m] mf)
         -- END magic.
       ; cs_of_exp y (EBinop Mult [EVar x,EVar m])
       ; cs_of_exp neg_y (EBinop Sub [EVal one,EVar y])
       ; add_constraint 
           (CMult (one,neg_y) (one,x) (zero,Nothing))
       }
    where mf [x0,m0] 
            = do { tx <- bind_of_var x0
                 ; case tx of
                     Left _ -> return False
                     Right c -> 
                       if c == zero then 
                         do { bind_var (m0,zero)
                            ; return True
                            }
                       else case inv c of
                         Nothing -> 
                           fail_with 
                           $ ErrMsg ("expected " ++ show x0 ++ "==" ++ show c
                                     ++ " to be invertible")
                         Just c' -> 
                           do { bind_var (m0,c')
                              ; return True
                              }
                 }
          mf _ = fail_with 
                 $ ErrMsg "internal error in 'encode_zeq'"

-- | Constraint 'y == x==0:1?0'
encode_zeq :: Field a => (Var,Var) -> State (CEnv a) ()
encode_zeq (x,y) 
  = do { neg_y <- fresh_var
       ; encode_zneq (x,neg_y)
       ; cs_of_exp y (EBinop Sub [EVal one,EVar neg_y])
       }

-- | Encode the constraint 'un_op x = y'
encode_unop :: Field a => UnOp -> (Var,Var) -> State (CEnv a) ()
encode_unop op (x,y) = go op 
  where go ZEq = encode_zeq (x,y)

-- | Encode the constraint 'x op y = z'.
encode_binop :: Field a => Op -> (Var,Var,Var) -> State (CEnv a) ()
encode_binop op (x,y,z) = go op
  where go And = encode_binop Mult (x,y,z)
        go Or  = encode_or (x,y,z)
        go XOr = encode_xor (x,y,z)
        go Eq  = encode_eq (x,y,z)
        go BEq = encode_boolean_eq (x,y,z)        

        go Add
          = add_constraint
            $ cadd zero [(x,one),(y,one),(z,neg one)]

        go Sub
          = add_constraint
            $ cadd zero [(x,one),(y,neg one),(z,neg one)]
            
        go Mult
          = add_constraint
            $ CMult (one,x) (one,y) (one,Just z)

        go Div
          = add_constraint
            $ CMult (one,y) (one,z) (one,Just x)

encode_linear :: Field a => Var -> [Var] -> State (CEnv a) ()
encode_linear out xs
  = add_constraint
    $ cadd zero $ (out,neg one) : zip xs (repeat one)

cs_of_exp :: Field a => Var -> Exp a -> State (CEnv a) ()
cs_of_exp out e = case e of
  EVar x ->
    do { ensure_equal (out,x)
       }
    
  EVal c ->
    do { ensure_const (out,c)
       }

  EUnop op e1 -> 
    do { e1_out <- fresh_var 
       ; cs_of_exp e1_out e1
       ; encode_unop op (e1_out,out)
       }

  EBinop op es ->
    let go [] = return []
        go (e1 : es')
          = do { e1_out <- fresh_var
               ; cs_of_exp e1_out e1
               ; labels <- go es'
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
            
    in do { labels <- go es
          ; case op of
              -- Encode x1 + x2 + ... + xn directly as a linear constraint.
              Add -> encode_linear out labels
              -- Otherwise, do the pairwise encoding.
              _ -> h labels
          }

  -- Encoding: out = b*e1 \/ (1-b)e2 
  EIf b e1 e2 -> cs_of_exp out e0
    where e0 = EBinop Or
               [ EBinop Mult [b,e1]
               , EBinop Mult [EBinop Sub [EVal one,b],e2]
               ]
    
  -- NOTE: when compiling assignments, the naive thing to do is
  -- to introduce a new var, e2_out, bound to result of e2 and
  -- then ensure that e2_out == x. We optimize by passing x to
  -- compilation of e2 directly.
  EAssert e1 e2 ->
    do { let x = var_of_exp e1
       ; cs_of_exp x e2
       }

  ESeq le -> go le 
    where go []   = fail_with $ ErrMsg "internal error: empty ESeq"
          go [e1] = cs_of_exp out e1
          go (e1 : le')  
            = do { e1_out <- fresh_var
                 ; cs_of_exp e1_out e1
                 ; go le'
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
        (_,cs_simpl) = do_simplify False Map.empty cs
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

