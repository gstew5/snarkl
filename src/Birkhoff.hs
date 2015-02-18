{-# LANGUAGE GADTs, DataKinds #-}

module Birkhoff where

import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import Common
import Field
import Lang
import Simplify
import Compile

data Nat = Z | S Nat
  deriving (Show,Eq)

var_of_nat :: Nat -> Var
var_of_nat Z = 0
var_of_nat (S n) = 1 + var_of_nat n

nat_of_var :: Var -> Nat
nat_of_var x
  | x == 0
  = Z    

  | x > 0
  = S (nat_of_var $ x-1)

  | otherwise
  = error $ "in nat_of_var, variable " ++ show x ++ " is negative"

data Tm a where
  TmConst :: a -> Tm a
  TmVar :: Nat -> Tm a
  deriving (Show,Eq)

exp_of_tm :: Field a => Tm a -> Exp a
exp_of_tm tm = case tm of
  TmConst c -> EVal c
  TmVar n -> EVar $ var_of_nat n

data Prop a where
  PropEq :: Tm a -> Tm a -> Prop a
  deriving (Show,Eq)
  
data Pf a where
  Eq_refl  :: Pf (PropEq t t)
  Eq_sym   :: Pf (PropEq s t) -> Pf (PropEq t s)
  Eq_trans :: Pf (PropEq s t) -> Pf (PropEq t u) -> Pf (PropEq s u)

compile_spec :: Field a
             => Int -- | A bound on supported proof-tree depth
             -> Var -- | The output variable
             -> Prop a -- | The spec. 
             -> State (CEnv a ) () -- | Encoded as a constraint set
compile_spec bound out p
  = if bound == 0 then return ()
    else case p of
      PropEq s t -> 
        do { refl_out  <- fresh_var
           ; sym_out   <- fresh_var
           ; trans_out <- fresh_var
                          
           ; compile_refl refl_out s t 
           ; compile_sym bound sym_out s t
           ; compile_trans bound trans_out s t
             
           ; let e = EBinop XOr (EVar refl_out)
                                (EBinop XOr (EVar sym_out)
                                            (EVar trans_out))
           ; cs_of_exp out e
           }

compile_refl :: Field a => Var -> Tm a -> Tm a -> State (CEnv a) ()
compile_refl out s t
  = do { choose_refl <- fresh_var
       ; let c = EBinop Eq (exp_of_tm s) (exp_of_tm t)
       ; let e = EBinop And (EVar choose_refl) c
       ; cs_of_exp out e
       }

compile_sym :: Field a => Int -> Var -> Tm a -> Tm a -> State (CEnv a) ()
compile_sym bound out s t
  = do { choose_sym <- fresh_var
       ; eq_ts      <- fresh_var
       ; compile_spec (bound-1) eq_ts (PropEq t s)
       ; let e = EBinop And (EVar choose_sym) (EVar eq_ts)
       ; cs_of_exp out e
       }

compile_trans :: Field a => Int -> Var -> Tm a -> Tm a -> State (CEnv a) ()
compile_trans bound out s t
  = do { choose_trans <- fresh_var
       ; choose_u     <- fresh_var
       ; eq_su        <- fresh_var
       ; eq_ut        <- fresh_var                         
       ; compile_spec (bound-1) eq_su (PropEq s (TmVar $ nat_of_var choose_u))
       ; compile_spec (bound-1) eq_ut (PropEq (TmVar $ nat_of_var choose_u) t)
       ; let e = EBinop And (EVar choose_trans)
                            (EBinop And (EVar eq_su) (EVar eq_ut))
       ; cs_of_exp out e
       }

compile_prop bound p
  = let out_var = 0
        comp = compile_spec bound out_var p >> get_constraints
        (cs,_) = runState comp (CEnv Set.empty $ out_var + 1)
        pinned_vars = [out_var]
        (_,cs') = do_simplify pinned_vars Map.empty cs
    in cs'

prop1 :: Prop Rational 
prop1 = PropEq (TmConst 1.0) (TmConst 1.0)
