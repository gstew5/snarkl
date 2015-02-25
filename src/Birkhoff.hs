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
  
data Pf b a where
  Eq_refl  :: Pf b (PropEq t t)
  Eq_sym   :: Pf b (PropEq s t) -> Pf b (PropEq t s)
  Eq_trans :: b
           -> Pf b (PropEq s t)
           -> Pf b (PropEq t u)
           -> Pf b (PropEq s u)

data VarTree =
    VarLeaf
  | VarNode (Var,Var,Var,Var) VarTree VarTree VarTree
    deriving Show

wit_of_proof :: Field b => VarTree -> Pf b a -> Map.Map Var b
wit_of_proof t pf
  = case t of
      VarLeaf -> error "branch-variable tree bottomed out"
      VarNode (choose_refl_var,choose_sym_var,choose_trans_var,trans_u_var)
              sym_vars trans_vars_left trans_vars_right ->
        case pf of
          Eq_refl ->
            Map.fromList [ (choose_refl_var,one)
                         , (choose_sym_var,zero)
                         , (choose_trans_var,zero)
                         ]
          Eq_sym pf' ->
            Map.fromList [ (choose_refl_var,zero)
                         , (choose_sym_var,one)
                         , (choose_trans_var,zero)
                         ]
            `Map.union` wit_of_proof sym_vars pf'
          Eq_trans t pf1 pf2 ->
            Map.fromList [ (choose_refl_var,zero)
                         , (choose_sym_var,zero)
                         , (choose_trans_var,one)
                         , (trans_u_var,t)
                         ]
            `Map.union` wit_of_proof trans_vars_left pf1
            `Map.union` wit_of_proof trans_vars_right pf2

-- 44 + 3*f(bound-1)
compile_spec :: Field a
             => Int -- | A bound on supported proof-tree depth
             -> Var -- | The output variable
             -> Prop a -- | The spec. 
             -> State (CEnv a) VarTree -- | Encoded as a constraint set
compile_spec bound out p
  = if bound == 0 then return VarLeaf
    else case p of
      PropEq s t -> 
        do { refl_out  <- fresh_var 
           ; sym_out   <- fresh_var 
           ; trans_out <- fresh_var 

           ; choose_refl  <- fresh_var
           ; choose_sym   <- fresh_var
           ; choose_trans <- fresh_var
           ; choose_u     <- fresh_var
                          
           ; compile_refl choose_refl refl_out s t
           ; sym_vars <- compile_sym bound choose_sym sym_out s t 
           ; (trans_vars_left,trans_vars_right)
               <- compile_trans bound choose_trans choose_u trans_out s t
             
           ; let e = EBinop XOr [EVar refl_out
                                ,EBinop XOr [EVar sym_out
                                            ,EVar trans_out]]
           ; cs_of_exp out e
           ; return $ VarNode (choose_refl,choose_sym,choose_trans,choose_u)
                              sym_vars trans_vars_left trans_vars_right 
           }

-- | fresh_var += 13
compile_refl :: Field a => Var -> Var -> Tm a -> Tm a -> State (CEnv a) ()
compile_refl choose_refl out s t
  = do { let c = EBinop Eq [exp_of_tm s,exp_of_tm t]
       ; let e = EBinop And [EVar choose_refl,c]
       ; cs_of_exp out e
       }

-- | fresh_var += 6 + f(bound-1)
compile_sym :: Field a => Int -> Var -> Var -> Tm a -> Tm a -> State (CEnv a) VarTree
compile_sym bound choose_sym out s t
  = do { eq_ts      <- fresh_var -- +1
       ; recur_vars <- compile_spec (bound-1) eq_ts (PropEq t s) 
       ; let e = EBinop And [EVar choose_sym,EVar eq_ts]
       ; cs_of_exp out e
       ; return recur_vars
       }

-- | fresh_var += 12 + 2*f(bound-1)
compile_trans :: Field a
              => Int -> Var -> Var -> Var
              -> Tm a -> Tm a -> State (CEnv a) (VarTree,VarTree)
compile_trans bound choose_trans choose_u out s t
  = do { eq_su <- fresh_var 
       ; eq_ut <- fresh_var 
       ; recur_left  <- compile_spec (bound-1) eq_su (PropEq s (TmVar $ nat_of_var choose_u)) 
       ; recur_right <- compile_spec (bound-1) eq_ut (PropEq (TmVar $ nat_of_var choose_u) t) 
       ; let e = EBinop And [EVar choose_trans
                            ,EBinop And [EVar eq_su,EVar eq_ut]] 
       ; cs_of_exp out e
       ; return (recur_left,recur_right)
       }

compile_prop bound p
  = let out_var = 0
        comp = do { vtree <- compile_spec bound out_var p
                  ; cs <- get_constraints
                  ; return (vtree,cs)
                  }
        ((vtree,cs),_) = runState comp (CEnv Set.empty $ out_var + 1)
        pinned_vars = [out_var]
--       (_,cs') = do_simplify pinned_vars Map.empty cs
        f = solve_constraints pinned_vars cs
    in (f,vtree,cs)

prop1 :: Prop Rational 
prop1 = PropEq (TmConst 0.0) (TmConst 0.0)

pf1 :: Pf Rational ('PropEq u u)
pf1 = Eq_trans 0.0 (Eq_sym Eq_refl) Eq_refl

test bound p pf
  = let (f,vtree,cs) = compile_prop bound p
        wit = wit_of_proof vtree pf
    in f wit

test1 = Map.lookup 0 $ test 4 prop1 pf1       

