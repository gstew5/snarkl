{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Lang 
  ( Exp(..)
  , exp_seq
  , is_pure
  , var_of_exp
  ) where

import Common
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Exp a where
  EVar    :: Var -> Exp a
  EVal    :: Field a => a -> Exp a
  EBinop  :: Op -> Exp a -> Exp a -> Exp a
  EIf     :: Exp a -> Exp a -> Exp a -> Exp a
  EAssign :: Exp a -> Exp a -> Exp a
  ESeq    :: [Exp a] -> Exp a
  EUnit   :: Exp a

-- |Smart constructor for sequence, ensuring all expressions are
-- flattened to top level.
exp_seq :: Exp a -> Exp a -> Exp a
exp_seq e1 e2
  = case (e1,e2) of
      (ESeq l1,ESeq l2) -> ESeq $ l1++l2
      (ESeq l1,_) -> ESeq $ l1++[e2]
      (_,ESeq l2) -> ESeq $ e1 : l2
      (_,_) -> ESeq [e1,e2]

is_pure :: Exp a -> Bool
is_pure e
  = case e of
      EVar _ -> True
      EVal _ -> True
      EBinop op e1 e2 -> is_pure e1 && is_pure e2
      EIf b e1 e2 -> is_pure b && is_pure e1 && is_pure e2
      EAssign x e -> False
      ESeq le -> all is_pure le
      EUnit -> True

instance Show a => Show (Exp a) where
  show (EVar x) = "var " ++ show x
  show (EVal c) = show c
  show (EBinop op e1 e2) = show e1 ++ show op ++ show e2
  show (EIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (EAssign e1 e2) = show e1 ++ " := " ++ show e2
  show (ESeq le) = g le
    where g [] = ""
          g (e1 : le') = show e1 ++ "; " ++ g le'
  show EUnit = "()"

var_of_exp :: Exp a -> Var
var_of_exp e = case e of
  EVar x -> x
  _ -> error "var_of_exp: expected variable"

max_var_of_exp :: Exp a -> Var
max_var_of_exp e = g (-1) e
  where g y e = case e of
          EVar x -> max x y
          EVal c -> y
          EBinop op e1 e2 -> max (g y e1) (g y e2)
          EIf b e1 e2  -> max (g y b) $ max (g y e1) (g y e2)
          EAssign e1 e2 -> max (g y e1) (g y e2)
          ESeq le -> h y le
          EUnit -> y          
        h y [] = y
        h y (e1 : le') = max (g y e1) (h y le')
        
fresh_var_of_exp :: Exp a -> Var
fresh_var_of_exp = (+1) . max_var_of_exp

