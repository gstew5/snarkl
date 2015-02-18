{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Lang 
  ( Op(..)
  , is_boolean
  , Exp(..)
  , exp_seq
  , is_pure
  , var_of_exp
  ) where

import Common
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Op = Add | Sub | Mult | Div
        | And | Or | XOr | Eq

instance Show Op where
  show Add  = "+"
  show Sub  = "-"
  show Mult = "*"
  show Div  = "-*"
  show And  = "&&"
  show Or   = "||"  
  show XOr  = "xor"
  show Eq   = "=="  

is_boolean :: Op -> Bool
is_boolean b = case b of
  Add -> False
  Sub -> False
  Mult -> False
  Div -> False
  And -> True
  Or -> True  
  XOr -> True
  Eq -> True  

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
      EBinop _ e1 e2 -> is_pure e1 && is_pure e2
      EIf b e1 e2 -> is_pure b && is_pure e1 && is_pure e2
      EAssign _ _ -> False
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
