{-# LANGUAGE GADTs,FlexibleInstances,DataKinds,KindSignatures #-}

module Expr
  ( Exp(..)
  , exp_binop
  , exp_seq
  , is_pure
  , var_of_exp
  ) where

import Common
import Errors
import Field

data Exp :: * -> * where
  EVar    :: Var -> Exp a
  EVal    :: Field a => a -> Exp a
  EBinop  :: Op -> [Exp a] -> Exp a
  EIf     :: Exp a -> Exp a -> Exp a -> Exp a
  EUpdate :: Exp a -> Exp a -> Exp a
  ESeq    :: [Exp a] -> Exp a
  EUnit   :: Exp a

var_of_exp :: Show a => Exp a -> Var
var_of_exp e = case e of
  EVar x -> x
  _ -> fail_with $ ErrMsg ("var_of_exp: expected variable: " ++ show e)

-- |Smart constructor for EBinop, ensuring all expressions (involving
-- associative operations) are flattened to top level.
exp_binop :: Op -> Exp a -> Exp a -> Exp a
exp_binop op e1 e2
  = case (e1,e2) of
      (EBinop op1 l1,EBinop op2 l2)
        | op1==op2 && op2==op && is_assoc op
        -> EBinop op (l1++l2)
           
      (EBinop op1 l1,_)
        | op1==op && is_assoc op
        -> EBinop op (l1++[e2])
           
      (_,EBinop op2 l2)
        | op2==op && is_assoc op
        -> EBinop op (e1 : l2)

      (_,_) -> EBinop op [e1,e2]

-- |Smart constructor for sequence, ensuring all expressions are
-- flattened to top level.
exp_seq :: Exp a -> Exp a -> Exp a
exp_seq e1 e2
  = case (e1,e2) of
      (ESeq l1,ESeq l2) -> go (l1++l2)
      (ESeq l1,_) -> go (l1 ++ [e2])
      (_,ESeq l2) -> go (e1 : l2)
      (_,_) -> go [e1,e2]
  where go l = let linit = init l -- safe, by smart constructor invariant
               in ESeq $ filter (not . is_pure) linit ++ [last l]

is_pure :: Exp a -> Bool
is_pure e
  = case e of
      EVar _ -> True
      EVal _ -> True
      EBinop _ es -> all is_pure es
      EIf b e1 e2 -> is_pure b && is_pure e1 && is_pure e2
      EUpdate _ _ -> False
      ESeq es -> all is_pure es
      EUnit -> True


instance Show a => Show (Exp a) where
  show (EVar x) = "var " ++ show x
  show (EVal c) = show c
  show (EBinop op es) = go es
    where go [] = ""
          go (e1 : [])  = show e1
          go (e1 : es') = show e1 ++ show op ++ go es'
  show (EIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (EUpdate e1 e2) = show e1 ++ " := " ++ show e2
  show (ESeq es) = go es
    where go [] = ""
          go (e1 : es') = show e1 ++ "; " ++ go es'
  show EUnit = "()"
