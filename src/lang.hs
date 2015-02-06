{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Lang 
  ( Exp(..)
  , fresh_var_of_exp 
  ) where

import Common
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Exp a where
  EVar   :: Var -> Exp a
  EVal   :: Field a => a -> Exp a
  EBinop :: Op -> Exp a -> Exp a -> Exp a
  EIf    :: Exp a -> Exp a -> Exp a -> Exp a
  ELet   :: Var -> Exp a -> Exp a -> Exp a
  --EApp  :: Var -> [Exp a] -> Exp a

max_var_of_exp :: Exp a -> Var
max_var_of_exp e = g (-1) e
  where g y e = case e of
          EVar x -> max x y
          EVal c -> y
          EBinop op e1 e2 -> max (g y e1) (g y e2)
          EIf b e1 e2 -> max (g y b) $ max (g y e1) (g y e2)
          ELet x e1 e2 -> max x $ max (g y e1) (g y e2)

fresh_var_of_exp :: Exp a -> Var
fresh_var_of_exp = (+1) . max_var_of_exp

