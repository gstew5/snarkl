{-# LANGUAGE GADTs,FlexibleInstances,DataKinds,KindSignatures,RankNTypes #-}

module Source
  ( Val(..)    
  , TExp(..)
  , Ty(..)
  , TOp(..)
  , TVar(..)
  , var_of_texp
  , last_seq
  ) where

import Common
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Ty =
    TField
  | TBool
  | TRef Ty  
  | TUnit

data TVar :: Ty -> * where
  TVar :: forall ty. Var -> TVar ty

instance Eq (TVar ty) where
  TVar x==TVar y = x==y

instance Show (TVar ty) where
  show (TVar x) = show x

data TOp :: Ty -> * where
  TOp :: forall ty. Op -> TOp ty
  deriving Eq  

data Val :: Ty -> * -> * where
    VField :: Field a => a -> Val TField a
    VTrue  :: Val TBool a
    VFalse :: Val TBool a
    VUnit  :: Val TUnit a

data TExp :: Ty -> * -> * where
  TEVar    :: TVar ty -> TExp ty a
  TEVal    :: Val ty a -> TExp ty a
  TEBinop  :: TOp ty -> TExp ty a -> TExp ty a -> TExp ty a
  TEIf     :: TExp TBool a -> TExp ty a -> TExp ty a -> TExp ty a
  TEAssign :: TExp (TRef ty) a -> TExp ty a -> TExp TUnit a
  TESeq    :: TExp ty1 a -> TExp ty2 a -> TExp ty2 a

var_of_texp :: Show a => TExp ty a -> Var
var_of_texp te = case last_seq te of
  TEVar (TVar x) -> x
  _ -> error $ "var_of_texp: expected variable: " ++ show te

last_seq :: TExp ty a -> TExp ty a
last_seq te = case te of
  TESeq _ te2 -> last_seq te2
  _ -> te

instance Show (TOp ty) where
  show (TOp op) = show op

instance Show a => Show (Val ty a) where
  show (VField c) = show c
  show VTrue = "true"
  show VFalse = "false"  
  show VUnit = "()"

instance Show a => Show (TExp ty a) where
  show (TEVar x) = "var " ++ show x
  show (TEVal c) = show c
  show (TEBinop op e1 e2) = show e1 ++ show op ++ show e2
  show (TEIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (TEAssign e1 e2) = show e1 ++ " := " ++ show e2
  show (TESeq e1 e2) = show e1 ++ "; " ++ show e2

