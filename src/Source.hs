{-# LANGUAGE GADTs
           , DataKinds
           , KindSignatures
           , RankNTypes
           , DeriveDataTypeable
           , AutoDeriveTypeable
           , TypeFamilies
           , UndecidableInstances 
  #-}

module Source
  ( Val(..)    
  , TExp(..)
  , TFunct(..)
  , Ty(..)
  , Rep
  , TOp(..)
  , TVar(..)
  , boolean_vars_of_texp
  , var_of_texp
  , last_seq
  ) where

import Data.Typeable

import Common
import Errors
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data TFunct where
  TFConst :: Ty -> TFunct
  TFId :: TFunct
  TFProd :: TFunct -> TFunct -> TFunct
  TFSum :: TFunct -> TFunct -> TFunct
  TFComp :: TFunct -> TFunct -> TFunct
  deriving Typeable

data Ty where
  TField:: Ty
  TBool :: Ty
  TArr  :: Ty -> Ty
  TProd :: Ty -> Ty -> Ty  
  TSum  :: Ty -> Ty -> Ty
  TMu   :: TFunct -> Ty
  TUnit :: Ty
  deriving Typeable

type family Rep (f :: TFunct) (x :: Ty) :: Ty
type instance Rep (TFConst ty) x = ty
type instance Rep TFId x = x
type instance Rep (TFProd f g) x = TProd (Rep f x) (Rep g x)
type instance Rep (TFSum f g) x = TSum (Rep f x) (Rep g x)
type instance Rep (TFComp f g) x = Rep f (Rep g x)

newtype TVar (ty :: Ty) = TVar Var
  
var_is_boolean :: Typeable ty => TVar ty -> Bool
var_is_boolean x
  = typeOf x == typeOf (undefined :: TVar 'TBool)

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
  TEUpdate :: Typeable ty => TExp ty a -> TExp ty a -> TExp TUnit a
  TESeq    :: Typeable ty1 => TExp ty1 a -> TExp ty2 a -> TExp ty2 a

boolean_vars_of_texp :: Typeable ty => TExp ty a -> [Var]
boolean_vars_of_texp = go []
  where go :: Typeable ty => [Var] -> TExp ty a -> [Var]
        go vars (TEVar t@(TVar x))
          = if var_is_boolean t then x : vars
            else vars
        go vars (TEVal _) = vars
        go vars (TEBinop _ e1 e2) = go (go vars e1) e2
        go vars (TEIf e1 e2 e3)
          = go (go (go vars e1) e2) e3
        go vars (TEUpdate e1 e2) = go (go vars e1) e2
        go vars (TESeq e1 e2) = go (go vars e1) e2

var_of_texp :: Show a => TExp ty a -> Var
var_of_texp te = case last_seq te of
  TEVar (TVar x) -> x
  _ -> fail_with $ ErrMsg ("var_of_texp: expected array or var: "
                           ++ show te)

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
  show (TEUpdate e1 e2) = show e1 ++ " := " ++ show e2
  show (TESeq e1 e2) = show e1 ++ "; " ++ show e2

