{-# LANGUAGE GADTs
           , DataKinds
           , KindSignatures
           , RankNTypes
           , DeriveDataTypeable
           , AutoDeriveTypeable
           , TypeFamilies
           , UndecidableInstances
           , FlexibleContexts
           , ScopedTypeVariables
  #-}

module TExpr
  ( Val(..)    
  , TExp(..)
  , TFunct(..)
  , Ty(..)
  , Rep
  , TOp(..)
  , TVar(..)
  , boolean_vars_of_texp
  , var_of_texp
  , te_seq
  , last_seq
  , exp_of_texp
  ) where

import Data.Typeable

import Common
import Errors
import Field
import Expr

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
  TEAssert :: Typeable ty => TExp ty a -> TExp ty a -> TExp TUnit a
  TESeq    :: Typeable ty1 => TExp ty1 a -> TExp ty2 a -> TExp ty2 a
  TEBot    :: Typeable ty => TExp ty a

exp_of_val :: Field a => Val ty a -> Exp a
exp_of_val v = case v of
  VField c -> EVal c
  VTrue -> EVal one
  VFalse -> EVal zero
  VUnit -> EUnit

instance ( Field a
         , Eq a
         )
      => Eq (Val ty a) where
  v1 == v2 = exp_of_val v1 == exp_of_val v2

exp_of_texp :: Field a => TExp ty a -> Exp a
exp_of_texp te = case te of
  TEVar (TVar x) -> EVar x
  TEVal v -> exp_of_val v
  TEBinop (TOp op) te1 te2 ->
    exp_binop op (exp_of_texp te1) (exp_of_texp te2)
  TEIf te1 te2 te3 ->
    EIf (exp_of_texp te1) (exp_of_texp te2) (exp_of_texp te3)
  TEAssert te1 te2 ->
    EAssert (exp_of_texp te1) (exp_of_texp te2)
  TESeq te1 te2 -> exp_seq (exp_of_texp te1) (exp_of_texp te2)
  TEBot -> EUnit

instance ( Field a
         , Eq a
         )
      => Eq (TExp ty a) where
  te1 == te2 = exp_of_texp te1 == exp_of_texp te2

-- | Smart constructor for 'TESeq'.  Simplify 'TESeq te1 te2' to 'te2'
-- whenever the normal form of 'te1' (with seq's reassociated right)
-- is *not* equal 'TEAssert _ _'.
te_seq :: Typeable ty1 => TExp ty1 a -> TExp ty2 a -> TExp ty2 a
te_seq te1 te2 = case (te1,te2) of
  (TEAssert _ _,_) -> TESeq te1 te2
  (TESeq tx ty,_) -> te_seq tx (te_seq ty te2)
  (_,_) -> te2
  
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
        go vars (TEAssert e1 e2) = go (go vars e1) e2
        go vars (TESeq e1 e2) = go (go vars e1) e2
        go vars TEBot = vars

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
  show (TEAssert e1 e2) = show e1 ++ " := " ++ show e2
  show (TESeq e1 e2) = show e1 ++ "; " ++ show e2
  show TEBot = "bot"

