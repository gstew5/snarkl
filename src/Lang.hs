{-# LANGUAGE GADTs,FlexibleInstances,DataKinds,KindSignatures,TypeFamilies
,ExistentialQuantification #-}

module Lang 
  ( Op(..)
  , is_boolean
  , Val(..)    
  , TExp(..)
  , Ty(..)
  , TOp(..)
  , TVar(..)    
  , Exp(..)    
  , exp_binop
  , exp_seq
  , is_pure
  , var_of_exp
  , var_of_texp
  , exp_of_texp
  ) where

import Common
import Field

----------------------------------------------------------------
--                 Source Expression Language                 --
----------------------------------------------------------------

data Op = Add | Sub | Mult | Div
        | And | Or | XOr | Eq
  deriving Eq                           

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
is_boolean op = case op of
  Add -> False
  Sub -> False
  Mult -> False
  Div -> False
  And -> True
  Or -> True  
  XOr -> True
  Eq -> True  

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
  deriving (Show,Eq)  

data Val :: Ty -> * -> * where
    VField :: Field a => a -> Val TField a
    VTrue :: Val TBool a
    VFalse :: Val TBool a
    VUnit :: Val TUnit a

data TExp :: Ty -> * -> * where
  TEVar    :: TVar ty -> TExp ty a
  TEVal    :: Val ty a -> TExp ty a
  TEBinop  :: TOp ty -> TExp ty a -> TExp ty a -> TExp ty a
  TEIf     :: TExp TBool a -> TExp ty a -> TExp ty a -> TExp ty a
  TEAssign :: TExp (TRef ty) a -> TExp ty a -> TExp TUnit a
  TESeq    :: TExp ty1 a -> TExp ty2 a -> TExp ty2 a

var_of_texp :: TExp ty a -> Var
var_of_texp te = case te of
  TEVar (TVar x) -> x
  _ -> error "var_of_exp: expected variable"

data Exp :: * -> * where
  EVar    :: Var -> Exp a
  EVal    :: Field a => a -> Exp a
  EBinop  :: Op -> [Exp a] -> Exp a
  EIf     :: Exp a -> Exp a -> Exp a -> Exp a
  EAssign :: Exp a -> Exp a -> Exp a
  ESeq    :: [Exp a] -> Exp a
  EUnit   :: Exp a

var_of_exp :: Exp a -> Var
var_of_exp e = case e of
  EVar x -> x
  _ -> error "var_of_exp: expected variable"

exp_of_val :: Field a => Val ty a -> Exp a
exp_of_val v = case v of
  VField c -> EVal c
  VTrue -> EVal one
  VFalse -> EVal zero
  VUnit -> EUnit

exp_of_texp :: Field a => TExp ty a -> Exp a
exp_of_texp te = case te of
  TEVar (TVar x) -> EVar x
  TEVal v -> exp_of_val v
  TEBinop (TOp op) te1 te2 ->
    exp_binop op (exp_of_texp te1) (exp_of_texp te2)
  TEIf te1 te2 te3 ->
    EIf (exp_of_texp te1) (exp_of_texp te2) (exp_of_texp te3)
  TEAssign te1 te2 ->
    EAssign (exp_of_texp te1) (exp_of_texp te2)
  TESeq te1 te2 -> exp_seq (exp_of_texp te1) (exp_of_texp te2)

is_assoc :: Op -> Bool
is_assoc op = case op of
  Add -> True
  Sub -> False
  Mult -> True
  Div -> False
  And -> True
  Or -> True  
  XOr -> True
  Eq -> True  

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
  where go l = let le = last l -- safe, by smart constructor invariant
                   linit = init l
               in ESeq $ filter (not . is_pure) linit ++ [le]

is_pure :: Exp a -> Bool
is_pure e
  = case e of
      EVar _ -> True
      EVal _ -> True
      EBinop _ es -> all is_pure es
      EIf b e1 e2 -> is_pure b && is_pure e1 && is_pure e2
      EAssign _ _ -> False
      ESeq es -> all is_pure es
      EUnit -> True

instance Show a => Show (Exp a) where
  show (EVar x) = "var " ++ show x
  show (EVal c) = show c
  show (EBinop op es) = go es
    where go [] = ""
          go (e1 : es') = show e1 ++ show op ++ go es'
  show (EIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (EAssign e1 e2) = show e1 ++ " := " ++ show e2
  show (ESeq es) = go es
    where go [] = ""
          go (e1 : es') = show e1 ++ "; " ++ go es'
  show EUnit = "()"


