{-# LANGUAGE GADTs
           , KindSignatures
  #-}

module Expr
  ( Exp(..)
  , exp_binop
  , exp_seq
  , is_pure
  , var_of_exp
  , do_const_prop
  ) where

import Common
import Errors
import Field

import Control.Monad.State
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

data Exp :: * -> * where
  EVar    :: Var -> Exp a
  EVal    :: Field a => a -> Exp a
  EUnop   :: UnOp -> Exp a -> Exp a
  EBinop  :: Op -> [Exp a] -> Exp a
  EIf     :: Exp a -> Exp a -> Exp a -> Exp a
  EAssert :: Exp a -> Exp a -> Exp a
  ESeq    :: [Exp a] -> Exp a
  EUnit   :: Exp a

instance Eq a => Eq (Exp a) where
  EVar x == EVar y = x == y
  EVal a == EVal b = a == b
  EUnop op e1 == EUnop op' e1' 
    = op == op' && e1 == e1'
  EBinop op es == EBinop op' es'
    = op == op' && es == es'
  EIf e e1 e2 == EIf e' e1' e2'
    = e == e' && e1 == e1' && e2 == e2'
  EAssert e1 e2 == EAssert e1' e2'
    = e1 == e1' && e2 == e2'
  ESeq es == ESeq es' = es == es'
  EUnit == EUnit = True
  _ == _ = False

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
      (ESeq l1,ESeq l2) -> ESeq (l1 ++ l2)
      (ESeq l1,_) -> ESeq (l1 ++ [e2])
      (_,ESeq l2) -> ESeq (e1 : l2)
      (_,_) -> ESeq [e1, e2]

is_pure :: Exp a -> Bool
is_pure e
  = case e of
      EVar _ -> True
      EVal _ -> True
      EUnop _ e1 -> is_pure e1
      EBinop _ es -> all is_pure es
      EIf b e1 e2 -> is_pure b && is_pure e1 && is_pure e2
      EAssert _ _ -> False
      ESeq es -> all is_pure es
      EUnit -> True

const_prop :: Field a => Exp a -> State (IntMap a) (Exp a)
const_prop e
  = case e of
      EVar x -> lookup_var x
      EVal _ -> return e
      EUnop op e1 ->
        do { e1' <- const_prop e1
           ; return $ EUnop op e1'
           }
      EBinop op es ->
        do { es' <- mapM const_prop es
           ; return $ EBinop op es'
           }
      EIf e1 e2 e3 ->
        do { e1' <- const_prop e1
           ; e2' <- const_prop e2
           ; e3' <- const_prop e3
           ; return $ EIf e1' e2' e3'
           }
      EAssert (EVar x) (EVal c) -> add_bind (x,c)
      EAssert e1 e2 ->
        do { e1' <- const_prop e1
           ; e2' <- const_prop e2
           ; return $ EAssert e1' e2' 
           }
      ESeq es -> 
        do { es' <- mapM const_prop es
           ; return $ ESeq es'
           }
      EUnit -> return EUnit

  where lookup_var :: Field a => Int -> State (IntMap a) (Exp a)
        lookup_var x0
          = gets (\m -> case IntMap.lookup x0 m of
                          Nothing -> EVar x0
                          Just c -> EVal c)
        add_bind :: Field a => (Int,a) -> State (IntMap a) (Exp a)
        add_bind (x0,c0)
          = do { modify (IntMap.insert x0 c0)
               ; return EUnit
               }

do_const_prop :: Field a => Exp a -> Exp a
do_const_prop e = fst $ runState (const_prop e) IntMap.empty

instance Show a => Show (Exp a) where
  show (EVar x) = "var " ++ show x
  show (EVal c) = show c
  show (EUnop op e1) = show op ++ show e1
  show (EBinop op es) = go es
    where go [] = ""
          go (e1 : [])  = show e1
          go (e1 : es') = show e1 ++ show op ++ go es'
  show (EIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (EAssert e1 e2) = show e1 ++ " := " ++ show e2
  show (ESeq es) = "(" ++ go es ++ ")"
    where go [] = ""
          go (e1 : [])  = show e1
          go (e1 : es') = show e1 ++ "; " ++ go es'
  show EUnit = "()"

