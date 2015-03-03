{-# LANGUAGE GADTs,FlexibleInstances,DataKinds,KindSignatures #-}

module Expr
  ( Exp(..)
  , exp_binop
  , exp_seq
  , is_pure
  , var_of_exp
  , simpl_exp
  ) where

import Control.Monad.State

import Common
import Field
import UnionFind
import SimplMonad

data Exp :: * -> * where
  EVar    :: Var -> Exp a
  EVal    :: Field a => a -> Exp a
  EBinop  :: Op -> [Exp a] -> Exp a
  EIf     :: Exp a -> Exp a -> Exp a -> Exp a
  EAssign :: Exp a -> Exp a -> Exp a
  ESeq    :: [Exp a] -> Exp a
  EUnit   :: Exp a

instance Field a => Eq (Exp a) where
  EVar x==EVar y = x==y
  EVal c==EVal d = c==d
  EBinop op es==EBinop op' es' = op==op' && es==es'
  EIf e1 e2 e3==EIf e1' e2' e3' = e1==e1' && e2==e2' && e3==e3'
  EAssign e1 e2==EAssign e1' e2' = e1==e1' && e2==e2'
  ESeq es==ESeq es' = es==es'
  EUnit==EUnit = True
  _==_ = False

var_of_exp :: Show a => Exp a -> Var
var_of_exp e = case e of
  EVar x -> x
  _ -> error $ "var_of_exp: expected variable: " ++ show e

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
      EAssign _ _ -> False
      ESeq es -> all is_pure es
      EUnit -> True

subst_exp :: Field a => Exp a -> State (SEnv a) (Exp a)
subst_exp e = case e of
  EVar x ->
    do { bind <- bind_of_var x
       ; case bind of
           Left x' -> return $ EVar x'
           Right c -> return $ EVal c
       }
  EVal _ -> return $ e
  EBinop op es ->
    do { es' <- mapM subst_exp es
       ; return $ EBinop op es'
       }
  EIf e1 e2 e3 ->
    do { e1' <- subst_exp e1
       ; e2' <- subst_exp e2
       ; e3' <- subst_exp e3
       ; return $ EIf e1' e2' e3'
       }
  EAssign e1 e2 ->
    do { e1' <- subst_exp e1
       ; e2' <- subst_exp e2
       ; return $ EAssign e1' e2'
       }
  ESeq es ->     
    do { es' <- mapM subst_exp es
       ; return $ ESeq es'
       }
  EUnit -> return $ EUnit
    
const_prop :: Field a => Exp a -> State (SEnv a) (Exp a)
const_prop e =
  do { e' <- subst_exp e
     ; case e' of
         EVar _ -> return e'
         EVal _ -> return e'
         EBinop op es ->
           do { es' <- mapM const_prop es
              ; if all is_val es' then
                  return $ EVal (foldr (interp_op op) (unit_of op) $ map get_val es')
                else return $ EBinop op es'
              }
         EIf e1 e2 e3 ->
           do { e1' <- const_prop e1
              ; e2' <- const_prop e2
              ; e3' <- const_prop e3
              ; case e1' of
                  EVal b ->
                    if b == zero then return e3'
                    else if b == one then return e2'
                         else error $ "expected boolean in expression "
                              ++ show (EIf e1' e2' e3')
                  _ -> return $ EIf e1' e2' e3' 
              }
         EAssign (EVar x) (EVal c) ->
           do { bind_var (x,c)
              ; return $ EUnit
              }
         EAssign e1 e2 ->
           do { e1' <- const_prop e1
              ; e2' <- const_prop e2
              ; if (EAssign e1' e2') == e' then return e'
                else const_prop $ EAssign e1' e2' 
              }
         ESeq es ->
           do { es' <- mapM const_prop es
              ; return $ ESeq es'
              }
         EUnit -> return $ EUnit
     }
  where is_val (EVal _) = True
        is_val _ = False

        get_val (EVal c) = c
        get_val e0 = error $ "expected value " ++ show e0

        interp_op op = case op of
          Add -> add
          Sub -> \x y -> add x (neg y)
          Mult -> mult
          Div -> \x y -> mult x (neg y)
          And -> \x y -> if x == one && y == one then one else zero
          Or -> \x y -> if x == one || y == one then one else zero
          XOr -> \x y -> if (x == one && y == zero) || (x == zero && y == one) then one else zero
          Eq -> \x y -> if x == y then one else zero

        unit_of op = case op of
          Add -> zero
          Sub -> zero
          Mult -> one
          Div -> one
          And -> one
          Or -> zero
          XOr -> zero
          Eq -> error "unimplemented"

simpl_exp :: Field a => Exp a -> Exp a
simpl_exp e = fst $ runState (const_prop e) (SEnv new_uf)

instance Show a => Show (Exp a) where
  show (EVar x) = "var " ++ show x
  show (EVal c) = show c
  show (EBinop op es) = "(" ++ go es ++ ")"
    where go [] = ""
          go (e1 : [])  = show e1
          go (e1 : es') = show e1 ++ show op ++ go es'
  show (EIf b e1 e2) 
    = "if " ++ show b ++ " then " ++ show e1 ++ " else " ++ show e2
  show (EAssign e1 e2) = show e1 ++ " := " ++ show e2
  show (ESeq es) = go es
    where go [] = ""
          go (e1 : es') = show e1 ++ "; " ++ go es'
  show EUnit = "()"
