module Common where

import qualified Data.Map.Strict as Map

type Var = Int

type Assgn a = Map.Map Var a

data Term a =
    TConst a
  | TVar Bool Var
  deriving (Show,Eq,Ord)

var_of_term :: Term a -> Maybe Var
var_of_term t = case t of
  TConst _ -> Nothing  
  TVar _ x -> Just x

is_const :: Term a -> Bool
is_const t = case t of
  TConst _ -> True
  TVar _ _ -> False

