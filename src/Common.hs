module Common where

type Var = Int

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

