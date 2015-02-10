module Common where

type Var = Int

data Term a =
    TConst a
  | TVar Bool Var
  deriving (Show,Eq,Ord)

var_of_term :: Term a -> Maybe Var
var_of_term a = case a of
  (TConst _) -> Nothing  
  (TVar _ x) -> Just x


