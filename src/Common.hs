module Common where

type Var = Int

data Atom = Pos Var | Neg Var
  deriving (Show,Eq)

var_of_atom :: Atom -> Var
var_of_atom a = case a of
  Pos x -> x
  Neg x -> x

neg_atom :: Atom -> Atom
neg_atom (Pos x) = Neg x
neg_atom (Neg x) = Pos x

is_pos :: Atom -> Bool
is_pos (Pos _) = True
is_pos (Neg _) = False


