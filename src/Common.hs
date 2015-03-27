module Common where

import qualified Data.IntMap.Lazy as Map

type Var = Int

type Assgn a = Map.IntMap a

-- 'Eq' is general equality. 'BEq' is specialized to booleans, 
-- and is compiled more efficiently.
data Op = Add | Sub | Mult | Div | Eq 
        | And | Or | XOr | BEq
  deriving Eq                           

instance Show Op where
  show Add  = "+"
  show Sub  = "-"
  show Mult = "*"
  show Div  = "-*"
  show Eq   = "=="
  show And  = "&&"
  show Or   = "||"  
  show XOr  = "xor"
  show BEq   = "=b="  

is_boolean :: Op -> Bool
is_boolean op = case op of
  Add -> False
  Sub -> False
  Mult -> False
  Div -> False
  Eq  -> True
  And -> True
  Or -> True  
  XOr -> True
  BEq -> True  

is_assoc :: Op -> Bool
is_assoc op = case op of
  Add -> True
  Sub -> False
  Mult -> True
  Div -> False
  Eq  -> True
  And -> True
  Or -> True  
  XOr -> True
  BEq -> True

      
