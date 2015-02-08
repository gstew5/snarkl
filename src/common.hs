module Common where

type Var = Int

data Op = Add | Sub | Mult | Div
        | And | Or | XOr 

instance Show Op where
  show Add  = "+"
  show Sub  = "-"
  show Mult = "*"
  show Div  = "-*"
  show And  = "&&"
  show Or   = "||"  
  show XOr  = "xor"

is_boolean :: Op -> Bool
is_boolean b = case b of
  Add -> False
  Sub -> False
  Mult -> False
  Div -> False
  And -> True
  Or -> True  
  XOr -> True
