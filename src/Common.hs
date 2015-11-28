module Common where

import qualified Data.IntMap.Lazy as Map

type Var = Int

type Assgn a = Map.IntMap a

data UnOp = ZEq
  deriving Eq

instance Show UnOp where 
  show ZEq = "(== 0)"

data Op = Add | Sub | Mult | Div
        | And | Or | XOr | Eq | BEq
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
  show BEq  = "=b="  

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
  BEq -> True  

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
  BEq -> True      

data PragmaKind =
    Int32_to_Arr
  | Arr_to_Int32
  deriving Show
