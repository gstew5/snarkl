module Common where

type Var = Int

data Op = Add | Sub | Mult | Inv

instance Show Op where
  show Add  = "+"
  show Sub  = "-"
  show Mult = "*"
  show Inv  = "-*"      

