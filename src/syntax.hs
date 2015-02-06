{-# LANGUAGE RebindableSyntax #-}

module Syntax where

import Prelude hiding 
  ( ifThenElse 
  , (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , return
  , fromRational
  )
import qualified Prelude as P  

import Common
import R1CS
import Lang
import Compile

ifThenElse b e1 e2 = EIf b e1 e2

data State s a = State (s -> (a,s))

runState :: State s a -> s -> (a,s)
runState mf s = case mf of
  State f -> f s

var :: State Int (Exp Rational)
var = State (\s -> (EVar s,(P.+) s 1))

(>>=) :: State s a -> (a -> State s b) -> State s b
(>>=) mf g
  = State (\s -> let (e,s') = runState mf s
                 in runState (g e) s')

return :: a -> State s a
return e = State (\s -> (e,s))

ret = return

(+) :: Exp Rational -> Exp Rational -> Exp Rational
(+) e1 e2 = EBinop Add e1 e2

(-) :: Exp Rational -> Exp Rational -> Exp Rational
(-) e1 e2 = EBinop Sub e1 e2

(*) :: Exp Rational -> Exp Rational -> Exp Rational
(*) e1 e2 = EBinop Mult e1 e2

(/) :: Exp Rational -> Exp Rational -> Exp Rational
(/) e1 e2 = EBinop Inv e1 e2

fromRational r = EVal (r :: Rational)

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int }
  deriving Show  

check :: State Int (Exp Rational) -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf 0
        (f,r1cs) = compile_exp e 
        nw = num_vars r1cs
        ng = num_constraints r1cs
    in Result (sat_r1cs (f inputs) r1cs) nw ng
