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

arr :: Int -> State Int (Exp Rational)
arr 0 = error "array must have size >= 1"
arr 1 = var
arr n = do { x <- var; _ <- arr ((P.-) n 1); ret x }

arr_get :: Exp Rational -> Int -> Exp Rational
arr_get (EVar x) n = EVar $ (P.+) x n
arr_get _ _ = error "expected a variable"

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

exp_of_int :: Int -> Exp Rational
exp_of_int i = EVal (fromIntegral i)

iter :: Int
     -> (Int -> Exp Rational -> Exp Rational)
     -> Exp Rational
     -> Exp Rational
iter 0 f e = f 0 e
iter n f e = f n $ iter ((P.-) n 1) f e

summate :: Int
        -> (Int -> Exp Rational)
        -> Exp Rational
summate n f
  = iter ((P.-) n 1)
    (\i e -> case i == 0 of
        True -> e
        False -> f i + e) (f (0::Int))

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int
         , result :: Rational }
  deriving Show  

check :: State Int (Exp Rational) -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf 0
        (f,r1cs) = compile_exp e 
        nw = num_vars r1cs
        ng = num_constraints r1cs
        wit = f inputs
        out = head $ drop (length inputs) wit 
    in Result (sat_r1cs wit r1cs) nw ng out
