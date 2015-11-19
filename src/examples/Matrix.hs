{-# LANGUAGE RebindableSyntax,DataKinds #-}

module Matrix where

import Prelude hiding 
  ( (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , (&&)        
  , not
  , return
  , fromRational
  , negate
  )



import SyntaxMonad
import Syntax
import TExpr
import Toplevel

type Matrix = TExp ('TArr ('TArr 'TField))

new_matrix n m = arr2 n m

new_rowvec n = arr n

new_colvec n = arr n

input_matrix n m = input_arr2 n m

input_rowvec n = input_arr n

input_colvec n = input_arr n

type FixedMatrix = Int -> Int -> Rational

-- v0 + v1 + .. + v(n-1)
sum_vec n v = do
  iterM (dec n) (\i acc -> do
    a <- get (v,i)
    return $ a + acc) 0.0

-- Pinocchio's "Fixed Matrix" microbenchmark [p9]
matrix_colvec_mult fm n = do
  v  <- input_colvec n
  v' <- new_colvec n

  -- multiply
  forall [0..dec n] (\i -> do
    res <- iterM (dec n) (\j acc -> do
             a <- get (v,j)
             return $ (fm i j)*a + acc) 0.0
    set (v',i) res)

  -- return an output that's dependent on the entire vector v'
  sum_vec n v'

test1 n = matrix_colvec_mult (\_ _ -> 7.0) n

interp1 n = comp_interp (test1 n) (map fromIntegral [0..dec n])

