{-# LANGUAGE RebindableSyntax #-}

module Main where

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

import Syntax

g = do { x <- var
       ; y <- var
       ; z <- var
       ; u <- ret (if x + y then y else z)
       ; w <- ret (if x then y else z)
       ; ret $ x + u*z - w }

main = putStrLn $ show $ check g [0,1,1]

