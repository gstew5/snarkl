{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module Main where

import qualified Prelude as P

import Control.Monad ( mapM_ )

import Tests
import Toplevel

main
  = (P.>>) (mapM_ test bool_tests)
           (mapM_ test tests)

