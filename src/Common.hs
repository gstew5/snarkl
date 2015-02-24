module Common where

import qualified Data.Map.Strict as Map

type Var = Int

type Assgn a = Map.Map Var a
