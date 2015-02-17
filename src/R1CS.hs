{-# LANGUAGE GADTs #-}

module R1CS
  ( Field
  , Poly
  , Var
  , R1C(..)
  , R1CS(..)
  , sat_r1cs
  , num_vars
  , num_constraints
  ) where

import Data.List

import Common
import Field
import Poly

----------------------------------------------------------------
--                Rank-1 Constraint Systems                   --
----------------------------------------------------------------

data R1C a where
  R1C :: Field a => (Poly a, Poly a, Poly a) -> R1C a

instance Show a => Show (R1C a) where
  show (R1C (aV,bV,cV)) = show aV ++ "*" ++ show bV ++ "==" ++ show cV

data R1CS a where
  R1CS :: Field a => [R1C a] -> R1CS a

instance Show a => Show (R1CS a) where
  show (R1CS cs) = show cs

num_vars :: R1CS a -> Int
num_vars (R1CS ls) = case ls of
  [] -> 0
  (R1C (Poly aV,_,_) : _) -> length aV - 1

num_constraints :: R1CS a -> Int
num_constraints (R1CS ls) = length ls

-- sat_r1c: Does witness 'w' satisfy constraint 'c'?
sat_r1c :: Field a => [a] -> R1C a -> Bool
sat_r1c w c
  | R1C (aV, bV, cV) <- c
  = inner aV w `mult` inner bV w == inner cV w
    where inner :: Field a => Poly a -> [a] -> a
          inner p w'
            | Poly v <- p
            , length v == 1 + length w'
            = foldl' add zero $ map (uncurry mult) (zip v (one : w'))

            | Poly v <- p
            , otherwise
            = error $ "witness has wrong length: got "
                      ++ show (length w')
                      ++ ", expected " ++ show (length v - 1)

-- sat_r1cs: Does witness 'w' satisfy constraint set 'cs'?
sat_r1cs :: Field a => [a] -> R1CS a -> Bool
sat_r1cs w cs
  | R1CS cs' <- cs
  = g cs'
    where g [] = True
          g (c : cs'') =
            if sat_r1c w c then g cs''
            else error $ "sat_r1cs: witness failed to satisfy constraint: "
                         ++ show w ++ " " ++ show c


  







