{-# LANGUAGE GADTs #-}

module R1CS
  ( Field
  , Poly
  , Var
  , R1C(..)
  , R1CS(..)
  , sat_r1cs
  ) where

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

-- sat_r1c: Does witness 'w' satisfy constraint 'c'?
sat_r1c :: Field a => [a] -> R1C a -> Bool
sat_r1c w c
  | R1C (aV, bV, cV) <- c
  = inner aV w `mult` inner bV w == inner cV w
    where inner :: Field a => Poly a -> [a] -> a
          inner p w
            | Poly v <- p
            , length v == 1 + length w
            = foldl add zero $ map (uncurry mult) (zip v (one : w))

            | otherwise
            = error "witness has wrong length"

-- sat_r1cs: Does witness 'w' satisfy constraint set 'cs'?
sat_r1cs :: Field a => [a] -> R1CS a -> Bool
sat_r1cs w cs
  | R1CS cs' <- cs
  = all (sat_r1c w) cs'                 

-- x * y = z
cA :: R1CS Rational
cA = R1CS [R1C (Poly [0,1,0,0],Poly [0,0,1,0],Poly [0,0,0,1])]

cA_wit :: [Rational]
cA_wit = [1,2,2]

-- x + y = z
dA :: R1CS Rational
dA = R1CS [R1C (Poly [1,0,0,0],Poly [0,1,1,0],Poly [0,0,0,1])]

dA_wit :: [Rational]
dA_wit = [1,2,3]


  







