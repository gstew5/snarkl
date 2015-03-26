{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Field where

import Data.Ratio

import Errors

class (Show a,Eq a,Ord a) => Field a where
  zero :: a
  one  :: a
  add  :: a -> a -> a
  mult :: a -> a -> a
  neg  :: a -> a
  inv  :: a -> Maybe a

instance Field Rational where 
  zero = 0
  one  = 1
  add  = (+)
  mult = (*)
  neg  = \n -> -n
  inv  = \n -> if n == 0 then Nothing else Just $ denominator n % numerator n

field_p :: Integer
field_p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Citation: http://rosettacode.org/wiki/Modular_inverse#Haskell
-- License: http://www.gnu.org/licenses/fdl-1.2.html
-- Extended Euclidean algorithm.  Given non-negative a and b, return x, y and g
-- such that ax + by = g, where g = gcd(a,b).  Note that x or y may be negative. 
gcd_ext :: Integer -> Integer -> (Integer,Integer,Integer)
gcd_ext a 0 = (1, 0, a)
gcd_ext a b
  = let (q, r) = a `quotRem` b
        (s, t, g) = gcd_ext b r
    in (t, s - q * t, g)
 
-- Given a and m, return Just x such that ax = 1 mod m.  If there is no such x
-- return Nothing.
mod_inv :: Integer -> Integer -> Maybe Integer
mod_inv a m
  = let (i, _, g) = gcd_ext a m
    in if g == 1 then Just (mkPos i) else Nothing
  where mkPos x = if x < 0 then x + m else x
-- /End cited code/

newtype IntP = IntP { unIntP :: Integer }
  deriving ( Ord 
           , Eq
           )

instance Show IntP where
  show (IntP i) = show i

int_p :: Integer -> IntP
int_p i 
  = if i >= field_p then 
      fail_with $ ErrMsg (show i ++ " exceeds field size")
    else IntP $ i `mod` field_p

-- | The finite field of integers mod 'field_p'.
instance Field IntP where
  zero = int_p 0
  one  = int_p 1
  add  = \n m -> int_p $ (unIntP n + unIntP m) `mod` field_p
  mult = \n m -> int_p $ (unIntP n * unIntP m) `mod` field_p
  neg  = \n -> int_p $ -(unIntP n) `mod` field_p
  inv  = \n -> case mod_inv (unIntP n) field_p of
                 Nothing -> Nothing
                 Just n' -> Just $ int_p n'

