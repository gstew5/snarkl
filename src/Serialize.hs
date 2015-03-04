module Serialize where

import qualified Data.IntMap.Lazy as Map
import Data.Ratio

import Poly
import R1CS

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

flatten_rat :: Rational -> Integer
flatten_rat r
  = let a = numerator r
        b = denominator r
    in case mod_inv b field_p of
         Nothing -> error $ "expected " ++ show b ++ " to be invertible"
         Just b_inv -> (a * b_inv) `mod` field_p
    
serialize_poly :: Poly Rational -> String
serialize_poly p = case p of
  Poly m -> 
    let size = Map.size m
        binds = Map.toList $ Map.mapKeys (+ 1) m
        string_binds = map (\(k,v) -> show k ++ "\n"
                                      ++ show (flatten_rat v) ++ "\n")
                       binds
    in show size ++ "\n"
       ++ concat string_binds

serialize_r1c :: R1C Rational -> String
serialize_r1c cons = case cons of
  R1C (a, b, c) -> concat $ map serialize_poly [a, b, c]

serialize_r1cs :: R1CS Rational -> String
serialize_r1cs cs
  = let r1c_strings :: String
        r1c_strings = concat (map serialize_r1c (r1cs_clauses cs))
    in show (length $ r1cs_in_vars cs) ++ "\n"
       ++ show (r1cs_num_vars cs) ++ "\n"
       ++ show (length $ r1cs_clauses cs) ++ "\n"
       ++ r1c_strings
