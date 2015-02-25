module Serialize where

import qualified Data.Map.Strict as Map
import Data.Ratio

import Poly
import R1CS

field_p :: Integer
field_p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

gcd_quotients :: Integer -> Integer -> ( Integer  -- s
                                       , Integer) -- t
gcd_quotients a b
  = let (_,ss,ts) = go a b [a `quot` b] [0,1] [1,0] in (head ss,head ts)
  where go a b qs ss ts
          | b==0
          = (qs,ss,ts)

        go a b qs ss ts
          | otherwise  
          = let q = a `div` b
                r = a `mod` b
                s = ss !! 1 - (head qs * head ss)
                t = ts !! 1 - (head qs * head ts)
            in go b r (q : qs) (s : ss) (t : ts)

flatten_rat :: Rational -> Integer
flatten_rat r
  = let (s, t) = gcd_quotients (numerator r) (denominator r) 
        x = (1 + field_p * t) `div` denominator r
    in (numerator r * x) `mod` field_p
    
serialize_poly :: Poly a -> String
serialize_poly p = case p of
  Poly m -> 
    let size = Map.size m
        binds = Map.toList $ Map.mapKeys (+ 1) m
        string_binds = map (\(k,v) -> show k ++ "\n" ++ show v ++ "\n") binds
    in show size ++ "\n" ++ concat string_binds

serialize_r1c :: R1C a -> String
serialize_r1c cons = case cons of
  R1C (a, b, c) -> concat $ map serialize_poly [a, b, c]

serialize_r1cs :: R1CS a -> String
serialize_r1cs cs
  = let r1c_strings :: String
        r1c_strings = concat (map serialize_r1c (clauses cs))
    in show (length $ r1cs_in_vars cs) ++ "\n"
       ++ show (num_vars cs) ++ "\n"
       ++ show (length $ clauses cs) ++ "\n"
       ++ r1c_strings
