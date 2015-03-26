module Serialize where

import qualified Data.IntMap.Lazy as Map
import Data.Ratio

import Errors
import Field
import Poly
import R1CS

flatten_rat :: Rational -> IntP
flatten_rat r
  = let a = numerator r
        b = denominator r
    in case mod_inv b field_p of
         Nothing ->
           fail_with $ ErrMsg ("expected " ++ show b ++ " to be invertible")
         Just b_inv -> int_p (a * b_inv)
    
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
