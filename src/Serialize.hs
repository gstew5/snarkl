module Serialize where

import qualified Data.Map.Strict as Map

import Poly
import R1CS

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
