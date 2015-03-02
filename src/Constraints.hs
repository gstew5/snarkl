{-# LANGUAGE GADTs,TypeSynonymInstances,FlexibleInstances #-}

module Constraints where

import qualified Data.IntMap.Lazy as Map

import Common
import Field
import Poly
import R1CS

----------------------------------------------------------------
--            Intermediate Constraint Language                --
----------------------------------------------------------------

-- | Constraints are either
--   * 'CAdd a m': A linear combination of the constant 'a' with
--     the variable-coeff. terms given by map 'm : Map.Map Var a'.
--   * 'CMult (c,x) (d,y) (e,mz)': A multiplicative constraint with
--     interpretation cx * dy = e (when mz = Nothing), or
--                    cx * dy = ez (when mz = Just z). 
data Constraint a =
    CAdd a (Assgn a)
  | CMult (a,Var) (a,Var) (a, Maybe Var)
  deriving (Eq,Ord)

instance Show a => Show (Constraint a) where
  show (CAdd a m) = show a ++ " + " ++ go (Map.toList m)
    where go [] = " == 0"
          go [(x,c)] = show c ++ "x" ++ show x ++ go []
          go ((x,c) : c_xs) = show c ++ "x" ++ show x ++ " + " ++ go c_xs

  show (CMult (c,x) (d,y) (e,mz))
    = let show_term c0 x0 = show c0 ++ "x" ++ show x0
      in show_term c x ++ " * " ++ show_term d y
         ++ " == " 
         ++ case mz of
              Nothing -> show e
              Just z  -> show_term e z

r1cs_of_cs :: Field a 
           => [Constraint a] -- ^ Constraints
           -> Int -- ^ Total number of variables
           -> [Var] -- ^ Input variables
           -> [Var] -- ^ Output variables
           -> (Assgn a -> Assgn a) -- ^ Witness generator
           -> R1CS a
r1cs_of_cs cs = R1CS $ go cs
  where go [] = []
        go (CAdd a m : cs')
          = R1C (const_poly one,Poly $ Map.insert (-1) a m,const_poly zero) : go cs'

        go (CMult cx dy (e,Nothing) : cs')
          = R1C (var_poly cx,var_poly dy,const_poly e) : go cs'

        go (CMult cx dy (e,Just z) : cs')
          = R1C (var_poly cx,var_poly dy,var_poly (e,z)) : go cs'


            

        
