{-# LANGUAGE GADTs #-}

module Harness where

import           System.IO (hPutStrLn, stderr)

import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Set as Set
import           Data.Typeable

import           Compile (SimplParam)
import           TExpr
import           Toplevel

-- Just interpret.
test_interp :: Typeable ty => Comp ty -> [Int] -> Rational
test_interp mf inputs
  = comp_interp mf (map fromIntegral inputs)

-- Just elaborate to TExp.
test_texp :: Typeable ty => Comp ty -> IO ()
test_texp mf = (hPutStrLn stderr . show . extract_rat . last_seq . comp_texp . texp_of_comp) mf
  where extract_rat :: TExp ty Rational -> Int
        extract_rat te =
          case te of
            TEVar _ -> 0
            TEVal _ -> 1
            TEUnop _ _ -> 2
            TEBinop _ _ _ -> 3
            TEIf _ _ _ -> 4
            TEAssert _ _ -> 5
            TESeq _ _ -> 6
            TEBot -> 7

-- Just compile to constraints (no simplification yet).
test_constraints :: Typeable ty => Comp ty -> IO ()
test_constraints mf
  = let texp_pkg = texp_of_comp mf
        constrs  = constrs_of_texp texp_pkg
    in hPutStrLn stderr
       $ show
       $ Set.size
       $ cs_constraints constrs

-- Compile to constraints and simplify.
test_simplify :: Typeable ty => Comp ty -> IO ()
test_simplify mf
  = let texp_pkg     = texp_of_comp mf
        constrs      = constrs_of_texp texp_pkg
        (_,constrs') = do_simplify False IntMap.empty constrs
    in hPutStrLn stderr
       $ show
       $ Set.size
       $ cs_constraints constrs'

-- Generate (simplified) R1CS, but don't run it yet.  (No witness is
-- generated.)
test_r1cs :: Typeable ty => SimplParam -> Comp ty -> IO ()
test_r1cs simpl mf
  = let texp_pkg = texp_of_comp mf
        constrs  = constrs_of_texp texp_pkg
        r1cs     = r1cs_of_constrs simpl constrs
    in hPutStrLn stderr
       $ show
       $ length (r1cs_clauses r1cs) 

-- Same as 'test_r1cs', but also generates a satisfying assignment.
test_wit :: (Integral a, Typeable ty) => SimplParam -> Comp ty -> [a] -> IO ()
test_wit simpl mf inputs
  = let texp_pkg = texp_of_comp mf
        r1cs     = r1cs_of_texp simpl texp_pkg
        wit      = wit_of_r1cs (map fromIntegral inputs) r1cs
    in case IntMap.lookup 1000000 wit of
         Nothing -> hPutStrLn stderr $ show $ last (r1cs_clauses r1cs) 
         Just v  -> hPutStrLn stderr $ show v ++ (show $ last (r1cs_clauses r1cs))

-- Do everything.
test_full :: Typeable ty => SimplParam -> Comp ty -> [Int] -> Rational -> IO ()
test_full simpl mf inputs result
  = benchmark_comp (simpl, mf, map fromIntegral inputs, result)



