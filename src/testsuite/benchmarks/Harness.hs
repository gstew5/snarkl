module Harness where

import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Set as Set
import           Data.Typeable

import           Toplevel

-- Just interpret.
test_interp :: Typeable ty => Comp ty -> [Int] -> Rational
test_interp mf inputs
  = comp_interp mf (map fromIntegral inputs)

-- Just compile to constraints (no simplification yet).
test_constraints :: Typeable ty => Comp ty -> IO ()
test_constraints mf
  = let texp_pkg = texp_of_comp mf
        constrs  = constrs_of_texp texp_pkg
    in putStrLn
       $ show
       $ Set.size
       $ cs_constraints constrs

-- Compile to constraints and simplify.
test_simplify :: Typeable ty => Comp ty -> IO ()
test_simplify mf
  = let texp_pkg     = texp_of_comp mf
        constrs      = constrs_of_texp texp_pkg
        (_,constrs') = do_simplify False IntMap.empty constrs
    in putStrLn
       $ show
       $ Set.size
       $ cs_constraints constrs'

-- Generate (simplified) R1CS, but don't run it yet.  (No witness is
-- generated.)
test_r1cs mf
  = let texp_pkg = texp_of_comp mf
        r1cs     = r1cs_of_texp texp_pkg
    in putStrLn
       $ show
       $ last (r1cs_clauses r1cs) 

-- Same as 'test_r1cs', but also generates a satisfying assignment.
test_wit mf inputs
  = let texp_pkg = texp_of_comp mf
        r1cs     = r1cs_of_texp texp_pkg
        wit      = wit_of_r1cs (map fromIntegral inputs) r1cs
    in case IntMap.lookup 1000000 wit of
         Nothing -> putStr $ show $ last (r1cs_clauses r1cs) 
         Just v  -> putStr $ show v ++ (show $ last (r1cs_clauses r1cs))

-- Do everything.
test_full :: Typeable ty => Comp ty -> [Int] -> Rational -> IO ()
test_full mf inputs result
  = benchmark_comp (mf, map fromIntegral inputs, result)



