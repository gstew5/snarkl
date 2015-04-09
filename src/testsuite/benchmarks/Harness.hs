module Harness where

import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Set as Set
import           Data.Typeable

import           Compile
import           Constraints
import           R1CS
import           Simplify
import           SyntaxMonad ( Comp )
import           Toplevel

-- Just interpret.
test_interp mf inputs
  = texp_interp mf (map fromIntegral inputs)

-- Just compile to constraints (no simplification yet).
test_constraints :: Typeable ty => Comp ty -> IO ()
test_constraints mf
  = let (nv,in_vars,te) = texp_of_comp mf
        constrs         = constraints_of_texp nv in_vars te
    in putStrLn
       $ show
       $ Set.size
       $ cs_constraints constrs

-- Compile to constraints and simplify.
test_simplify :: Typeable ty => Comp ty -> IO ()
test_simplify mf
  = let (nv,in_vars,te) = texp_of_comp mf
        constrs         = constraints_of_texp nv in_vars te
        (_,constrs')    = do_simplify False IntMap.empty constrs
    in putStrLn
       $ show
       $ Set.size
       $ cs_constraints constrs'

-- Generate (simplified) R1CS, but don't run it yet.  (No witness is
-- generated.)
test_r1cs mf
  = let (nv,in_vars,te) = texp_of_comp mf
        r1cs            = r1cs_of_texp nv in_vars te
    in putStrLn
       $ show
       $ last (r1cs_clauses r1cs) 

-- Same as 'test_r1cs', but also generates a satisfying assignment.
test_wit mf inputs
  = let (nv,in_vars,te) = texp_of_comp mf
        r1cs           = r1cs_of_texp nv in_vars te
        wit            = wit_of_r1cs (map fromIntegral inputs) r1cs
    in case IntMap.lookup 1000000 wit of
         Nothing -> putStr $ show $ last (r1cs_clauses r1cs) 
         Just v  -> putStr $ show v ++ (show $ last (r1cs_clauses r1cs))

-- Do everything.
test_full mf inputs result
  = test (mf, inputs, result)



