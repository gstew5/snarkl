{-# LANGUAGE GADTs #-}

module Harness where

import           System.IO (hPutStrLn, stderr)
import           GHC.IO.Exception

import qualified Data.IntMap.Lazy as IntMap
import qualified Data.Set as Set
import           Data.Typeable

import           Compile (SimplParam)
import           TExpr
import           Errors
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
-- generated.) Also, serialize the r1cs to stderr.
test_r1cs :: Typeable ty => SimplParam -> Comp ty -> IO ()
test_r1cs simpl mf
  = let texp_pkg = texp_of_comp mf
        constrs  = constrs_of_texp texp_pkg
        r1cs     = r1cs_of_constrs simpl constrs
    in hPutStrLn stderr
       $ show
       $ serialize_r1cs r1cs 

-- Same as 'test_r1cs', but also generates and serializes
-- a satisfying assignment, as well as serializing the given inputs.
test_wit :: (Integral a, Typeable ty) => SimplParam -> Comp ty -> [a] -> IO ()
test_wit simpl mf inputs
  = let texp_pkg = texp_of_comp mf
        r1cs     = r1cs_of_texp simpl texp_pkg
    in do { hPutStrLn stderr (serialize_r1cs r1cs)
          ; hPutStrLn stderr (serialize_witnesses (map fromIntegral inputs) r1cs)
          ; hPutStrLn stderr (serialize_inputs (map fromIntegral inputs) r1cs)
          } 

test_keygen :: Typeable ty => SimplParam -> Comp ty -> [Int] -> IO ()
test_keygen simpl mf inputs
  = do { exit <- keygen_comp "test" simpl mf (map fromIntegral inputs)
       ; case exit of
           ExitSuccess -> Prelude.return ()
           ExitFailure err -> fail_with $ ErrMsg $ "test_full failed with " ++ show err
       }

test_proofgen :: Typeable ty => SimplParam -> Comp ty -> [Int] -> IO ()
test_proofgen simpl mf inputs
  = do { exit <- proofgen_comp "test" simpl mf (map fromIntegral inputs)
       ; case exit of
           ExitSuccess -> Prelude.return ()
           ExitFailure err -> fail_with $ ErrMsg $ "test_full failed with " ++ show err
       }

-- Run libsnark on the resulting files.
test_crypto :: Typeable ty => SimplParam -> Comp ty -> [Int] -> IO ()
test_crypto simpl mf inputs
  = do { exit <- snarkify_comp "test" simpl mf (map fromIntegral inputs)
       ; case exit of
           ExitSuccess -> Prelude.return ()
           ExitFailure err -> fail_with $ ErrMsg $ "test_full failed with " ++ show err
       }

-- This function "executes" the comp two ways, once by interpreting
-- the resulting TExp and second by interpreting the resulting circuit
-- on the inputs provided. Both results are checked to match 'res'.
-- The function outputs a 'Result' that details number of variables and
-- constraints in the resulting constraint system.
test_numconstrs :: Typeable ty => SimplParam -> Comp ty -> [Int] -> Rational -> IO ()
test_numconstrs simpl mf inputs res
  = benchmark_comp (simpl, mf, map fromIntegral inputs, res)


