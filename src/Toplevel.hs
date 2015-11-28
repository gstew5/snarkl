module Toplevel
  ( -- * Interpret Snarkl Computations
    comp_interp

    -- * Desugar
  , TExpPkg(..)
  , texp_of_comp

    -- * Generate Constraints    
  , constrs_of_texp
  , constrs_of_comp

    -- * Generate R1CS
  , r1cs_of_constrs
  , r1cs_of_texp
  , r1cs_of_comp

    -- * Given arguments, construct a witness
  , wit_of_r1cs
    -- * Serialize the resulting inputs assignment
  , serialize_inputs
    -- * Serialize the resulting witness assignment
  , serialize_witnesses

    -- * Serialize R1CS in 'libsnark' format
  , serialize_r1cs

    -- * For a given Snarkl computation, use 'libsnark' to test: (1)
    -- key generation, (2) proof generation, and (3) proof
    -- verification.  Currently assumes 'Toplevel' is loaded in working
    -- directory 'base-of-snarkl-repo'.
  , snarkify_comp
  , keygen_comp -- for benchmarking
  , proofgen_comp -- for benchmarking

    -- * Convenience functions
  , Result(..)
  , result_of_comp
  , int_of_comp
  , test_comp
  , benchmark_comp

    -- * Re-exported modules
  , module SyntaxMonad
  , module Constraints
  , module Simplify
  , module R1CS
  ) where

import           System.IO
  ( hFlush
  , stdout
  , hPutStr
  , hPutStrLn
  , withFile
  , IOMode( WriteMode )
  )

import qualified Data.IntMap.Lazy as IntMap
import           Data.List (sort)
import qualified Data.Map.Strict as Map
import           Data.Typeable
import           Prelude
import qualified Prelude as P
import           System.Exit
import           System.Process

import           Common
import           Compile
import           Constraints
import           Errors
import           Interp ( interp )
import           R1CS
import qualified Serialize as Serialize
import           Simplify
import           SyntaxMonad
import           TExpr

----------------------------------------------------
--
-- Toplevel Stuff 
--        
----------------------------------------------------        

-- | Using the executable semantics for the 'TExp' language, execute
-- the computation on the provided inputs, returning the 'Rational' result.
comp_interp :: Typeable ty
            => Comp ty
            -> [Rational]
            -> Rational
comp_interp mf inputs
  = let TExpPkg _ in_vars e = texp_of_comp mf
        input_map           = IntMap.fromList $ zip in_vars inputs
    in case interp input_map e of
         Left err -> fail_with err
         Right (_,Nothing) -> fail_with $ ErrMsg $ show e ++ " evaluated to bot"
         Right (_,Just v) -> v

------------------------------------------------------
--
-- 'TExp'
--        
------------------------------------------------------        

-- | The result of desugaring a Snarkl computation.
data TExpPkg ty
  = TExpPkg { comp_num_vars :: Int -- ^ The number of free variables in the computation. 
            , comp_input_vars :: [Var] -- ^ The variables marked as inputs.
            , comp_texp :: TExp ty Rational -- ^ The resulting 'TExp'.
            }
    deriving Show

-- | Desugar a 'Comp'utation to a pair of:
--   the total number of vars,
--   the input vars,
--   the 'TExp'.
texp_of_comp :: Typeable ty
             => Comp ty
             -> TExpPkg ty
texp_of_comp mf
  = case run mf of
      Left err -> fail_with err
      Right (e,rho) ->
        let nv = next_var rho
            in_vars = sort $ input_vars rho
        in TExpPkg nv in_vars e
  where run :: State Env a -> CompResult Env a
        run mf0 = runState mf0 (Env (fromInteger 0) (fromInteger 0)
                                [] Map.empty Map.empty)

------------------------------------------------------
--
-- Constraint generation
--        
------------------------------------------------------        

-- | Compile 'TExp's to constraint systems. Re-exported from 'Compile.Compile'.
constrs_of_texp :: Typeable ty
                => TExpPkg ty
                -> ConstraintSystem Rational
constrs_of_texp (TExpPkg out in_vars e) = constraints_of_texp out in_vars e
-- | Compile Snarkl computations to constraint systems.
constrs_of_comp :: Typeable ty
                => Comp ty
                -> ConstraintSystem Rational
constrs_of_comp = constrs_of_texp . texp_of_comp

------------------------------------------------------
--
-- R1CS
--        
------------------------------------------------------        

-- | Compile constraint systems to 'R1CS'. Re-exported from 'Constraints.hs'.
r1cs_of_constrs :: Field a 
                => SimplParam
                -> ConstraintSystem a -- ^ Constraints
                -> R1CS a
r1cs_of_constrs = r1cs_of_constraints

-- | Compile 'TExp's to 'R1CS'.
r1cs_of_texp :: Typeable ty
             => SimplParam
             -> TExpPkg ty
             -> R1CS Rational
r1cs_of_texp simpl = (r1cs_of_constrs simpl) . constrs_of_texp

-- | Compile Snarkl computations to 'R1CS'.
r1cs_of_comp :: Typeable ty
             => SimplParam
             -> Comp ty
             -> R1CS Rational
r1cs_of_comp simpl = (r1cs_of_constrs simpl) . constrs_of_comp

-- | For a given R1CS and inputs, calculate a satisfying assignment.
wit_of_r1cs inputs r1cs
  = let in_vars = r1cs_in_vars r1cs
        f = r1cs_gen_witness r1cs . IntMap.fromList
    in case length in_vars /= length inputs of
         True ->
           fail_with
           $ ErrMsg ("expected " ++ show (length in_vars) ++ " input(s)"
                     ++ " but got " ++ show (length inputs) ++ " input(s)")
         False ->
           f (zip in_vars inputs)

-- | For a given R1CS and inputs, serialize the input variable assignment.
serialize_inputs :: [Rational] -> R1CS Rational -> String
serialize_inputs inputs r1cs
  = let inputs_assgn = IntMap.fromList $ zip (r1cs_in_vars r1cs) inputs
    in Serialize.serialize_assgn inputs_assgn

-- | For a given R1CS and inputs, serialize the witness variable assignment.
serialize_witnesses :: [Rational] -> R1CS Rational -> String
serialize_witnesses inputs r1cs
  = let num_in_vars  = length $ r1cs_in_vars r1cs
        assgn        = wit_of_r1cs inputs r1cs
        inputs_assgn = IntMap.fromList $ drop num_in_vars $ IntMap.toAscList assgn
    in Serialize.serialize_assgn inputs_assgn

serialize_r1cs = Serialize.serialize_r1cs           

------------------------------------------------------
--
-- Libsnark hooks
--        
------------------------------------------------------        

-- |                       *** WARNING ***
-- This function creates/overwrites files prefixed with 'filePrefix',
-- within the scripts/ subdirectory. 'snarkify_comp' also
-- assumes that it's run in working directory 'base-of-snarkl-repo'.
snarkify_comp filePrefix simpl c inputs
  = do { let r1cs = r1cs_of_comp simpl c
             r1cs_file   = filePrefix ++ ".r1cs"
             inputs_file = filePrefix ++ ".inputs"
             wits_file   = filePrefix ++ ".wits"
             run_r1cs    = "./run-r1cs.sh"
             
       ; withFile ("scripts/" ++ r1cs_file) WriteMode (\h ->
             hPutStrLn h $ serialize_r1cs r1cs)

       ; withFile ("scripts/" ++ inputs_file) WriteMode (\h ->
             hPutStr h $ serialize_inputs inputs r1cs)

       ; withFile ("scripts/" ++ wits_file) WriteMode (\h ->
             hPutStr h $ serialize_witnesses inputs r1cs)

       ; (_,_,_,hdl) <-
            createProcess (proc run_r1cs [r1cs_file,inputs_file,wits_file])
            { cwd = Just "scripts" }

       ; waitForProcess hdl 
       }

-- Like snarkify_comp, but only generate keys
keygen_comp filePrefix simpl c inputs
  = do { let r1cs = r1cs_of_comp simpl c
             r1cs_file   = filePrefix ++ ".r1cs"
             inputs_file = filePrefix ++ ".inputs"
             wits_file   = filePrefix ++ ".wits"
             run_r1cs    = "./run-keygen.sh"
             
       ; withFile ("scripts/" ++ r1cs_file) WriteMode (\h ->
             hPutStrLn h $ serialize_r1cs r1cs)

       ; withFile ("scripts/" ++ inputs_file) WriteMode (\h ->
             hPutStr h $ serialize_inputs inputs r1cs)

       ; withFile ("scripts/" ++ wits_file) WriteMode (\h ->
             hPutStr h $ serialize_witnesses inputs r1cs)

       ; (_,_,_,hdl) <-
            createProcess (proc run_r1cs [r1cs_file,inputs_file,wits_file])
            { cwd = Just "scripts" }

       ; waitForProcess hdl 
       }

-- Like snarkify_comp, but only generate keys and proof
proofgen_comp filePrefix simpl c inputs
  = do { let r1cs = r1cs_of_comp simpl c
             r1cs_file   = filePrefix ++ ".r1cs"
             inputs_file = filePrefix ++ ".inputs"
             wits_file   = filePrefix ++ ".wits"
             run_r1cs    = "./run-proofgen.sh"
             
       ; withFile ("scripts/" ++ r1cs_file) WriteMode (\h ->
             hPutStrLn h $ serialize_r1cs r1cs)

       ; withFile ("scripts/" ++ inputs_file) WriteMode (\h ->
             hPutStr h $ serialize_inputs inputs r1cs)

       ; withFile ("scripts/" ++ wits_file) WriteMode (\h ->
             hPutStr h $ serialize_witnesses inputs r1cs)

       ; (_,_,_,hdl) <-
            createProcess (proc run_r1cs [r1cs_file,inputs_file,wits_file])
            { cwd = Just "scripts" }

       ; waitForProcess hdl 
       }


------------------------------------------------------
--
-- Convenience functions
--        
------------------------------------------------------        

-- | The result of compiling and executing a Snarkl computation.
data Result a = 
  Result { result_sat :: Bool
         , result_vars :: Int
         , result_constraints :: Int
         , result_result :: a
         , result_r1cs :: String
         }

instance Show a => Show (Result a) where
  show (Result the_sat the_vars the_constraints the_result _)
    = "sat = " ++ show the_sat
      ++ ", vars = " ++ show the_vars
      ++ ", constraints = " ++ show the_constraints
      ++ ", result = " ++ show the_result

-- | Compile a computation to R1CS, and run it on the provided inputs.
-- Also, interprets the computation using the executable semantics and
-- checks that the results match.
result_of_comp :: Typeable ty => SimplParam -> Comp ty -> [Rational] -> Result Rational
result_of_comp simpl mf inputs
  = execute simpl mf inputs

-- | Same as 'result_of_comp', but specialized to integer arguments
-- and results. Returns just the integer result.
int_of_comp :: Typeable ty => SimplParam -> Comp ty -> [Int] -> Int
int_of_comp simpl mf args
  = truncate $ result_result $ result_of_comp simpl mf (map fromIntegral args)

-- | Same as 'int_of_comp', but additionally runs resulting R1CS
-- through key generation, proof generation, and verification stages
-- of 'libsnark'.  TODO: This function does duplicate R1CS generation,
-- once for 'libsnark' and a second time for 'int_of_comp'.
test_comp :: Typeable ty => SimplParam -> Comp ty -> [Int] -> IO (Either ExitCode Int)
test_comp simpl mf args
  = do { exit_code <- snarkify_comp "hspec" simpl mf (map fromIntegral args)
       ; case exit_code of
           ExitFailure _ -> Prelude.return $ Left exit_code
           ExitSuccess   -> Prelude.return $ Right (int_of_comp simpl mf args)
       }


--------------------------------------------------
--
-- Internal Functions
--
--------------------------------------------------

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, 'w'.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check whether the R1CS result matches the interpreter result.
--   (5) Return the 'Result'.
execute :: Typeable ty => SimplParam -> Comp ty -> [Rational] -> Result Rational
execute simpl mf inputs
  = let TExpPkg nv in_vars e  = texp_of_comp mf
        r1cs                  = r1cs_of_texp simpl (TExpPkg nv in_vars e)
        r1cs_string           = serialize_r1cs r1cs        
        nw        = r1cs_num_vars r1cs
        [out_var] = r1cs_out_vars r1cs
        ng        = num_constraints r1cs
        wit       = wit_of_r1cs inputs r1cs
        out = case IntMap.lookup out_var wit of
                Nothing ->
                  fail_with
                  $ ErrMsg ("output variable " ++ show out_var
                            ++ "not mapped, in\n  " ++ show wit)
                Just out_val -> out_val
        -- Interpret the program using the executable semantics and
        -- the input assignment (a subset of 'wit').
        -- Output the return value of 'e'.
        out_interp = comp_interp mf inputs
        result = case out_interp == out of
                   True -> sat_r1cs wit r1cs
                   False -> fail_with
                            $ ErrMsg $ "interpreter result " ++ show out_interp
                              ++ " differs from actual result " ++ show out
    in Result result nw ng out r1cs_string

-- | 'execute' computation, reporting error if result doesn't match
-- the return value provided by the caller. Also, serializes the
-- resulting 'R1CS'.
benchmark_comp :: Typeable ty => (SimplParam, Comp ty, [Rational], Rational) -> IO ()
benchmark_comp (simpl,prog,inputs,res)
  = let print_ln = print_ln_to_file stdout
        print_ln_to_file h s = (P.>>) (hPutStrLn h s) (hFlush h)
        print_to_file s
          = withFile "test_cs_in.ppzksnark" WriteMode (flip print_ln_to_file s)
    in case execute simpl prog inputs of
      r@(Result True _ _ res' r1cs_string) ->
        if res == res' then
          do { print_to_file r1cs_string
             ; print_ln $ show r
             }
        else
          print_ln
          $ show
          $ "error: results don't match: "
          ++ "expected " ++ show res ++ " but got " ++ show res'
      Result False _ _ _ _ ->
        print_ln $ "error: witness failed to satisfy constraints"
