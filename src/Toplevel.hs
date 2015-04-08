module Toplevel
  ( -- | Top-level functions
    Result(..)
  , run
  , check
  , test
  ) where

import System.IO
  ( hFlush
  , stdout
  , hPutStrLn
  , withFile
  , IOMode( WriteMode )
  )

import qualified Prelude as P
import Prelude

import Data.Typeable

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Lazy as IntMap

import Errors
import R1CS
import Compile
import Serialize
import Interp ( interp )
import SyntaxMonad

----------------------------------------------------
--
-- Toplevel Stuff 
--        
----------------------------------------------------        

data Result = 
  Result { result_sat :: Bool
         , result_vars :: Int
         , result_constraints :: Int
         , result_result :: Rational 
         , result_r1cs :: String
         }

instance Show Result where
  show (Result the_sat the_vars the_constraints the_result _)
    = "sat = " ++ show the_sat
      ++ ", vars = " ++ show the_vars
      ++ ", constraints = " ++ show the_constraints
      ++ ", result = " ++ show the_result

run :: State Env a -> CompResult Env a
run mf = runState mf (Env (P.fromInteger 0) [] Map.empty Set.empty Map.empty)

check :: Typeable ty => Comp ty -> [Rational] -> Result
check mf inputs
  = let (e,s) =
          case run mf of
            Left err -> fail_with err
            Right x -> x
        nv       = next_var s
        in_vars  = reverse $ input_vars s
        r1cs     = r1cs_of_exp nv in_vars e
        r1cs_string = serialize_r1cs r1cs
        nw        = r1cs_num_vars r1cs
        f         = r1cs_gen_witness r1cs . IntMap.fromList
        [out_var] = r1cs_out_vars r1cs
        ng  = num_constraints r1cs
        wit = case length in_vars /= length inputs of
                True ->
                  fail_with
                  $ ErrMsg ("expected " ++ show (length in_vars) ++ " input(s)"
                            ++ " but got " ++ show (length inputs) ++ " input(s)")
                False ->
                  f (zip in_vars inputs)
        out = case IntMap.lookup out_var wit of
                Nothing ->
                  fail_with
                  $ ErrMsg ("output variable " ++ show out_var
                            ++ "not mapped, in\n  " ++ show wit)
                Just out_val -> out_val
        out_interp
          = case interp wit e of
              Left err -> fail_with err
              Right (_,Nothing) ->
                fail_with
                $ ErrMsg $ show e ++ " evaluated to bot"
              Right (_,Just v) -> v
        result
          = case out_interp == out of
              True -> sat_r1cs wit r1cs
              False -> fail_with
                       $ ErrMsg $ "interpreter result " ++ show out_interp
                         ++ " differs from actual result " ++ show out
    in Result result nw ng out r1cs_string

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, w.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check that results match.
do_test :: Typeable ty => (Comp ty, [Rational], Rational) -> IO ()
do_test (prog,inputs,res) =
  let print_ln             = print_ln_to_file stdout
      print_ln_to_file h s = (P.>>) (hPutStrLn h s) (hFlush h)
      print_to_file s
        = withFile "test_cs_in.ppzksnark" WriteMode (flip print_ln_to_file s)
  in case check prog inputs of
    r@(Result True _ _ res' r1cs_string) ->
      case res == res' of
        True  ->  (P.>>) (print_to_file r1cs_string) (print_ln $ show r)
        False ->  print_ln $ show $ "error: results don't match: "
                  ++ "expected " ++ show res ++ " but got " ++ show res'
    Result False _ _ _ _ ->
      print_ln $ "error: witness failed to satisfy constraints"

test :: Typeable ty => (Comp ty,[Int],Integer) -> IO ()
test (prog,args,res)
  = do_test (prog,map fromIntegral args,fromIntegral res)

