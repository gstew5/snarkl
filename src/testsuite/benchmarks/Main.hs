module Main where

import Criterion.Main

import Compile (SimplParam(..))
import Harness

import qualified List as List
-- import qualified Tree as Tree
-- import qualified Lam as Lam
import qualified Keccak as Keccak
import qualified Matrix as Matrix

mk_bgroup nm mf inputs result
  = bgroup nm 
    [ bench (nm ++ "-interp")              $ nf (test_interp mf) inputs
    , bench (nm ++ "-elaborate")           $ nfIO $ test_texp mf
    , bench (nm ++ "-constraints")         $ nfIO $ test_constraints mf
    , bench (nm ++ "-simplify")            $ nfIO $ test_simplify mf

    , bench (nm ++ "-simpl-r1cs")          $ nfIO $ test_r1cs Simplify mf
    , bench (nm ++ "-simpl-wit")           $ nfIO $ test_wit Simplify mf inputs
    , bench (nm ++ "-simpl-full")          $ nfIO $ test_full Simplify mf inputs result

      -- last three as above, but don't simplify
    , bench (nm ++ "-nosimpl-r1cs")        $ nfIO $ test_r1cs NoSimplify mf
    , bench (nm ++ "-nosimpl-wit")         $ nfIO $ test_wit NoSimplify mf inputs
    , bench (nm ++ "-nosimpl-full")        $ nfIO $ test_full NoSimplify mf inputs result
    ]

the_benchmarks
  = [ mk_bgroup "input-matrix" (Matrix.test2 70)
                ((Matrix.t2_m0 4900)++(Matrix.t2_m1 4900)) 2048215153250
    , mk_bgroup "keccak" (Keccak.keccak1 22) Keccak.input_vals 1
    , mk_bgroup "list"    List.test_listN (90 : take 100 [0..]) 90
    , mk_bgroup "fixed-matrix" (Matrix.test1 600) [0..599] 754740000
    ] 

-- the_benchmarks
--   = [ mk_bgroup "list" List.list_comp3 [1] 24
--     , mk_bgroup "tree" Tree.tree_test1 [1] 77
--     , mk_bgroup "lambda" Lam.beta_test1 [] 0
--     , mk_bgroup "keccak" (Keccak.keccak1 18) Keccak.input_vals 1
--     ] 

run_benchmarks
  = defaultMain the_benchmarks

main = run_benchmarks    

