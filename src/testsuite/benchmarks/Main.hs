module Main where

import Criterion.Main

import Compile (SimplParam(..))
import Harness

import qualified List as List
import qualified Keccak as Keccak
import qualified Matrix as Matrix

mk_bgroup nm mf inputs result
  = bgroup nm 
    [ bench (nm ++ "-elaborate")     $ nfIO $ test_texp mf
    , bench (nm ++ "-constraints")   $ nfIO $ test_constraints mf
    , bench (nm ++ "-simplify")      $ nfIO $ test_simplify mf
    , bench (nm ++ "-r1cs")          $ nfIO $ test_r1csgen Simplify mf
    , bench (nm ++ "-witgen")           $ nfIO $ test_witgen Simplify mf inputs
     , bench (nm ++ "-keygen")        $ nfIO $ test_keygen Simplify mf inputs
    , bench (nm ++ "-verif")         $ nfIO $ test_crypto Simplify mf inputs
    , bench (nm ++ "-full")          $ nfIO $ test_numconstrs Simplify mf inputs result
    ]

the_benchmarks
  = [ mk_bgroup "keccak800" (Keccak.keccak1 22) Keccak.input_vals 1
    , mk_bgroup "map-list" List.test_listN (90 : take 100 [0..]) 90
    ,  mk_bgroup "fixed-matrix600" (Matrix.test1 600) [0..599] 754740000
    , mk_bgroup "input-matrix70" (Matrix.test2 70)
                ((Matrix.t2_m0 4900)++(Matrix.t2_m1 4900)) 2048215153250
    ] 

run_benchmarks
  = defaultMain the_benchmarks

main = run_benchmarks    

