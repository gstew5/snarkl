module Main where

import Criterion.Main

import Harness

import qualified Lam as Lam
import qualified Keccak as Keccak

mk_bgroup nm mf inputs result
  = bgroup nm 
    [ bench (nm ++ "-interp")        $ nf   (test_interp mf) inputs
    , bench (nm ++ "-constraints")   $ nfIO $ test_constraints mf
    , bench (nm ++ "-simplify")      $ nfIO $ test_simplify mf            
    , bench (nm ++ "-r1cs")          $ nfIO $ test_r1cs mf
    , bench (nm ++ "-wit")           $ nfIO $ test_wit mf inputs
    , bench (nm ++ "-full")          $ nfIO $ test_full mf inputs result
    ]

the_benchmarks
  = [ mk_bgroup "lambda" Lam.beta_test1 [] 0
    , mk_bgroup "keccak" (Keccak.keccak1 2) Keccak.input_vals 1
    ] 

run_benchmarks
  = defaultMain the_benchmarks

main = run_benchmarks    

