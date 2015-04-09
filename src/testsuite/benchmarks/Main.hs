module Main where

import Criterion.Main
import qualified Keccak as Keccak

run_benchmarks
  = defaultMain
    [ bgroup "micro" [ bench "keccak-interp" $ nf Keccak.test_interp 2
                     , bench "keccak-r1cs"   $ nfIO (Keccak.test_r1cs 2)
                     , bench "keccak-wit"    $ nfIO (Keccak.test_wit 2)
                     , bench "keccak-full"   $ nfIO (Keccak.test_full 2)
                     ]
    ]

main = run_benchmarks    

