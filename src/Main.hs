module Main where

import Criterion.Main

import UnitTests
import Toplevel
import qualified Keccak as Keccak

notify nm mf
  = do { putStr "Start: "
       ; putStrLn nm
       ; putStrLn "============================="
       ; mf
       ; putStr "End: "
       ; putStrLn nm
       }

unit_tests
  = do { notify "Bool Tests" $ mapM_ test bool_tests
       ; notify "Field Tests" $ mapM_ test bool_tests
       ; notify "Keccak Test" $ Keccak.test_full 2
       } 

run_benchmarks
  = defaultMain
    [ bgroup "micro" [ bench "keccak-interp" $ nf Keccak.test_interp 2
                     , bench "keccak-r1cs"   $ nfIO (Keccak.test_r1cs 2)
                     , bench "keccak-wit"    $ nfIO (Keccak.test_wit 2)
                     , bench "keccak-full"   $ nfIO (Keccak.test_full 2)
                     ]
    ]
    
main
  = do { notify "Unit Tests" unit_tests
       ; notify "Benchmarks" run_benchmarks
       }

    

