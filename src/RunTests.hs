module Main where

import Test.Hspec

import UnitTests
import Toplevel
       
main :: IO ()
main = hspec $ do

  describe "Boolean Tests" $ do

    describe "if-then-else" $ do 
      it "1-1" $ result_of prog1 [1,2,1] `shouldBe` (negate 240)

    describe "bigsum" $ do
      it "2-1" $ result_of (prog2 4) [0] `shouldBe` 10
      it "2-2" $ result_of (prog2 4) [1] `shouldBe` 15
      it "2-3" $ result_of (prog2 4) [2] `shouldBe` 20
      it "2-4" $ result_of (prog2 10) [10] `shouldBe` 165

    describe "arrays" $ do
      it "3-1" $ result_of prog3 [8]  `shouldBe` 512
      it "3-2" $ result_of prog3 [16] `shouldBe` 4096
      it "3-3" $ result_of prog3 [0]  `shouldBe` 0
      it "3-4" $ result_of prog3 [-1] `shouldBe` (-1)

      it "4-1" $ result_of prog4 [8]  `shouldBe` 512
      it "4-2" $ result_of prog4 [16] `shouldBe` 4096
      it "4-3" $ result_of prog4 [0]  `shouldBe` 0
      it "4-4" $ result_of prog4 [-1] `shouldBe` (-1)

      it "5-1" $ result_of prog5 [8]  `shouldBe` 8^(101::Integer)
      it "5-2" $ result_of prog5 [16] `shouldBe` 16^(101::Integer)
      it "5-3" $ result_of prog5 [0]  `shouldBe` 0
      it "5-4" $ result_of prog5 [-1] `shouldBe` (-1)

      it "6-1" $ result_of prog6 [8]  `shouldBe` 8

      it "7-1" $ result_of prog7 []   `shouldBe` 100

      it "8-1" $ result_of prog8 []   `shouldBe` 29

      it "11-1" $ result_of prog11 [1,1] `shouldBe` 1

      it "13-1" $ result_of prog13 [1] `shouldBe` 1            
  
    -- , (prog13, [1], 1)

    -- , (prog14, [3,4], 0)

    -- , (prog15, [], 2)

    -- , (prog26, [], 33)

    -- , (prog27, [], 34)

    -- , (prog28, [], 24)

    -- , (prog29, [1], 24)

    -- , (prog30, [], 24)      

    -- , (prog31, [4,2], 2)      
    -- , (prog31, [4,1], 4)      
    -- , (prog31, [4,4], 1)      
    -- , (prog31, [21,7], 3)

    -- , (prog34, [], 0)            
    -- ]
