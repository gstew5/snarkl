module Main where

import Test.Hspec

import Keccak
import Toplevel
import UnitTests

main :: IO ()
main = hspec $ do

  describe "Field Tests" $ do

    describe "if-then-else" $ do 
      it "1-1" $ int_of_comp prog1 [1,2,1] `shouldBe` (negate 240)

    describe "bigsum" $ do
      it "2-1" $ int_of_comp (prog2 4) [0] `shouldBe` 10
      it "2-2" $ int_of_comp (prog2 4) [1] `shouldBe` 15
      it "2-3" $ int_of_comp (prog2 4) [2] `shouldBe` 20
      it "2-4" $ int_of_comp (prog2 10) [10] `shouldBe` 165

    describe "arrays" $ do
      it "3-1" $ int_of_comp prog3 [8]  `shouldBe` 512
      it "3-2" $ int_of_comp prog3 [16] `shouldBe` 4096
      it "3-3" $ int_of_comp prog3 [0]  `shouldBe` 0
      it "3-4" $ int_of_comp prog3 [-1] `shouldBe` (-1)

      it "4-1" $ int_of_comp prog4 [8]  `shouldBe` 512
      it "4-2" $ int_of_comp prog4 [16] `shouldBe` 4096
      it "4-3" $ int_of_comp prog4 [0]  `shouldBe` 0
      it "4-4" $ int_of_comp prog4 [-1] `shouldBe` (-1)

      it "5-1" $ int_of_comp prog5 [8]  `shouldBe` 8^(101::Integer)
      it "5-2" $ int_of_comp prog5 [16] `shouldBe` 16^(101::Integer)
      it "5-3" $ int_of_comp prog5 [0]  `shouldBe` 0
      it "5-4" $ int_of_comp prog5 [-1] `shouldBe` (-1)

    describe "times" $ do
      it "6-1" $ int_of_comp prog6 [8]  `shouldBe` 8

    describe "forall" $ do
      it "7-1" $ int_of_comp prog7 []   `shouldBe` 100

    describe "foral2" $ do
      it "8-1" $ int_of_comp prog8 []   `shouldBe` 29

    describe "unused inputs" $ do
      it "11-1" $ int_of_comp prog11 [1,1] `shouldBe` 1

    describe "multiplicative identity" $ do
      it "13-1" $ int_of_comp prog13 [1] `shouldBe` 1

    describe "opt: 0x * 3y = out ~~> out=0" $ do
      it "14-1" $ int_of_comp prog14 [3,4] `shouldBe` 0

    describe "exp_binop smart constructor: 3 - (2 - 1) = 2" $ do
      it "15-1" $ int_of_comp prog15 [] `shouldBe` 2

    describe "lists" $ do
      it "26-1" $ int_of_comp prog26 [] `shouldBe` 33
      it "27-1" $ int_of_comp prog27 [] `shouldBe` 34
      it "28-1" $ int_of_comp prog28 [] `shouldBe` 24
      it "29-1" $ int_of_comp prog29 [1] `shouldBe` 24
      it "30-1" $ int_of_comp prog30 [] `shouldBe` 24
      
    describe "div" $ do
      it "31-1" $ int_of_comp prog31 [4,2] `shouldBe` 2
      it "31-1" $ int_of_comp prog31 [4,1] `shouldBe` 4
      it "31-1" $ int_of_comp prog31 [4,4] `shouldBe` 1
      it "31-1" $ int_of_comp prog31 [21,7] `shouldBe` 3

    describe "beta" $ do 
      it "34-1" $ int_of_comp prog34 [] `shouldBe` 0

  describe "Boolean Tests" $ do

    describe "and" $ do 
      it "9-1" $ int_of_comp bool_prog9 [0,0] `shouldBe` 0
      it "9-2" $ int_of_comp bool_prog9 [0,1] `shouldBe` 0
      it "9-3" $ int_of_comp bool_prog9 [1,0] `shouldBe` 0
      it "9-4" $ int_of_comp bool_prog9 [1,1] `shouldBe` 1      

    describe "xor" $ do 
      it "10-1" $ int_of_comp bool_prog10 [0,0] `shouldBe` 0
      it "10-2" $ int_of_comp bool_prog10 [0,1] `shouldBe` 1
      it "10-3" $ int_of_comp bool_prog10 [1,0] `shouldBe` 1
      it "10-4" $ int_of_comp bool_prog10 [1,1] `shouldBe` 0      

    describe "boolean eq" $ do 
      it "12-1" $ int_of_comp bool_prog12 [0,0] `shouldBe` 1
      it "12-2" $ int_of_comp bool_prog12 [0,1] `shouldBe` 0
      it "12-3" $ int_of_comp bool_prog12 [1,0] `shouldBe` 0
      it "12-4" $ int_of_comp bool_prog12 [1,1] `shouldBe` 1      

    describe "bool inputs" $ do
      it "16-1" $ int_of_comp bool_prog16 (take 100 $ repeat 1) `shouldBe` 0

    describe "array" $ do
      it "17-1" $ int_of_comp bool_prog17 [] `shouldBe` 1

    describe "input array" $ do
      it "18-1" $ int_of_comp bool_prog18 [0,1,0,1,0,1,0,1] `shouldBe` 1

    describe "products" $ do
      it "19-1" $ int_of_comp bool_prog19 [1,1] `shouldBe` 1
      it "20-1" $ int_of_comp bool_prog20 [1,1] `shouldBe` 1
      it "21-1" $ int_of_comp bool_prog21 [0,1] `shouldBe` 0     

    describe "products" $ do
      it "22-1" $ int_of_comp bool_prog22 [0,1] `shouldBe` 1
      it "23-1" $ int_of_comp bool_prog23 [0,1] `shouldBe` 0

    describe "peano" $ do
      it "24-1" $ int_of_comp bool_prog24 [] `shouldBe` 1

    describe "lam" $ do
      it "25-1" $ int_of_comp bool_prog25 [] `shouldBe` 1

    describe "zeq" $ do
      it "32-1" $ int_of_comp bool_prog32 [0] `shouldBe` 1
      it "32-2" $ int_of_comp bool_prog32 [1] `shouldBe` 0
      it "32-3" $ int_of_comp bool_prog32 [2] `shouldBe` 0 

    describe "eq" $ do
      it "33-1" $ int_of_comp bool_prog33 [23,44] `shouldBe` 0
      it "33-2" $ int_of_comp bool_prog33 [0,100] `shouldBe` 0
      it "33-3" $ int_of_comp bool_prog33 [0,0] `shouldBe` 1
      it "33-3" $ int_of_comp bool_prog33 [100,100] `shouldBe` 1
      it "33-3" $ int_of_comp bool_prog33 [-33,44] `shouldBe` 0
      it "33-3" $ int_of_comp bool_prog33 [-1,-1] `shouldBe` 1
    
  describe "Keccak Tests" $ do

    describe "keccak" $ do 
      it "keccak-2" $ int_of_comp (keccak1 2) input_vals `shouldBe` 1
      it "keccak-2" $ int_of_comp (keccak1 5) input_vals `shouldBe` 0     
