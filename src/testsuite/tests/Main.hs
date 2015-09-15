module Main where

import Test.Hspec

import Keccak
import Toplevel
import UnitTests

main :: IO ()
main = hspec $ do

  describe "Field Tests" $ do

    describe "if-then-else" $ do 
      it "1-1" $ test_comp prog1 [1,2,1] `shouldReturn` Right (negate 240)

    describe "bigsum" $ do
      it "2-1" $ test_comp (prog2 4) [0] `shouldReturn` Right 10
      it "2-2" $ test_comp (prog2 4) [1] `shouldReturn` Right 15
      it "2-3" $ test_comp (prog2 4) [2] `shouldReturn` Right 20
      it "2-4" $ test_comp (prog2 10) [10] `shouldReturn` Right 165

    describe "arrays" $ do
      it "3-1" $ test_comp prog3 [8]  `shouldReturn` Right 512
      it "3-2" $ test_comp prog3 [16] `shouldReturn` Right 4096
      it "3-3" $ test_comp prog3 [0]  `shouldReturn` Right 0
      it "3-4" $ test_comp prog3 [-1] `shouldReturn` Right (-1)

      it "4-1" $ test_comp prog4 [8]  `shouldReturn` Right 512
      it "4-2" $ test_comp prog4 [16] `shouldReturn` Right 4096
      it "4-3" $ test_comp prog4 [0]  `shouldReturn` Right 0
      it "4-4" $ test_comp prog4 [-1] `shouldReturn` Right (-1)

      it "5-1" $ test_comp prog5 [8]  `shouldReturn` Right (8^(101::Integer))
      it "5-2" $ test_comp prog5 [16] `shouldReturn` Right (16^(101::Integer))
      it "5-3" $ test_comp prog5 [0]  `shouldReturn` Right 0
      it "5-4" $ test_comp prog5 [-1] `shouldReturn` Right (-1)

    describe "times" $ do
      it "6-1" $ test_comp prog6 [8]  `shouldReturn` Right 8

    describe "forall" $ do
      it "7-1" $ test_comp prog7 []   `shouldReturn` Right 100

    describe "forall2" $ do
      it "8-1" $ test_comp prog8 []   `shouldReturn` Right 29

    describe "unused inputs" $ do
      it "11-1" $ test_comp prog11 [1,1] `shouldReturn` Right 1

    describe "multiplicative identity" $ do
      it "13-1" $ test_comp prog13 [1] `shouldReturn` Right 1

    describe "opt: 0x * 3y = out ~~> out=0" $ do
      it "14-1" $ test_comp prog14 [3,4] `shouldReturn` Right 0

    describe "exp_binop smart constructor: 3 - (2 - 1) = 2" $ do
      it "15-1" $ test_comp prog15 [] `shouldReturn` Right 2

    describe "lists" $ do
      it "26-1" $ test_comp prog26 [] `shouldReturn` Right 33
      it "27-1" $ test_comp prog27 [] `shouldReturn` Right 34
      it "28-1" $ test_comp prog28 [] `shouldReturn` Right 24
      it "29-1" $ test_comp prog29 [1] `shouldReturn` Right 24
      it "30-1" $ test_comp prog30 [] `shouldReturn` Right 24
      
    describe "div" $ do
      it "31-1" $ test_comp prog31 [4,2] `shouldReturn` Right 2
      it "31-1" $ test_comp prog31 [4,1] `shouldReturn` Right 4
      it "31-1" $ test_comp prog31 [4,4] `shouldReturn` Right 1
      it "31-1" $ test_comp prog31 [21,7] `shouldReturn` Right 3

    describe "beta" $ do 
      it "34-1" $ test_comp prog34 [] `shouldReturn` Right 0

    describe "list" $ do 
      it "35-1" $ test_comp prog35 [] `shouldReturn` Right 77

  describe "Boolean Tests" $ do

    describe "and" $ do 
      it "9-1" $ test_comp bool_prog9 [0,0] `shouldReturn` Right 0
      it "9-2" $ test_comp bool_prog9 [0,1] `shouldReturn` Right 0
      it "9-3" $ test_comp bool_prog9 [1,0] `shouldReturn` Right 0
      it "9-4" $ test_comp bool_prog9 [1,1] `shouldReturn` Right 1      

    describe "xor" $ do 
      it "10-1" $ test_comp bool_prog10 [0,0] `shouldReturn` Right 0
      it "10-2" $ test_comp bool_prog10 [0,1] `shouldReturn` Right 1
      it "10-3" $ test_comp bool_prog10 [1,0] `shouldReturn` Right 1
      it "10-4" $ test_comp bool_prog10 [1,1] `shouldReturn` Right 0      

    describe "boolean eq" $ do 
      it "12-1" $ test_comp bool_prog12 [0,0] `shouldReturn` Right 1
      it "12-2" $ test_comp bool_prog12 [0,1] `shouldReturn` Right 0
      it "12-3" $ test_comp bool_prog12 [1,0] `shouldReturn` Right 0
      it "12-4" $ test_comp bool_prog12 [1,1] `shouldReturn` Right 1      

    describe "bool inputs" $ do
      it "16-1" $ test_comp bool_prog16 (take 100 $ repeat 1) `shouldReturn` Right 0

    describe "array" $ do
      it "17-1" $ test_comp bool_prog17 [] `shouldReturn` Right 1

    describe "input array" $ do
      it "18-1" $ test_comp bool_prog18 [0,1,0,1,0,1,0,1] `shouldReturn` Right 1

    describe "products" $ do
      it "19-1" $ test_comp bool_prog19 [1,1] `shouldReturn` Right 1
      it "20-1" $ test_comp bool_prog20 [1,1] `shouldReturn` Right 1
      it "21-1" $ test_comp bool_prog21 [0,1] `shouldReturn` Right 0     

    describe "products" $ do
      it "22-1" $ test_comp bool_prog22 [0,1] `shouldReturn` Right 1
      it "23-1" $ test_comp bool_prog23 [0,1] `shouldReturn` Right 0

    describe "peano" $ do
      it "24-1" $ test_comp bool_prog24 [] `shouldReturn` Right 1

    describe "lam" $ do
      it "25-1" $ test_comp bool_prog25 [] `shouldReturn` Right 1

    describe "zeq" $ do
      it "32-1" $ test_comp bool_prog32 [0] `shouldReturn` Right 1
      it "32-2" $ test_comp bool_prog32 [1] `shouldReturn` Right 0
      it "32-3" $ test_comp bool_prog32 [2] `shouldReturn` Right 0 

    describe "eq" $ do
      it "33-1" $ test_comp bool_prog33 [23,44] `shouldReturn` Right 0
      it "33-2" $ test_comp bool_prog33 [0,100] `shouldReturn` Right 0
      it "33-3" $ test_comp bool_prog33 [0,0] `shouldReturn` Right 1
      it "33-3" $ test_comp bool_prog33 [100,100] `shouldReturn` Right 1
      it "33-3" $ test_comp bool_prog33 [-33,44] `shouldReturn` Right 0
      it "33-3" $ test_comp bool_prog33 [-1,-1] `shouldReturn` Right 1

    describe "sum" $ do
      it "36-1" $ test_comp prog36 [0] `shouldReturn` Right 10
      it "36-2" $ test_comp prog36 [1] `shouldReturn` Right 7
    
  describe "Keccak Tests" $ do

    describe "keccak" $ do 
      it "keccak-2" $ test_comp (keccak1 2) input_vals `shouldReturn` Right 1
      it "keccak-2" $ test_comp (keccak1 5) input_vals `shouldReturn` Right 0     

