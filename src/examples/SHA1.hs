{-# LANGUAGE RebindableSyntax,DataKinds #-}

module SHA1 where

import Prelude hiding 
  ( (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , (&&)        
  , not
  , return
  , fromRational
  , negate
  )
import qualified Prelude as P

import Syntax
import TExpr
import Toplevel
import Compile

wordsize = 32

rot_index :: Int -- rotate index 'i'
          -> Int -- by 'n' (mod lane width)
          -> Int
rot_index i n = ((P.+) i n) `mod` wordsize

sub :: Int -> Int -> Int
sub i j = (P.-) i j

copy_word dest src = do
  forall [0..dec wordsize] (\i ->
    do b <- get(src,i)
       set(dest,i) b)

copy_word_leftrotate n dest src = do
  forall [0..dec wordsize] (\i ->
    do b <- get(src,i)
       set(dest,rot_index n i) b)

{- UNUSED -}
add_words :: TExp ('TArr 'TBool) Rational
          -> TExp ('TArr 'TBool) Rational
          -> TExp ('TArr 'TBool) Rational
          -> Comp 'TUnit
add_words dest src1 src2 = do
  carry <- arr (inc wordsize)
  set(carry,0) false
  forall [0..dec wordsize] (\i ->
    do c <- get(carry,i)
       s1 <- get(src1,i)
       s2 <- get(src2,i)
       set(carry,inc i) ((c && s1) `bor` (c && s2) `bor` (s1 && s2))
       set(dest,i) (c `xor` s1 `xor` s2))

add_all _ [] = return unit
add_all dest (src : srcs) = do
  add_words dest dest src
  add_all dest srcs
{- END UNUSED -}

leftrotate n dest src = do
  forall [0..dec wordsize] (\i ->
    do s <- get(src,i)
       set(dest,rot_index i n) s)

leftshift n dest src = do
  forall [0..dec wordsize] (\i ->
    do s <- get(src,i)
       set(dest,rot_index i n) s)

sha1 :: TExp ('TArr ('TArr 'TBool)) Rational
     -> Comp ('TArr 'TBool)
sha1 w = do
  a <- arr wordsize
  a_lr <- arr wordsize
  b <- arr wordsize
  c <- arr wordsize
  d <- arr wordsize
  e <- arr wordsize
  f <- arr wordsize
  k <- arr wordsize

  hh <- arr 160 -- 5*wordsize

  -- FIXME: Initializations of a-e,h0-h4
  -- initialize a-h4
  forall [0..dec wordsize] (\i ->
    do set(a,i) false
       set(a_lr,i) false
       set(b,i) false
       set(c,i) false
       set(d,i) false
       set(e,i) false
       set(f,i) false
       set(k,i) false)
  forall [0..159] (\i -> set(hh,i) false)

  -- expand w from 16 to 80 32-bit words
  forall2 ([16..79],[0..dec wordsize]) (\i j -> 
    do w3 <- get2(w,i `sub` 3,j)
       w8 <- get2(w,i `sub` 8,j)
       w14<- get2(w,i `sub` 14,j)
       w16<- get2(w,i `sub` 16,j)        
       set2 (w,i,rot_index j 1) (w3 `xor` w8 `xor` w14 `xor` w16))

  forall [0..19] (\i ->
    do forall [0..dec wordsize] (\j ->
         do b' <- get(b,j)
            c' <- get(c,j)
            d' <- get(d,j)
            set(f,j) (d' `xor` (b' && (c' `xor` d'))))
       loop_body i a a_lr b c d e f k)    

  forall [20..39] (\i ->
    do forall [0..dec wordsize] (\j ->
         do b' <- get(b,j)
            c' <- get(c,j)
            d' <- get(d,j)
            set(f,j) (b' `xor` c' `xor` d'))
       loop_body i a a_lr b c d e f k)

  forall [40..59] (\i ->
    do forall [0..dec wordsize] (\j ->
         do b' <- get(b,j)
            c' <- get(c,j)
            d' <- get(d,j)
            set(f,j) ((b' && c') `bor` (d' && (b' `xor` c'))))
       loop_body i a a_lr b c d e f k)

  forall [60..79] (\i ->
    do forall [0..dec wordsize] (\j ->
         do b' <- get(b,j)
            c' <- get(c,j)
            d' <- get(d,j)
            set(f,j) (b' `xor` c' `xor` d'))
       loop_body i a a_lr b c d e f k)

  -- final message digest (but little-endian, not big-endian)
  copy_word hh e
  copy_word_leftrotate 32 hh d
  copy_word_leftrotate 64 hh c
  copy_word_leftrotate 96 hh b
  copy_word_leftrotate 128 hh a
  return hh

  where loop_body i a a_lr b c d e f k = do
          leftrotate 5 a_lr a
          wi <- get(w,i)
          a_lr' <- arr_to_int32 a_lr
          f' <- arr_to_int32 f
          e' <- arr_to_int32 e
          k' <- arr_to_int32 k
          wi' <- arr_to_int32 wi
          temp <- return $ a_lr' + f' + e' + k' + wi'
          temp' <- int32_to_arr temp
          copy_word e d
          copy_word d c
          copy_word_leftrotate 30 c b
          copy_word b a
          copy_word a temp'

do_sha1 = do
  w <- input_arr2 13 wordsize
  w' <- arr2 80 wordsize
  forall2 ([0..12],[0..dec wordsize]) (\i j ->
    do x <- get2(w,i,j)
       set2(w',i,j) x)
  forall2 ([13..79],[0..dec wordsize]) (\i j ->
    do set2(w',i,j) false)
  hh <- sha1 w'
  get(hh,31)

test1 = length $ r1cs_clauses $ r1cs_of_comp Simplify do_sha1
