{-# LANGUAGE GADTs
           , RebindableSyntax
           , DataKinds
           , RankNTypes
           , KindSignatures
           , ScopedTypeVariables
           , FlexibleContexts
           , UndecidableInstances
           , PolyKinds
  #-}

module Syntax
       ( Zippable
       , Derive

         -- | Sums, products, recursive types
       , inl
       , inr
       , case_sum
       , pair
       , fst_pair
       , snd_pair
       , roll
       , unroll
       , fixN
       , fix
         
         -- | Arithmetic and boolean operations 
       , (+)
       , (-)
       , (*)
       , (/)
       , (&&)
       , bor
       , zeq
       , not
       , xor
       , eq
       , beq
       , exp_of_int
       , int_of_exp
       , inc
       , dec
       , fromRational
       , ifThenElse
       , negate

         -- | Arrays
       , arr
       , arr2
       , arr3
       , input_arr
       , input_arr2
       , input_arr3
       , set
       , set2
       , set3
       , set4
       , get
       , get2
       , get3
       , get4

         -- | Iteration
       , iter
       , iterM
       , bigsum
       , times
       , forall
       , forall2
       , forall3
       ) where

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

import Data.Typeable

import Unsafe.Coerce

import Common
import Errors
import R1CS
import TExpr
import SyntaxMonad

inc :: Int -> Int
inc n = (P.+) n 1

dec :: Int -> Int
dec n = (P.-) n 1

----------------------------------------------------
--
-- Arrays
--        
----------------------------------------------------        

-- | 2-d arrays. 'width' is the size, in "bits" (#field elements), of
-- each array element.
arr2 :: Typeable ty => Int -> Int -> Comp ('TArr ('TArr ty))
arr2 len width
  = do { a <- arr len
       ; forall [0..dec len] (\i ->
           do { ai <- arr width
              ; set (a,i) ai
              })
       ; return a
       }

-- | 3-d arrays.
arr3 :: Typeable ty => Int -> Int -> Int -> Comp ('TArr ('TArr ('TArr ty)))
arr3 len width height
  = do { a <- arr2 len width
       ; forall2 ([0..dec len],[0..dec width]) (\i j ->
           do { aij <- arr height
              ; set2 (a,i,j) aij
              })
       ; return a
       }

input_arr2 :: Typeable ty => Int -> Int -> Comp ('TArr ('TArr ty))
input_arr2 0 _ = raise_err $ ErrMsg "array must have size > 0"
input_arr2 len width
  = do { a <- arr len
       ; forall [0..dec len] (\i ->
           do { ai <- input_arr width
              ; set (a,i) ai
              })
       ; return a
       }

input_arr3 :: Typeable ty => Int -> Int -> Int -> Comp ('TArr ('TArr ('TArr ty)))
input_arr3 len width height
  = do { a <- arr2 len width
       ; forall2 ([0..dec len],[0..dec width]) (\i j ->
           do { aij <- input_arr height
              ; set2 (a,i,j) aij
              })
       ; return a
       }

set2 (a,i,j) e     = do { a' <- get (a,i); set (a',j) e }
set3 (a,i,j,k) e   = do { a' <- get2 (a,i,j); set (a',k) e }
set4 (a,i,j,k,l) e = do { a' <- get3 (a,i,j,k); set (a',l) e }

get2 (a,i,j)       = do { a' <- get (a,i); get (a',j) }
get3 (a,i,j,k)     = do { a' <- get2 (a,i,j); get (a',k) }
get4 (a,i,j,k,l)   = do { a' <- get3 (a,i,j,k); get (a',l) }

----------------------------------------------------
--
-- Sums
--        
----------------------------------------------------        

rep_sum :: TExp ('TSum ty1 ty2) Rational
        -> TExp ('TProd 'TBool ('TProd ty1 ty2)) Rational
rep_sum = unsafe_cast

unrep_sum :: TExp ('TProd 'TBool ('TProd ty1 ty2)) Rational
          -> TExp ('TSum ty1 ty2) Rational
unrep_sum = unsafe_cast

inl :: forall ty1 ty2.
       ( Typeable ty1
       , Typeable ty2
       )
    => TExp ty1 Rational
    -> Comp ('TSum ty1 ty2)
inl te1
  = do { let v2 = TEBot
       ; y <- pair te1 v2
       ; v2_var <- snd_pair y
       ; assert_bot v2_var
       ; z <- pair (TEVal VFalse) y
       ; z_fst <- fst_pair z
       ; assert_false z_fst
       ; return $ unrep_sum z
       }

inr :: forall ty1 ty2.
       ( Typeable ty1
       , Typeable ty2
       )
    => TExp ty2 Rational
    -> Comp ('TSum ty1 ty2)
inr te2
  = do { let v1 = TEBot
       ; y <- pair v1 te2
       ; v1_var <- fst_pair y
       ; assert_bot v1_var
       ; z <- pair (TEVal VTrue) y
       ; z_fst <- fst_pair z
       ; assert_true z_fst
       ; return $ unrep_sum z
       }

case_sum :: forall ty1 ty2 ty.
            ( Typeable ty1
            , Typeable ty2
            , Typeable ty
            , Zippable ty
            )
         => (TExp ty1 Rational -> Comp ty)
         -> (TExp ty2 Rational -> Comp ty)
         -> TExp ('TSum ty1 ty2) Rational
         -> Comp ty
case_sum f1 f2 e
  = do { let p = rep_sum e
       ; b <- fst_pair p
       ; is_inl <- is_false b              
       ; is_inr <- is_true b
       ; p_rest <- snd_pair p
       ; e1 <- fst_pair p_rest
       ; e2 <- snd_pair p_rest
       ; case is_inl of
           TEVal VTrue -> f1 e1
           _ -> case is_inr of
             TEVal VTrue -> f2 e2
             _ -> do { le <- f1 e1
                     ; re <- f2 e2
                       -- NOTE: should not guard b here.
                       -- zip_vals ... must maintain SyntaxMonad [INVARIANT]
                       -- regarding the representation of nonbase-type expressions.
                     ; zip_vals (not b) le re
                     }
       }

-- | Types for which a default value is derivable
class Derive ty where
  derive :: Int -> Comp ty

instance Derive 'TUnit where
  derive _ = return $ TEVal VUnit

instance Derive 'TBool where
  derive _ = return $ TEVal VFalse

instance Derive 'TField where
  derive _ = return $ TEVal (VField 0)

instance (Typeable ty,Derive ty) => Derive ('TArr ty) where
  derive n
    = do { a <- arr 1
         ; v <- derive n
         ; set (a,0) v
         ; return a
         }

instance ( Typeable ty1
         , Derive ty1
         , Typeable ty2
         , Derive ty2
         )
      => Derive ('TProd ty1 ty2) where
  derive n
    = do { v1 <- derive n
         ; v2 <- derive n
         ; pair v1 v2
         }

instance ( Typeable ty1
         , Derive ty1
         , Typeable ty2
         , Derive ty2
         )
      => Derive ('TSum ty1 ty2) where
  derive n
    = do { v1 <- derive n
         ; inl v1
         }

instance ( Typeable f
         , Typeable (Rep f ('TMu f))   
         , Derive (Rep f ('TMu f))
         )
      => Derive ('TMu f) where
  derive n
    | n > 0
    = do { v1 <- derive (dec n)
         ; roll v1
         }

    | otherwise
    = do { x <- fresh_var
         ; assert_bot x
         ; return x
         } 

-- | Types for which conditional branches can be pushed to the leaves
-- of two values.
class Zippable ty where
  zip_vals :: TExp 'TBool Rational
           -> TExp ty Rational
           -> TExp ty Rational
           -> Comp ty

instance Zippable 'TUnit where
  zip_vals _ _ _ = return unit

zip_base TEBot _ _  = return TEBot
zip_base _ TEBot e2 = return e2
zip_base _ e1 TEBot = return e1
zip_base b e1 e2
  = do { b_true <- is_true b
       ; b_false <- is_false b
       ; case (b_true,b_false) of
           (TEVal VTrue,_) -> return e1
           (_,TEVal VTrue) -> return e2
           _ -> guard (\b0 -> 
                  do { e1_bot <- is_bot e1
                     ; e2_bot <- is_bot e2
                     ; case (e1_bot,e2_bot) of
                         (TEVal VTrue,_) -> return e2
                         (_,TEVal VTrue) -> return e1
                         _ -> return $ ifThenElse_aux b0 e1 e2
                     }) b
        }

instance Zippable 'TBool where
  zip_vals b b1 b2 = zip_base b b1 b2

instance Zippable 'TField where
  zip_vals b e1 e2 = zip_base b e1 e2

fuel :: Int
fuel = 1

check_bots :: ( Typeable ty
              , Derive ty
              )
           => Comp ty
           -> TExp 'TBool Rational
           -> TExp ty Rational
           -> TExp ty Rational
           -> Comp ty
check_bots f b e1 e2
  = do { b_true <- is_true b
       ; b_false <- is_false b
       ; b_bot  <- is_bot b
       ; e1_bot <- is_bot e1
       ; e2_bot <- is_bot e2
       ; case (b_true,b_false,b_bot,e1_bot,e2_bot) of
           (TEVal VTrue,_,_,_,_) -> return e1
           (_,TEVal VTrue,_,_,_) -> return e2
           (_,_,TEVal VTrue,_,_) -> derive fuel
           (_,_,_,TEVal VTrue,TEVal VTrue) -> derive fuel
           (_,_,_,TEVal VTrue,TEVal VFalse) -> return e2
           (_,_,_,TEVal VFalse,TEVal VTrue) -> return e1
           (_,_,_,TEVal VFalse,TEVal VFalse) -> f
           (_,_,_,_,_) -> raise_err $ ErrMsg "internal error in check_bots"
       }

instance ( Zippable ty1
         , Typeable ty1
         , Derive ty1
         , Zippable ty2
         , Typeable ty2
         , Derive ty2
         )
      => Zippable ('TProd ty1 ty2) where
  zip_vals b e1 e2 = check_bots f b e1 e2
    where f = do { e11 <- fst_pair e1
                 ; e12 <- snd_pair e1
                 ; e21 <- fst_pair e2
                 ; e22 <- snd_pair e2
                 ; p1 <- zip_vals b e11 e21
                 ; p2 <- zip_vals b e12 e22
                 ; pair p1 p2
                 }

instance ( Zippable ty1
         , Typeable ty1
         , Derive ty1
         , Zippable ty2
         , Typeable ty2
         , Derive ty2
         )
      => Zippable ('TSum ty1 ty2) where
  zip_vals b e1 e2 = check_bots f b e1 e2
    where f = do { let p1 = rep_sum e1 
                 ; let p2 = rep_sum e2 
                 ; p' <- zip_vals b p1 p2
                 ; return $ unrep_sum p'
                 }

instance ( Typeable f
         , Typeable (Rep f ('TMu f))
         , Zippable (Rep f ('TMu f))
         , Derive (Rep f ('TMu f))
         )
      => Zippable ('TMu f) where
  zip_vals b e1 e2 = check_bots f b e1 e2
    where f = do { e1' <- unroll e1
                 ; e2' <- unroll e2
                 ; x <- zip_vals b e1' e2'
                 ; roll x
                 }


----------------------------------------------------
--
-- Recursive Types
--        
----------------------------------------------------        

unsafe_cast :: TExp ty1 Rational -> TExp ty2 Rational
unsafe_cast = unsafeCoerce

unroll :: ( Typeable (Rep f ('TMu f))
          )  
       => TExp ('TMu f) Rational
       -> Comp (Rep f ('TMu f))
unroll te = return $ unsafe_cast te

roll :: ( Typeable f
        , Typeable (Rep f ('TMu f))
        )
     => TExp (Rep f ('TMu f)) Rational
     -> Comp ('TMu f)
roll te = return $ unsafe_cast te
             
fixN :: Typeable ty2
     => Int -> 
        ((TExp ty1 Rational -> Comp ty2)
        -> TExp ty1 Rational
        -> Comp ty2)
     -> TExp ty1 Rational
     -> Comp ty2
fixN depth f e = go depth e
  where -- WARNING: We only handle inductive data up to size 'depth'.
        go 0 _ = return TEBot
        go n e0 = f (go (dec n)) e0

fix :: Typeable ty2
     => ((TExp ty1 Rational -> Comp ty2)
        -> TExp ty1 Rational
        -> Comp ty2)
     -> TExp ty1 Rational
     -> Comp ty2
fix = fixN 100

----------------------------------------------------
--
-- Operators, Values
--        
----------------------------------------------------        

(+) :: TExp 'TField Rational -> TExp 'TField Rational -> TExp 'TField Rational
(+) e1 e2 = TEBinop (TOp Add) e1 e2

(-) :: TExp 'TField Rational -> TExp 'TField Rational -> TExp 'TField Rational
(-) e1 e2 = TEBinop (TOp Sub) e1 e2

(*) :: TExp 'TField Rational -> TExp 'TField Rational -> TExp 'TField Rational
(*) e1 e2 = TEBinop (TOp Mult) e1 e2

(/) :: TExp 'TField Rational -> TExp 'TField Rational -> TExp 'TField Rational
(/) e1 e2 = TEBinop (TOp Div) e1 e2

(&&) :: TExp 'TBool Rational -> TExp 'TBool Rational -> TExp 'TBool Rational
(&&) e1 e2 = TEBinop (TOp And) e1 e2

bor :: TExp 'TBool Rational -> TExp 'TBool Rational -> TExp 'TBool Rational
bor e1 e2 = TEBinop (TOp Or) e1 e2

zeq :: TExp 'TField Rational -> TExp 'TBool Rational
zeq e = TEUnop (TUnop ZEq) e

not :: TExp 'TBool Rational -> TExp 'TBool Rational
not e = ifThenElse_aux e false true

xor :: TExp 'TBool Rational -> TExp 'TBool Rational -> TExp 'TBool Rational
xor e1 e2 = TEBinop (TOp XOr) e1 e2

beq :: TExp 'TBool Rational -> TExp 'TBool Rational -> TExp 'TBool Rational
beq e1 e2 = TEBinop (TOp BEq) e1 e2

eq :: Typeable ty => TExp ty Rational -> TExp ty Rational -> TExp 'TBool Rational
eq e1 e2 = TEBinop (TOp Eq) e1 e2

fromRational :: Rational -> TExp 'TField Rational
fromRational r = TEVal (VField (r :: Rational))

exp_of_int :: Int -> TExp 'TField Rational
exp_of_int i = TEVal (VField $ fromIntegral i)

int_of_exp :: TExp 'TField Rational -> Int
int_of_exp e = case e of
  TEVal (VField r) -> truncate r
  _ -> fail_with $ ErrMsg $ "expected field elem " ++ show e

ifThenElse_aux :: Field a
               => TExp 'TBool a -> TExp ty a -> TExp ty a -> TExp ty a
ifThenElse_aux b e1 e2
  | e1 == e2
  = e1    

  | otherwise
  = case b of
      TEVal VFalse -> e2
      TEVal VTrue -> e1
      _ -> TEIf b e1 e2

ifThenElse :: ( Zippable ty
              , Typeable ty
              )
           => Comp 'TBool
           -> Comp ty
           -> Comp ty 
           -> Comp ty
ifThenElse cb c1 c2
  = do { b <- cb
       ; e1 <- c1
       ; e2 <- c2
       ; zip_vals b e1 e2
       }

negate :: TExp 'TField Rational -> TExp 'TField Rational
negate e = -1.0 * e

----------------------------------------------------
--
-- Iteration
--        
----------------------------------------------------        

iter :: Typeable ty
     => Int
     -> (Int -> TExp ty Rational -> TExp ty Rational)
     -> TExp ty Rational
     -> TExp ty Rational
iter n f e = g n f e
  where g 0 f' e' = f' 0 e'
        g m f' e' = f' m $ g (dec m) f' e'

iterM :: Typeable ty
      => Int
      -> (Int -> TExp ty Rational -> Comp ty)
      -> TExp ty Rational
      -> Comp ty
iterM n mf e = g n mf e
  where g 0 mf' e' = mf' 0 e'
        g m mf' e'
          = do { x <- g (dec m) mf' e'
               ; mf' m x
               }

bigsum :: Int
       -> (Int -> TExp 'TField Rational)
       -> TExp 'TField Rational
bigsum n f = iter n (\n' e -> f n' + e) 0.0

forall :: [a]
       -> (a -> Comp 'TUnit)
       -> Comp 'TUnit
forall as mf = g as mf
  where g [] _ = return unit
        g (a : as') mf'
          = do { _ <- mf' a; g as' mf' }

forall2 (as1,as2) mf
  = forall as1 (\a1 -> forall as2 (\a2 -> mf a1 a2))
forall3 (as1,as2,as3) mf
  = forall2 (as1,as2) (\a1 a2 -> forall as3 (\a3 -> mf a1 a2 a3))

times :: Int
      -> Comp 'TUnit
      -> Comp 'TUnit
times n mf = forall [0..dec n] (const mf)


