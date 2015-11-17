{-# LANGUAGE RebindableSyntax
           , DataKinds
           , GADTs
           , KindSignatures
           , RankNTypes
           , ScopedTypeVariables
  #-}

module Games where

import Prelude hiding
  ( (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , (&&)        
  , return
  , fromRational
  , negate    
  )

import Data.Typeable

import Errors
import Syntax
import SyntaxMonad
import TExpr
import Toplevel

{---------------------------------------------------------
  See Vytiniotis & Kennedy,
  "Functional Pearl: Every Bit Counts", ICFP 2010
 ---------------------------------------------------------}

data ISO (t :: Ty) (s :: Ty) =
  Iso { to   :: TExp t Rational -> Comp s
      , from :: TExp s Rational -> Comp t
      }

data Game :: Ty -> * where
  Single :: forall (s :: Ty) (t :: Ty).
            ( Typeable s
            , Typeable t
            )
         => ISO t s -> Game t
  Split  :: forall (t1 :: Ty) (t2 :: Ty) (t :: Ty).
            ( Typeable t1
            , Typeable t2
            , Typeable t
            , Zippable t1
            , Zippable t2              
            , Zippable t
            , Derive t1
            , Derive t2              
            )
         => ISO t ('TSum t1 t2) -> Game t1 -> Game t2 -> Game t

decode :: Game t -> Comp t
decode (Single (Iso _ bld))
  = do { x <- fresh_input
       ; bld x
       }
decode (Split (Iso _ bld) g1 g2)
  = do { x <- fresh_input
       ; e1 <- decode g1
       ; e2 <- decode g2
       ; s1 <- inl e1
       ; s2 <- inr e2
       ; v1 <- bld s1
       ; v2 <- bld s2
       ; if return x then return v2 else return v1
       }

field_game :: Game 'TField
field_game = Single (Iso return return)

bool_game :: Game 'TBool
bool_game = Single (Iso (\be -> if return be then return 1.0 else return 0.0)
                        (\te -> if return (zeq te) then return false else return true))

unit_game :: Game 'TUnit
unit_game = Single (Iso (\_ -> return 1.0) (\_ -> return unit))

fail_game :: Typeable ty => Game ty
fail_game = Single (Iso (\_ -> fail_with $ ErrMsg "fail-games can't encode")
                        (\(_ :: TExp 'TField Rational) ->
                                fail_with $ ErrMsg "fail-games can't decode"))

sum_game :: ( Typeable t1
            , Typeable t2
            , Zippable t1
            , Zippable t2
            , Derive t1
            , Derive t2
            )
         => Game t1
         -> Game t2
         -> Game ('TSum t1 t2)
sum_game g1 g2
  = Split (Iso return return) g1 g2
    
basic_game :: Game ('TSum 'TField 'TField)
basic_game = sum_game field_game field_game

basic_test :: Comp 'TField
basic_test
  = do { s <- decode basic_game
       ; case_sum return return s
       }

t1 = comp_interp basic_test [0,23,88] -- 23
t2 = comp_interp basic_test [1,23,88] -- 88

(+>) :: ( Typeable t
        , Typeable s
        , Zippable t
        , Zippable s
        )
     => Game t -> ISO s t -> Game s
(Single j) +> i      = Single (i `seqI` j)
(Split j g1 g2) +> i = Split  (i `seqI` j) g1 g2

idI :: ISO a a
idI = Iso return return

prodI :: ( Typeable a
         , Typeable b
         , Typeable c
         , Typeable d )
      => ISO a b
      -> ISO c d
      -> ISO ('TProd a c) ('TProd b d)
prodI (Iso f g) (Iso f' g')
  = Iso (\p -> do
            x1 <- fst_pair p
            x2 <- snd_pair p
            y1 <- f x1
            y2 <- f' x2
            pair y1 y2)
        (\p -> do
            x1 <- fst_pair p
            x2 <- snd_pair p
            y1 <- g x1
            y2 <- g' x2
            pair y1 y2)

seqI :: Typeable b => ISO a b -> ISO b c -> ISO a c
seqI (Iso f g) (Iso f' g') = Iso (\a -> f a >>= f') (\c -> g' c >>= g)

prodLInputI :: ( Typeable a
               , Typeable b
               )
            => ISO ('TProd a b) b
prodLInputI
  = Iso snd_pair
        (\b -> do
            a <- fresh_input
            pair a b)

prodLSumI :: ( Typeable a
             , Typeable b
             , Typeable c
             , Zippable a
             , Zippable b
             , Zippable c
             , Derive a
             , Derive b
             , Derive c
             )
          => ISO ('TProd ('TSum b c) a) ('TSum ('TProd b a) ('TProd c a))
prodLSumI 
  = Iso (\p -> do
            xbc <- fst_pair p
            xa  <- snd_pair p
            case_sum
              (\xb -> do
                  p' <- pair xb xa
                  inl p')
              (\xc -> do
                  p' <- pair xc xa
                  inr p')
              xbc)
        (\s -> do
            case_sum
              (\pba -> do
                  a  <- snd_pair pba
                  b  <- fst_pair pba
                  sb <- inl b
                  pair sb a)
              (\pca -> do
                  a  <- snd_pair pca
                  c  <- fst_pair pca
                  sc <- inr c
                  pair sc a)
              s)

prod_game :: ( Typeable b
             , Zippable a
             , Zippable b
             , Derive a
             , Derive b
             )
          => Game a -> Game b -> Game ('TProd a b)
prod_game (Single iso) g2 = g2 +> iso'
  where iso' = prodI iso idI `seqI` prodLInputI
prod_game (Split iso g1a g1b) g2
  = Split iso' (prod_game g1a g2) (prod_game g1b g2)
  where iso' = prodI iso idI `seqI` prodLSumI

basic_game2 :: Game ('TProd 'TField 'TField)
basic_game2 = prod_game field_game field_game

basic_test2 :: Comp 'TField
basic_test2
  = do { p <- decode basic_game2
       ; fst_pair p
       }

t3 = comp_interp basic_test2 [88,23] -- fst (23, 88) = 23

basic_game3 :: Game ('TProd ('TProd 'TField 'TField) 'TField)
basic_game3
  = prod_game (prod_game field_game field_game)
              field_game

basic_test3 :: Comp 'TField
basic_test3
  = do { p <- decode basic_game3
       ; p2 <- fst_pair p
       ; snd_pair p2
       }

t4 = comp_interp basic_test3 [0,1,2]
  
{---------------------------------------------------------
  Generic Games
 ---------------------------------------------------------}

class Gameable (a :: Ty) where
  mkGame :: Game a

instance Gameable 'TField where
  mkGame = field_game

instance Gameable 'TBool where
  mkGame = bool_game

instance Gameable 'TUnit where
  mkGame = unit_game

instance ( Typeable a
         , Typeable b
         , Zippable a
         , Zippable b
         , Derive a
         , Derive b
         , Gameable a
         , Gameable b
         )
      => Gameable ('TProd a b) where
  mkGame = prod_game mkGame mkGame
     
instance ( Typeable a
         , Typeable b
         , Zippable a
         , Zippable b
         , Derive a
         , Derive b
         , Gameable a
         , Gameable b
         )
      => Gameable ('TSum a b) where
  mkGame = sum_game mkGame mkGame

gdecode :: Gameable t => Comp t
gdecode = decode mkGame


  
     


