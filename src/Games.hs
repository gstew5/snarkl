{-# LANGUAGE RebindableSyntax
           , DataKinds
           , GADTs
           , KindSignatures
           , RankNTypes
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

import Syntax
import SyntaxMonad
import TExpr
import Toplevel

{- See Vytiniotis & Kennedy, "Functional Pearl: Every Bit Counts", ICFP 2010 -}

data ISO (t :: Ty) (s :: Ty) =
  Iso { to   :: TExp t Rational -> Comp s
      , from :: TExp s Rational -> Comp t
      }

data Game :: Ty -> * where
  Single :: forall (t :: Ty).
            Typeable t => ISO t t -> Game t
  Split  :: forall (t1 :: Ty) (t2 :: Ty) (t :: Ty).
            ( Typeable t1
            , Typeable t2
            , Typeable t
            , Zippable t
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
       ; if x then v2 else v1
       }

field_game :: Game 'TField
field_game = Single (Iso return return)

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
