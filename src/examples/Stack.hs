{-# LANGUAGE RebindableSyntax
           , DataKinds
  #-}

module Stack where

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

import SyntaxMonad
import Syntax
import TExpr
import Toplevel
import List

type TStack a = TList a

type Stack a = TExp (TStack a) Rational

empty_stack :: Typeable a => Comp (TStack a)
empty_stack = nil

push_stack :: Typeable a => TExp a Rational -> Stack a -> Comp (TStack a)
push_stack p q = cons p q

pop_stack :: (Derive a, Zippable a, Typeable a) => Stack a -> Comp (TStack a)
pop_stack f = tail_list f

top_stack :: (Derive a, Zippable a, Typeable a) => TExp a Rational-> Stack a -> Comp  a
top_stack def e = head_list def e

is_empty_stack :: Typeable a => Stack a -> Comp 'TBool
is_empty_stack s =
  case_list s (return true) (\_ _ -> return false)

  
