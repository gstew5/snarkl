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
import Compile
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

---Test Examples---

stack1
  = do {  
       ;  tl  <- empty_stack
       ;  tl' <- push_stack 15.0 tl
       ;  push_stack 99.0 tl' 
       }
stack2
  = do {  
       ;  tl   <- empty_stack
       ;  tl'  <- push_stack 1.0 tl
       ;  tl'' <- push_stack 12.0 tl'
       ;  push_stack 89.0 tl'' 
       }

--top_stack on empty stack
test_top1
   = do {
        ;  s1  <- stack1
        ;  s2 <- pop_stack s1
        ;  s3 <- pop_stack s2
        ;  top_stack 1.0 s3
        }

--top_stack on non-empty stack
test_top2
   = do {
        ; s1 <- stack1
        ; top_stack 1.0 s1
        }

--is_empty_stack on an empty stack
test_empty_stack1
   = do {
        ; s1 <- stack1
        ; s2 <- pop_stack s1
        ; s3 <- pop_stack s2
        ; is_empty_stack s3
        } 

--is_empty_stack on non-empty stack
test_empty_stack2
   = do {
        ; s1 <- stack1
        ; is_empty_stack s1
        }

