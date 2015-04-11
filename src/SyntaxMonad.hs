{-# LANGUAGE RebindableSyntax
           , DataKinds
           , ScopedTypeVariables
           , PolyKinds
  #-}

module SyntaxMonad
  ( -- | Computation monad
    Comp
  , CompResult
  , runState
  , ret
  , return
  , (>>=)
  , (>>)
  , raise_err
  , Env(..)    
  , State(..)
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

import Data.Typeable

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import Common
import Errors
import TExpr

----------------------------------------------------
--
-- State Monad
--        
----------------------------------------------------        

type CompResult s a = Either ErrMsg (a,s)

data State s a = State (s -> CompResult s a)

-- | At "parse" time, we maintain an environment containing
--    (i) next_var: the next free variable
--    (ii) obj_map: a symbol table mapping (obj_var,integer index) to
--    the constraint variable associated with that object, at
--    that field index.
--  Reading from object 'a' at index 'i' (x := a_i) corresponds to:
--    (a) getting y <- obj_map(a,i)
--    (b) inserting the constraint (x = y)

type ObjMap
  = Map.Map ( Var -- object a
            , Int -- at index i
            )
            Var -- maps to variable x

data Env = Env { next_var :: Int
               , input_vars :: [Int]
               , obj_map :: ObjMap
               , bots :: Set.Set Var 
               , guards :: Map.Map Var Bool
               }
           deriving Show

type Comp ty = State Env (TExp ty Rational)

runState :: State s a -> s -> CompResult s a
runState mf s = case mf of
  State f -> f s

raise_err :: ErrMsg -> Comp ty
raise_err msg = State (\_ -> Left msg)

-- | We have to define our own bind operator, unfortunately,
-- because the "result" that's returned is the sequential composition
-- of the results of 'mf', 'g' (not just whatever 'g' returns)
(>>=) :: forall (ty1 :: Ty) (ty2 :: Ty) s a.
         Typeable ty1
      => State s (TExp ty1 a)
      -> (TExp ty1 a -> State s (TExp ty2 a))
      -> State s (TExp ty2 a)
(>>=) mf g = State (\s ->
  case runState mf s of
    Left err -> Left err
    Right (e,s') ->
      case runState (g e) s' of
        Left err -> Left err
        Right (e',s'') -> Right (te_seq e e',s''))

(>>) :: forall (ty1 :: Ty) (ty2 :: Ty) s a.
        Typeable ty1
     => State s (TExp ty1 a)
     -> State s (TExp ty2 a)
     -> State s (TExp ty2 a)
(>>) mf g = do { _ <- mf; g }    


return :: a -> State s a
return e = State (\s -> Right (e,s))

ret :: a -> State s a
ret = return
