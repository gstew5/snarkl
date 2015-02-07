{-# LANGUAGE RebindableSyntax #-}

module Syntax where

import Prelude hiding 
  ( ifThenElse 
  , (>>)
  , (>>=)
  , (+)
  , (-)    
  , (*)    
  , (/)
  , return
  , fromInteger
  , fromRational
  )
import qualified Prelude as P

import qualified Data.Map.Strict as Map

import Common
import R1CS
import Lang
import Compile

ifThenElse b e1 e2 = EIf b e1 e2

data State s a = State (s -> (a,s))

-- at "parse" time, we maintain an environment containing
--  (i) next_var: the next free variable
--  (ii) arr_map: a symbol table mapping (array_var,index) to
--  the constraint variable associated with that array index.
--  Reading from array x := a[i] corresponds to:
--    (a) getting i <- arr_map(a,i)
--    (b) inserting the constraint (x = i)

type ArrMap = Map.Map (Var,Int) Var

data Env = Env { next_var   :: Int
               , arr_map    :: ArrMap }
           deriving Show

runState :: State s a -> s -> (a,s)
runState mf s = case mf of
  State f -> f s

inc :: Int -> Int
inc n = (P.+) n (P.fromInteger 1)

dec :: Int -> Int
dec n = (P.-) n (P.fromInteger 1)

-- allocate a new internal variable (not instantiated by user)
var :: State Env (Exp Rational)
var = State (\s -> ( EVar (next_var s)
                   , Env (inc (next_var s))
                         (arr_map s)
                   )
            )

-- arrays: initial values currently considered "input", may change
declare_vars :: Int -> State Env (Exp Rational)
declare_vars 0 = error "must declare >= 1 vars"
declare_vars n =
  do { x <- var
     ; g (dec n)
     ; ret x }
  where g 0 = ret EUnit
        g n = var >> g (dec n)

add_arr_bindings :: [((Var,Int),Var)] -> State Env (Exp Rational)
add_arr_bindings bindings
  = State (\s -> case s of
              Env nv m -> ( EUnit 
                          , Env nv (Map.fromList bindings `Map.union` m)
                          )
          )

add_arr_mapping :: Exp Rational -> Int -> State Env (Exp Rational)
add_arr_mapping a sz
  = do { let x = var_of_exp a
       ; let indices  = take sz [(P.fromInteger 0::Int)..]
       ; let arr_vars = map ((P.+) x) indices
       ; add_arr_bindings $ zip (zip (repeat x) indices) arr_vars }

arr :: Int -> State Env (Exp Rational)
arr 0  = error "array must have size > 0"
arr sz = do { a <- declare_vars sz
            ; add_arr_mapping a sz
            ; ret a }

get :: Exp Rational -- select from array a
    -> Int          -- at index i
    -> State Env (Exp Rational) -- result e
get a i
  = let x = var_of_exp a
    in State (\s -> case s of
                 env@(Env nv m) ->
                   case Map.lookup (x,i) m of
                     Just y  -> (EVar y, env)
                     Nothing -> error $ "unbound var " ++ show (x,i)
             )
    
set :: Exp Rational -- update array a
    -> Int          -- at position j
    -> Exp Rational -- to expression e
    -> State Env (Exp Rational)
set a j e
  = let x = var_of_exp a
    in do { le <- var
          ; let y = var_of_exp le
          ; add_arr_bindings [((x,j),y)]
          ; ret $ EAssign le e }

(>>=) :: State s (Exp Rational)
      -> (Exp Rational -> State s (Exp Rational))
      -> State s (Exp Rational)
(>>=) mf g
  = State (\s -> let (e,s') = runState mf s
                     (e',s'') = runState (g e) s'
                 in case e of 
                      EAssign _ _ -> (ESeq e e',s'')
                      _ -> (e',s''))

(>>) mf g = do { _ <- mf; g }    

return :: a -> State s a
return e = State (\s -> (e,s))

ret = return

(+) :: Exp Rational -> Exp Rational -> Exp Rational
(+) e1 e2 = EBinop Add e1 e2

(-) :: Exp Rational -> Exp Rational -> Exp Rational
(-) e1 e2 = EBinop Sub e1 e2

(*) :: Exp Rational -> Exp Rational -> Exp Rational
(*) e1 e2 = EBinop Mult e1 e2

(/) :: Exp Rational -> Exp Rational -> Exp Rational
(/) e1 e2 = EBinop Inv e1 e2

fromRational r = EVal (r :: Rational)

exp_of_int :: Int -> Exp Rational
exp_of_int i = EVal (P.fromIntegral i)

iter :: Int
     -> (Int -> Exp Rational -> Exp Rational)
     -> Exp Rational
     -> Exp Rational
iter 0 f e = f 0 e
iter n f e = f n $ iter ((P.-) n 1) f e

summate :: Int
        -> (Int -> Exp Rational)
        -> Exp Rational
summate n f
  = iter ((P.-) n 1)
    (\i e -> case i == 0 of
        True -> e
        False -> f i + e) (f (0::Int))

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int
         , result :: Rational }
  deriving Show  

check :: State Env (Exp Rational) -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf (Env (P.fromInteger 0) Map.empty)
        nv       = next_var s
        (f,r1cs) = compile_exp nv e
        nw = num_vars r1cs
        ng = num_constraints r1cs
        wit = f inputs
        out = head $ drop nv wit 
    in Result (sat_r1cs wit r1cs) nw ng out
