{-# LANGUAGE RebindableSyntax #-}

module Syntax where

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
import qualified Prelude as P

import qualified Data.Map.Strict as Map

import Common
import Field
import R1CS
import Lang
import Compile

ifThenElse :: Exp a -> Exp a -> Exp a -> Exp a
ifThenElse b e1 e2 = EIf b e1 e2

data State s a = State (s -> (a,s))

-- | At "parse" time, we maintain an environment containing
--    (i) next_var: the next free variable
--    (ii) arr_map: a symbol table mapping (array_var,index) to
--    the constraint variable associated with that array index.
--  Reading from array x := a[i] corresponds to:
--    (a) getting i <- arr_map(a,i)
--    (b) inserting the constraint (x = i)

type ArrMap = Map.Map (Var,Int) Var

data Env = Env { next_var   :: Int
               , arr_map    :: ArrMap }
           deriving Show

type Comp = State Env (Exp Rational)

runState :: State s a -> s -> (a,s)
runState mf s = case mf of
  State f -> f s

inc :: Int -> Int
inc n = (P.+) n 1

dec :: Int -> Int
dec n = (P.-) n 1

-- | Allocate a new internal variable (not instantiated by user)
var :: Comp
var = State (\s -> ( EVar (next_var s)
                   , Env (inc (next_var s))
                         (arr_map s)
                   )
            )

-- | Arrays: initial values currently considered "input", may change
declare_vars :: Int -> Comp
declare_vars 0 = error "must declare >= 1 vars"
declare_vars n =
  do { x <- var
     ; _ <- g (dec n)
     ; ret x }
  where g 0 = ret EUnit
        g m = var >> g (dec m)

add_arr_bindings :: [((Var,Int),Var)] -> Comp
add_arr_bindings bindings
  = State (\s -> case s of
              Env nv m -> ( EUnit 
                          , Env nv (Map.fromList bindings `Map.union` m)
                          )
          )

add_arr_mapping :: Exp Rational -> Int -> Comp
add_arr_mapping a sz
  = do { let x = var_of_exp a
       ; let indices  = take sz [(0::Int)..]
       ; let arr_vars = map ((P.+) x) indices
       ; add_arr_bindings $ zip (zip (repeat x) indices) arr_vars }

arr :: Int -> Comp
arr 0  = error "array must have size > 0"
arr sz = do { a <- declare_vars sz
            ; _ <- add_arr_mapping a sz
            ; ret a }

get :: ( Exp Rational -- select from array a
       , Int )        -- at index i
    -> Comp -- result e
get (a,i)
  = let x = var_of_exp a
    in State (\s -> case s of
                 env@(Env _ m) ->
                   case Map.lookup (x,i) m of
                     Just y  -> (EVar y, env)
                     Nothing -> error $ "unbound var " ++ show (x,i)
             )
    
set :: ( Exp Rational -- ^ Update array a
       , Int )        -- ^ At position j
    -> Exp Rational   -- ^ To expression e
    -> Comp
set (a,j) e
  = let x = var_of_exp a
    in do { le <- var
          ; let y = var_of_exp le
          ; _ <- add_arr_bindings [((x,j),y)]
          ; ret $ EAssign le e }

(>>=) :: State s (Exp Rational)
      -> (Exp Rational -> State s (Exp Rational))
      -> State s (Exp Rational)
(>>=) mf g = State (\s ->
  let (e,s') = runState mf s
      (e',s'') = runState (g e) s'
  in case is_pure e of
       True  -> (e',s'')
       False -> case e of
         -- This next line is an optimization; in a sequenced expression
         -- (v<-ESeq [e1..eN]; eN+1[v]), we never need to generate 
         -- constraints for pure expressions in [e1..eN-1], since 
         --   (a) they will not be bound to v in eN+1; and
         --   (b) they otherwise have no effect (non-side-effecting)
         -- NOTE: [length le > 0], by the smart constructor invariant for
         -- sequencing, hence [last le] is always safe.
         ESeq le ->
           let all_but_last = init le
               le' = filter (not . is_pure) all_but_last
           in (exp_seq (ESeq le') e',s'')
         _ -> (exp_seq e e',s''))

(>>) :: State s (Exp Rational)
     -> State s (Exp Rational)
     -> State s (Exp Rational)
(>>) mf g = do { _ <- mf; g }    

return :: a -> State s a
return e = State (\s -> (e,s))

ret :: a -> State s a
ret = return

(+) :: Exp Rational -> Exp Rational -> Exp Rational
(+) e1 e2 = EBinop Add e1 e2

(-) :: Exp Rational -> Exp Rational -> Exp Rational
(-) e1 e2 = EBinop Sub e1 e2

(*) :: Exp Rational -> Exp Rational -> Exp Rational
(*) e1 e2 = EBinop Mult e1 e2

(/) :: Exp Rational -> Exp Rational -> Exp Rational
(/) e1 e2 = EBinop Div e1 e2

(&&) :: Exp Rational -> Exp Rational -> Exp Rational
(&&) e1 e2 = EBinop And e1 e2

xor :: Exp Rational -> Exp Rational -> Exp Rational
xor e1 e2 = EBinop XOr e1 e2

fromRational :: Rational -> Exp Rational
fromRational r = EVal (r :: Rational)

negate :: Exp Rational -> Exp Rational
negate e = EBinop Sub e (EVal zero) 

exp_of_int :: Int -> Exp Rational
exp_of_int i = EVal (P.fromIntegral i)

iter :: Int
     -> (Int -> Exp Rational -> Exp Rational)
     -> Exp Rational
     -> Exp Rational
iter n f e = g n f e
  where g 0 f' e' = f' 0 e'
        g m f' e' = f' m $ g (dec m) f' e'

bigsum :: Int
       -> (Int -> Exp Rational)
       -> Exp Rational
bigsum n f = iter n (\n' e -> f n' + e) 0.0

times :: Int
      -> Comp
      -> Comp
times n mf = g n mf 
  where g 0 _   = ret EUnit
        g m mf' = do { _ <- mf'; g (dec m) mf' }

forall :: [a]
       -> (a -> Comp)
       -> Comp
forall as mf = g as mf
  where g [] _ = ret EUnit
        g (a : as') mf'
          = do { _ <- mf' a; g as' mf' }

forall_pairs :: ([a],[a])
             -> (a -> a -> Comp)
             -> Comp
forall_pairs (as1,as2) mf
  = forall as1 (\a1 -> forall as2 (\a2 -> mf a1 a2))

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int
         , result :: Rational }
  deriving Show  

check :: Comp -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf (Env (P.fromInteger 0) Map.empty)
        nv       = next_var s
        (f,r1cs) = compile_exp nv e
        nw = num_vars r1cs
        ng = num_constraints r1cs
        wit = f inputs
        out = head $ drop nv wit 
    in Result (sat_r1cs wit r1cs) nw ng out
