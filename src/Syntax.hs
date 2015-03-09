{-# LANGUAGE GADTs
           , RebindableSyntax
           , DataKinds
           , RankNTypes
           , KindSignatures
           , ScopedTypeVariables
  #-}

module Syntax where

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

import System.IO
  ( hFlush
  , stdout
  , hPutStrLn
  , withFile
  , IOMode( WriteMode )
  )

import Data.Typeable

import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Lazy as IntMap

import Common
import Errors
import R1CS
import Source
import Compile
import Serialize

ifThenElse :: TExp TBool a -> TExp ty a -> TExp ty a -> TExp ty a
ifThenElse b e1 e2 = TEIf b e1 e2

data State s a = State (s -> (a,s))

-- | At "parse" time, we maintain an environment containing
--    (i) next_var: the next free variable
--    (ii) arr_map: a symbol table mapping (array_var,index) to
--    the constraint variable associated with that array index
--    (iii) width_map: a symbol table mapping 'array_var' to the
--    bit width of each array element.
--  Reading from array x := a[i] corresponds to:
--    (a) calculating the effective address (a + width(a)*i) 
--    (b) getting v <- arr_map(a,i)
--    (c) inserting the constraint (x = x)

type ArrMap
  = Map.Map ( Var -- array a
            , Int -- at index i
            )
            Var -- maps to variable x

type WidthMap
  = IntMap.IntMap -- array a
              Int -- has elements of width w

data Env = Env { next_var :: Int
               , input_vars :: [Int]
               , arr_map  :: ArrMap
               , width_map :: WidthMap
               }
           deriving Show

type Comp ty = State Env (TExp ty Rational)

runState :: State s a -> s -> (a,s)
runState mf s = case mf of
  State f -> f s

-- | We have to define our own bind operator, unfortunately,
-- because the "result" that's returned is the sequential composition
-- of the results of 'mf', 'g' (not just whatever 'g' returns)
(>>=) :: forall (ty1 :: Ty) (ty2 :: Ty) s a.
         Typeable ty1
      => State s (TExp ty1 a)
      -> (TExp ty1 a -> State s (TExp ty2 a))
      -> State s (TExp ty2 a)
(>>=) mf g = State (\s ->
  let (e,s') = runState mf s
      (e',s'') = runState (g e) s'
  in (TESeq e e',s''))

(>>) :: forall (ty1 :: Ty) (ty2 :: Ty) s a.
        Typeable ty1
     => State s (TExp ty1 a)
     -> State s (TExp ty2 a)
     -> State s (TExp ty2 a)
(>>) mf g = do { _ <- mf; g }    

return :: a -> State s a
return e = State (\s -> (e,s))

ret :: a -> State s a
ret = return

inc :: Int -> Int
inc n = (P.+) n 1

dec :: Int -> Int
dec n = (P.-) n 1

-- | Allocate a new internal variable (not instantiated by user)
var :: Comp ty
var = State (\s -> ( TEVar (TVar (next_var s))
                   , Env (inc (next_var s))
                         (input_vars s)
                         (arr_map s)
                         (width_map s)
                   )
            )

-- | Allocate a new input variable (instantiated by user)
input :: Comp ty
input = State (\s -> ( TEVar (TVar (next_var s))
                     , Env (inc (next_var s))
                           (next_var s : input_vars s)
                           (arr_map s)
                           (width_map s)                       
                     )
              )

iter_comp :: Typeable ty
          => Comp ty
          -> Int
          -> Comp ty
iter_comp _ 0 = fail_with $ ErrMsg "must declare >= 1 vars"
iter_comp f n =
  do { x <- f
     ; _ <- g (dec n)
     ; ret x
     }
  where g 0 = ret (TEVal VUnit)
        g m = f >> g (dec m)

----------------------------------------------------
--
-- Arrays
--        
----------------------------------------------------        

-- | Arrays: uninitialized field elements
declare_vars :: Typeable ty => Int -> Comp ty
declare_vars = iter_comp (var :: Comp ty)

-- | Like declare_vars, except vars. are marked explicitly as inputs
declare_inputs :: Typeable ty => Int -> Comp ty
declare_inputs = iter_comp (input :: Comp ty)

add_width_bindings :: [(Var,Int)] -> Comp TUnit
add_width_bindings width_bindings
  = State (\s -> case s of
              Env nv ivs m m_width ->
                ( unit
                , Env nv ivs m
                  (IntMap.fromList width_bindings `IntMap.union` m_width)   
                )
          )

add_arr_bindings :: [((Var,Int),Var)] -> Comp TUnit
add_arr_bindings bindings
  = State (\s -> case s of
              Env nv ivs m m_width ->
                ( unit
                , Env nv ivs
                  (Map.fromList bindings `Map.union` m)
                  m_width
                )
          )

add_arr_mapping :: Var -> Int -> Comp TUnit
add_arr_mapping x len
  = do { let indices  = take len $ [(0::Int)..]
       ; let arr_vars = map ((P.+) x) indices
       ; add_arr_bindings $ zip (zip (repeat x) indices) arr_vars
       }

-- | 1-d arrays. 
arr :: Typeable ty => Int -> Comp (TArr ty)
arr 0 = fail_with $ ErrMsg "array must have size > 0"
arr len
  = do { a <- declare_vars len
       ; let x = var_of_texp a
       ; _ <- add_arr_mapping x len
       ; ret $ last_seq a
       }


-- | 2-d arrays. 'width' is the size, in "bits" (#field elements), of
-- each array element.
arr2 :: Typeable ty => Int -> Int -> Comp (TArr (TArr ty))
arr2 len width
  = do { a <- arr len
       ; forall [0..dec len] (\i ->
           do { ai <- arr width
              ; set (a,i) ai
              })
       ; ret a
       }

-- | 3-d arrays.
arr3 :: Typeable ty => Int -> Int -> Int -> Comp (TArr (TArr (TArr ty)))
arr3 len width height
  = do { a <- arr2 len width
       ; forall2 ([0..dec len],[0..dec width]) (\i j ->
           do { aij <- arr height
              ; set2 (a,i,j) aij
              })
       ; ret a
       }

-- | Like 'arr', but declare array vars. as inputs.
input_arr :: Typeable ty => Int -> Comp (TArr ty)
input_arr len
  = do { a <- declare_inputs len
       ; let x = var_of_texp a
       ; _ <- add_arr_mapping x len
       ; ret $ last_seq a
       }

input_arr2 :: Typeable ty => Int -> Int -> Comp (TArr (TArr ty))
input_arr2 0 _ = fail_with $ ErrMsg "array must have size > 0"
input_arr2 len width
  = do { a <- arr len
       ; forall [0..dec len] (\i ->
           do { ai <- input_arr width
              ; set (a,i) ai
              })
       ; ret a
       }

input_arr3 :: Typeable ty => Int -> Int -> Int -> Comp (TArr (TArr (TArr ty)))
input_arr3 len width height
  = do { a <- arr2 len width
       ; forall2 ([0..dec len],[0..dec width]) (\i j ->
           do { aij <- input_arr height
              ; set2 (a,i,j) aij
              })
       ; ret a
       }

-- | Update array 'a' at position 'i' to expression 'e'.
set_addr :: Typeable ty
         => (TExp (TArr ty) Rational, Int)        
         -> TExp ty Rational   
         -> Comp TUnit
set_addr (a,i) e
  = let x = var_of_texp a
    in case last_seq e of
         scrut@(TEVar _) -> 
           do { let y = var_of_texp scrut
              ; _ <- add_arr_bindings [((x,i),y)]
              ; ret unit
              }
           
         _ ->  
           do { le <- var
              ; let y = var_of_texp le
              ; _ <- add_arr_bindings [((x,i),y)]
              ; ret $ TEUpdate le e
              }

set (a,i) e      = set_addr (a,i) e
set2 (a,i,j) e   = do { a' <- get (a,i); set (a',j) e }
set3 (a,i,j,k) e = do { a' <- get2 (a,i,j); set (a',k) e }
set4 (a,i,j,k,l) e = do { a' <- get3 (a,i,j,k); set (a',l) e }


get_addr :: Typeable ty => (Var,Int) -> Comp ty
get_addr (x,i)
  = State (\s -> case s of
              env@(Env _ _ m _) ->
                case Map.lookup (x,i) m of
                  Nothing ->
                    fail_with
                    $ ErrMsg ("unbound var " ++ show (x,i)
                              ++ " in map " ++ show m)
                  Just y  ->
                    (TEVar (TVar y), env)
          )

get :: Typeable ty => (TExp (TArr ty) Rational,Int) -> Comp ty
get (a,i)        = get_addr (var_of_texp a,i)
get2 (a,i,j)     = do { a' <- get (a,i); get (a',j) }
get3 (a,i,j,k)   = do { a' <- get2 (a,i,j); get (a',k) }
get4 (a,i,j,k,l) = do { a' <- get3 (a,i,j,k); get (a',l) }


----------------------------------------------------
--
-- Products
--        
----------------------------------------------------        

pair :: ( Typeable ty1
        , Typeable ty2
        )
     => TExp ty1 Rational
     -> TExp ty2 Rational
     -> Comp (TProd ty1 ty2)
pair te1 te2 = go (last_seq te1) (last_seq te2)
  where go e1@(TEVar _) e2@(TEVar _)
          = do { x <- var
               ; let x1 = var_of_texp e1
               ; let x2 = var_of_texp e2             
               ; add_arr_bindings [((var_of_texp x,0),x1)
                                  ,((var_of_texp x,1),x2)]
               ; ret x
               }
        go e1@(TEVar _) e2@(_)
          = do { x <- var
               ; let x1 = var_of_texp e1
               ; x2 <- var      
               ; add_arr_bindings [((var_of_texp x,0),x1)
                                  ,((var_of_texp x,1),var_of_texp x2)]
               ; ret $ TESeq (TEUpdate x2 e2) x
               }    
        go e1@(_) e2@(TEVar _)
          = do { x <- var
               ; x1 <- var                    
               ; let x2 = var_of_texp e2
               ; add_arr_bindings [((var_of_texp x,0),var_of_texp x1)
                                  ,((var_of_texp x,1),x2)]
               ; ret $ TESeq (TEUpdate x1 e1) x
               }    
        go e1@(_) e2@(_)
          = do { x1 <- var
               ; x2 <- var
               ; x <- var
               ; add_arr_bindings [((var_of_texp x,0),var_of_texp x1)
                                  ,((var_of_texp x,1),var_of_texp x2)]
               ; ret $ TESeq (TESeq (TEUpdate x1 e1) (TEUpdate x2 e2)) x
               }

fst_pair :: ( Typeable ty1
            , Typeable ty2
            )
         => TExp (TProd ty1 ty2) Rational
         -> Comp ty1
fst_pair e = get_addr (var_of_texp e,0)

snd_pair :: ( Typeable ty1
            , Typeable ty2
            )
         => TExp (TProd ty1 ty2) Rational
         -> Comp ty2
snd_pair e = get_addr (var_of_texp e,1)


----------------------------------------------------
--
-- Operators, Values
--        
----------------------------------------------------        

unit :: TExp TUnit Rational
unit = TEVal VUnit 

true :: TExp TBool Rational
true = TEVal VTrue

false :: TExp TBool Rational
false = TEVal VFalse

(+) :: TExp TField Rational -> TExp TField Rational -> TExp TField Rational
(+) e1 e2 = TEBinop (TOp Add) e1 e2

(-) :: TExp TField Rational -> TExp TField Rational -> TExp TField Rational
(-) e1 e2 = TEBinop (TOp Sub) e1 e2

(*) :: TExp TField Rational -> TExp TField Rational -> TExp TField Rational
(*) e1 e2 = TEBinop (TOp Mult) e1 e2

(/) :: TExp TField Rational -> TExp TField Rational -> TExp TField Rational
(/) e1 e2 = TEBinop (TOp Div) e1 e2

(&&) :: TExp TBool Rational -> TExp TBool Rational -> TExp TBool Rational
(&&) e1 e2 = TEBinop (TOp And) e1 e2

not :: TExp TBool Rational -> TExp TBool Rational
not e = if e then false else true

xor :: TExp TBool Rational -> TExp TBool Rational -> TExp TBool Rational
xor e1 e2 = TEBinop (TOp XOr) e1 e2

eq :: TExp TBool Rational -> TExp TBool Rational -> TExp TBool Rational
eq e1 e2 = TEBinop (TOp Eq) e1 e2

fromRational :: Rational -> TExp TField Rational
fromRational r = TEVal (VField (r :: Rational))

exp_of_int :: Int -> TExp TField Rational
exp_of_int i = TEVal (VField $ P.fromIntegral i)

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

bigsum :: Int
       -> (Int -> TExp TField Rational)
       -> TExp TField Rational
bigsum n f = iter n (\n' e -> f n' + e) 0.0

times :: Typeable ty
      => Int
      -> Comp ty
      -> Comp TUnit
times n mf = g n mf 
  where g 0 _   = ret unit
        g m mf' = do { _ <- mf'; g (dec m) mf' }

forall :: Typeable ty
       => [a]
       -> (a -> Comp ty)
       -> Comp TUnit
forall as mf = g as mf
  where g [] _ = ret unit
        g (a : as') mf'
          = do { _ <- mf' a; g as' mf' }

forall2 (as1,as2) mf = forall as1 (\a1 -> forall as2 (\a2 -> mf a1 a2))
forall3 (as1,as2,as3) mf
  = forall2 (as1,as2) (\a1 a2 -> forall as3 (\a3 -> mf a1 a2 a3))

----------------------------------------------------
--
-- Toplevel Stuff 
--        
----------------------------------------------------        

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int
         , result :: Rational 
         , the_r1cs :: String
         }

instance Show Result where
  show (Result the_sat the_vars the_constraints the_result _)
    = "sat = " ++ show the_sat
      ++ ", vars = " ++ show the_vars
      ++ ", constraints = " ++ show the_constraints
      ++ ", result = " ++ show the_result

check :: Typeable ty => Comp ty -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf (Env (P.fromInteger 0) [] Map.empty IntMap.empty)
        nv       = next_var s
        in_vars  = reverse $ input_vars s
        r1cs     = r1cs_of_exp nv in_vars e
        r1cs_string = serialize_r1cs r1cs
        nw        = r1cs_num_vars r1cs
        f         = r1cs_gen_witness r1cs . IntMap.fromList
        [out_var] = r1cs_out_vars r1cs
        ng  = num_constraints r1cs
        wit = case length in_vars /= length inputs of
                True ->
                  fail_with
                  $ ErrMsg ("expected " ++ show (length in_vars) ++ " input(s)"
                            ++ " but got " ++ show (length inputs) ++ " input(s)")
                False ->
                  f (zip in_vars inputs)
        out = case IntMap.lookup out_var wit of
                Nothing ->
                  fail_with
                  $ ErrMsg ("output variable " ++ show out_var
                            ++ "not mapped, in\n  " ++ show wit)
                Just out_val -> out_val
    in Result (sat_r1cs wit r1cs) nw ng out r1cs_string

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, w.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check that results match.
do_test :: Typeable ty => (Comp ty, [Rational], Rational) -> IO ()
do_test (prog,inputs,res) =
  let print_ln             = print_ln_to_file stdout
      print_ln_to_file h s = (P.>>) (hPutStrLn h s) (hFlush h)
      print_to_file s
        = withFile "test_cs_in.ppzksnark" WriteMode (flip print_ln_to_file s)
  in case check prog inputs of
    r@(Result True _ _ res' r1cs_string) ->
      case res == res' of
        True  ->  (P.>>) (print_to_file r1cs_string) (print_ln $ show r)
        False ->  print_ln $ show $ "error: results don't match: "
                  ++ "expected " ++ show res ++ " but got " ++ show res'
    Result False _ _ _ _ ->
      print_ln $ "error: witness failed to satisfy constraints"

test :: Typeable ty => (Comp ty,[Int],Integer) -> IO ()
test (prog,args,res)
  = do_test (prog,map fromIntegral args,fromIntegral res)
