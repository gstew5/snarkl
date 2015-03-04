{-# LANGUAGE GADTs,RebindableSyntax,DataKinds,RankNTypes #-}

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

import Unsafe.Coerce 

import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Lazy as IntMap

import Common
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
--    the constraint variable associated with that array index.
--  Reading from array x := a[i] corresponds to:
--    (a) getting i <- arr_map(a,i)
--    (b) inserting the constraint (x = i)

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


-- | Arrays: uninitialized
declare_vars :: Int -> Comp ty
declare_vars 0 = error "must declare >= 1 vars"
declare_vars n =
  do { x <- var
     ; _ <- g (dec n)
     ; ret x
     }
  where g 0 = ret (TEVal VUnit)
        g m = var >> g (dec m)


-- Like declare_vars, except vars. are marked explicitly as inputs
declare_inputs :: Int -> Comp ty
declare_inputs 0 = error "must declare >= 1 vars"
declare_inputs n =
  do { x <- input
     ; _ <- g (dec n)
     ; ret x
     }
  where g 0 = ret $ TEVal VUnit
        g m = input >> g (dec m)

add_width_bindings :: [(Var,Int)] -> Comp TUnit
add_width_bindings width_bindings
  = State (\s -> case s of
              Env nv ivs m m_width ->
                ( unit
                , Env nv ivs m
                  (IntMap.fromList width_bindings `IntMap.union` m_width)   
                )
          )


add_arr_bindings :: [((Var,Int),Var)]
                 -> Comp TUnit
add_arr_bindings bindings
  = State (\s -> case s of
              Env nv ivs m m_width ->
                ( unit
                , Env nv ivs
                  (Map.fromList bindings `Map.union` m)
                  m_width
                )
          )


add_arr_mapping :: TExp (TRef ty) Rational -> Int -> Int -> Comp TUnit
add_arr_mapping a sz width
  = do { let x = var_of_texp a
       ; let len = ((P.*) sz width)
       ; let indices  = take len $ [(0::Int)..]
       ; let arr_vars = map ((P.+) x) indices
       ; add_width_bindings [(x,width)]
       ; add_arr_bindings $ zip (zip (repeat x) indices) arr_vars
       }

-- | 2-d arrays. 'width' is the size, in "bits" (#field elements), of
-- each array element.
arr2 :: Int -> Int -> Comp (TRef ty)
arr2 0 _ = error "array must have size > 0"
arr2 sz width
  = do { let len = ((P.*) sz width)
       ; a <- declare_vars len
       ; _ <- add_arr_mapping a sz width
       ; ret $ last_seq a
       }

arr :: Int -> Comp (TRef ty)
arr sz = arr2 sz 1

-- Like arr, except array variables are marked as "inputs"
input_arr2 :: Int -> Int -> Comp (TRef ty)
input_arr2 0 _ = error "array must have size > 0"
input_arr2 sz width
  = do { let len = ((P.*) sz width)
       ; a <- declare_inputs len
       ; _ <- add_arr_mapping a sz width
       ; ret $ last_seq a
       }

input_arr :: Int -> Comp (TRef ty)
input_arr sz = input_arr2 sz 1

get_arr_width :: Var -> WidthMap -> Int
get_arr_width x m_width
  = case IntMap.lookup x m_width of
      Nothing -> error $ "unbound var " ++ show x
      Just w -> w

-- | Calculate the effective address of a[i]
eff_addr :: (TExp (TRef ty) Rational, Int) -> Comp TField
eff_addr (a,i)
  = let x = var_of_texp a
    in State (\s -> case s of
                 env@(Env _ _ _ m_width) ->
                   let width = get_arr_width x m_width
                   in ( TEVal $ VField (fromIntegral $ (P.*) width i)
                      , env
                      )
             )

get_addr :: (TExp (TRef ty) Rational,Int) -> Comp ty
get_addr (a',i')
  = let x = var_of_texp a'
    in State (\s -> case s of
                 env@(Env _ _ m _) ->
                   case Map.lookup (x,i') m of
                     Nothing -> error $ "unbound var " ++ show (x,i')
                                        ++ " in map " ++ show m
                     Just y  -> (unsafeCoerce
                                 $ TEVar (TVar y), env)
             )

get2 :: ( TExp (TRef ty) Rational -- select from array a
        , Int   -- at index i  
        , Int ) -- at index j
     -> Comp ty
get2 (a,i,j)
  = do { addr <- eff_addr (a,i)
       ; let TEVal (VField addr') = addr
       ; e <- get_addr (a,(P.+) (truncate addr') j)
       ; ret e
       }

get :: ( TExp (TRef ty) Rational -- select from array a
       , Int )        -- at index i
    -> Comp ty -- result e
get (a,i) = get2 (a,i,0)


-- | Update array 'a' at position 'i,j' to expression 'e'.
set2 :: (TExp (TRef ty) Rational, Int, Int)        
     -> TExp ty Rational   
     -> Comp TUnit
set2 (a,i,j) e
  = let x = var_of_texp a
    in do { le <- var
          ; let y = var_of_texp le
          ; addr <- eff_addr (a,i)
          ; let TEVal (VField addr') = addr
          ; _ <- add_arr_bindings [((x,(P.+) (truncate addr') j),y)]
          ; ret $ TEAssign le e
          }
       
-- | Update array 'a' at position 'i' to expression 'e'.
set :: (TExp (TRef ty) Rational, Int)        
    -> TExp ty Rational   
    -> Comp TUnit
set (a,i) = set2 (a,i,0)

(>>=) :: State s (TExp ty1 a)
      -> (TExp ty1 a -> State s (TExp ty2 a))
      -> State s (TExp ty2 a)
(>>=) mf g = State (\s ->
  let (e,s') = runState mf s
      (e',s'') = runState (g e) s'
  in (TESeq e e',s''))

(>>) :: State s (TExp ty1 a)
     -> State s (TExp ty2 a)
     -> State s (TExp ty2 a)
(>>) mf g = do { _ <- mf; g }    

return :: a -> State s a
return e = State (\s -> (e,s))

ret :: a -> State s a
ret = return

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

iter :: Int
     -> (Int -> TExp ty Rational -> TExp ty Rational)
     -> TExp ty Rational
     -> TExp ty Rational
iter n f e = g n f e
  where g 0 f' e' = f' 0 e'
        g m f' e' = f' m $ g (dec m) f' e'

unit :: TExp TUnit Rational
unit = TEVal VUnit 


bigsum :: Int
       -> (Int -> TExp TField Rational)
       -> TExp TField Rational
bigsum n f = iter n (\n' e -> f n' + e) 0.0

times :: Int
      -> Comp ty
      -> Comp TUnit
times n mf = g n mf 
  where g 0 _   = ret unit
        g m mf' = do { _ <- mf'; g (dec m) mf' }

forall :: [a]
       -> (a -> Comp ty)
       -> Comp TUnit
forall as mf = g as mf
  where g [] _ = ret unit
        g (a : as') mf'
          = do { _ <- mf' a; g as' mf' }

forall_pairs :: ([a],[a])
             -> (a -> a -> Comp ty)
             -> Comp TUnit
forall_pairs (as1,as2) mf
  = forall as1 (\a1 -> forall as2 (\a2 -> mf a1 a2))

data Result = 
  Result { sat :: Bool
         , vars :: Int
         , constraints :: Int
         , result :: Rational 
         , the_r1cs :: String }

instance Show Result where
  show (Result the_sat the_vars the_constraints the_result _)
    = "sat = " ++ show the_sat
      ++ ", vars = " ++ show the_vars
      ++ ", constraints = " ++ show the_constraints
      ++ ", result = " ++ show the_result

check :: Comp ty -> [Rational] -> Result
check mf inputs
  = let (e,s)    = runState mf (Env (P.fromInteger 0) [] Map.empty IntMap.empty)
        nv       = next_var s
        in_vars  = reverse $ input_vars s
        r1cs     = compile_exp nv in_vars e
        r1cs_string = serialize_r1cs r1cs
        nw        = r1cs_num_vars r1cs
        f         = r1cs_gen_witness r1cs . IntMap.fromList
        [out_var] = r1cs_out_vars r1cs
        ng  = num_constraints r1cs
        wit = case length in_vars /= length inputs of
                True ->
                  error $ "expected " ++ show (length in_vars) ++ " input(s)"
                  ++ " but got " ++ show (length inputs) ++ " input(s)"
                False -> f (zip in_vars inputs)
        out = case IntMap.lookup out_var wit of
                Nothing -> error $ "output variable " ++ show out_var
                                   ++ "not mapped, in " ++ show wit
                Just out_val -> out_val
    in Result (sat_r1cs wit r1cs) nw ng out r1cs_string

-- | (1) Compile to R1CS.
--   (2) Generate a satisfying assignment, w.
--   (3) Check whether 'w' satisfies the constraint system produced in (1).
--   (4) Check that results match.
run_test (prog,inputs,res) =
  let print_ln = print_ln_to_file stdout
      print_ln_to_file h s
        = (P.>>) (hPutStrLn h s) (hFlush h)
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

