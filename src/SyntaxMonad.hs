{-# LANGUAGE RebindableSyntax
           , DataKinds
           , ScopedTypeVariables
           , PolyKinds
           , GADTs
  #-}

module SyntaxMonad
  ( -- | Computation monad
    Comp
  , CompResult
  , runState
  , return
  , (>>=)
  , (>>)
  , raise_err
  , Env(..)    
  , State(..)

    -- | Return a fresh input variable.
  , fresh_input
    -- | Return a fresh variable.
  , fresh_var
    -- | Return a fresh location.
  , fresh_loc
    
    -- | Basic values
  , unit
  , false
  , true

    -- | Arrays
  , arr
  , input_arr
  , get
  , set

    -- | Pairs
  , pair
  , fst_pair
  , snd_pair

    -- | Basic static analysis
  , is_true
  , is_false
  , assert_false
  , assert_true

  , is_bot
  , assert_bot

    -- | Show the current state.
  , debug_state

    -- | Misc. functions imported by 'Syntax.hs'
  , get_addr
  , add_objects
  ) where

import           Prelude hiding
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

import           Data.Typeable
import qualified Data.Map.Strict as Map

import           Common
import           Errors
import           TExpr

{-----------------------------------------------
 State Monad
------------------------------------------------}

type CompResult s a = Either ErrMsg (a,s)

data State s a = State (s -> CompResult s a)

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
    Right (e,s') -> case runState (g e) s' of
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

-- | At elaboration time, we maintain an environment containing
--    (i) next_var:  the next free variable
--    (ii) next_loc: the next fresh location
--    (iii) obj_map: a symbol table mapping (obj_loc,integer index) to
--    the constraint variable associated with that object, at that
--    field index. A given (obj_loc,integer index) pair may also
--    resolve to a constant rational, boolean, or the bottom value,
--    for constant propagation.
--
--  Reading from object 'a' at index 'i' (x := a_i) corresponds to:
--    (a) getting y <- obj_map(a,i)
--    (b) inserting the constraint (x = y), if x,y resolve to logic
--    vars.

data ObjBind
  = ObjLoc   Loc
  | ObjVar   Var
  deriving ( Show
           )  

data AnalBind
  = AnalBool  Bool
  | AnalConst Rational
  | AnalBot
  deriving ( Show
           )  

type ObjMap
  = Map.Map ( Loc     -- object a
            , Int     -- at index i
            )
            ObjBind   -- maps to result r

data Env = Env { next_var   :: Int
               , next_loc   :: Int
               , input_vars :: [Int]
               , obj_map    :: ObjMap
               , anal_map   :: Map.Map Var AnalBind -- supporting simple constprop analyses
               }
           deriving Show

type Comp ty = State Env (TExp ty Rational)

{-----------------------------------------------
 Units, Booleans (used below)
------------------------------------------------}

unit :: TExp 'TUnit Rational
unit = TEVal VUnit 

false :: TExp 'TBool Rational
false = TEVal VFalse

true :: TExp 'TBool Rational
true = TEVal VTrue

{-----------------------------------------------
 Arrays
------------------------------------------------}

arr :: Typeable ty => Int -> Comp ('TArr ty)
arr 0 = raise_err $ ErrMsg "array must have size > 0"
arr len
  = State (\s -> Right ( TEVal (VLoc (TLoc $ next_loc s))
                         -- allocate:
                         -- (1) a new location (next_loc s)
                         -- (2) 'len' new variables [(next_var s)..(next_var s+len-1)]
                       , s { next_var = (P.+) (next_var s) len
                           , next_loc = (P.+) (next_loc s) 1
                           , obj_map  = new_binds s `Map.union` obj_map s
                           }
                       )
          )
  where new_binds :: Env -> ObjMap
        new_binds s
          = Map.fromList
            (zip (zip (repeat (next_loc s)) [0..((P.-) len 1)])
                 (map ObjVar [next_var s..((P.+) (next_var s) ((P.-) len 1))]))

-- Like 'arr', but declare fresh array variables as inputs.
input_arr :: Typeable ty => Int -> Comp ('TArr ty)
input_arr 0 = raise_err $ ErrMsg "array must have size > 0"
input_arr len
  = State (\s -> Right ( TEVal (VLoc (TLoc $ next_loc s))
                         -- allocate:
                         -- (1) a new location (next_loc s)
                         -- (2) 'len' new variables [(next_var s)..(next_var s+len-1)]
                         -- (3) mark new vars. as inputs
                       , s { next_var   = (P.+) (next_var s) len
                           , next_loc   = (P.+) (next_loc s) 1
                           , input_vars = new_vars s ++ input_vars s 
                           , obj_map    = new_binds s `Map.union` obj_map s
                           }
                       )
          )
  where new_binds :: Env -> ObjMap
        new_binds s
          = Map.fromList
            (zip (zip (repeat (next_loc s)) [0..((P.-) len 1)]) (map ObjVar $ new_vars s))
            
        new_vars s = [next_var s..((P.+) (next_var s) ((P.-) len 1))]           

get_addr :: Typeable ty => (Loc,Int) -> Comp ty
get_addr (l,i)
  = State (\s -> case Map.lookup (l,i) (obj_map s) of
                   Just (ObjLoc l') -> Right (TEVal (VLoc (TLoc l')), s)
                   Just (ObjVar x)  -> Right (TEVar (TVar x), s)
                   Nothing -> Left $ ErrMsg ("unbound loc " ++ show (l,i)
                                             ++ " in heap " ++ show (obj_map s))
          )

get :: Typeable ty => (TExp ('TArr ty) Rational,Int) -> Comp ty
get (a,i) = get_addr (loc_of_texp a,i)

-- | Update array 'a' at position 'i' to expression 'e'. We special-case
-- variable and location expressions, because they're representable untyped
-- in the object map.
set_addr :: Typeable ty
         => (TExp ('TArr ty) Rational, Int)        
         -> TExp ty Rational   
         -> Comp 'TUnit

-- The following specialization (to variable expressions) is an
-- optimization: we avoid introducing a fresh variable.
set_addr (TEVal (VLoc (TLoc l)),i) (TEVar (TVar x))
  = add_objects [((l,i),ObjVar x)] >> return unit

-- The following specialization (to location values) is necessary to
-- satisfy [INVARIANT]: All expressions of compound types (sums,
-- products, arrays, ...) have the form (TEVal (VLoc (TLoc l))), for
-- some location l.
set_addr (TEVal (VLoc (TLoc l)),i) (TEVal (VLoc (TLoc l')))
  = do { add_objects [((l,i),ObjLoc l')]
       ; return unit
       }
    
-- Default:
set_addr (TEVal (VLoc (TLoc l)),i) e
  = do { x <- fresh_var
       ; add_objects [((l,i),ObjVar (var_of_texp x))]
       ; return $ TEAssert x e
       }
    
-- Err: expression does not satisfy [INVARIANT].     
set_addr (e1,_) _
  = raise_err $ ErrMsg ("expected " ++ show e1 ++ " a loc")

set (a,i) e = set_addr (a,i) e

{-----------------------------------------------
 Products
------------------------------------------------}

pair :: ( Typeable ty1
        , Typeable ty2
        )
     => TExp ty1 Rational
     -> TExp ty2 Rational
     -> Comp ('TProd ty1 ty2)
pair te1 te2
  = do { l <- fresh_loc
       ; add_binds (loc_of_texp l) (last_seq te1) (last_seq te2)
       ; return l
       }
  where add_binds l (TEVal (VLoc (TLoc l1))) (TEVal (VLoc (TLoc l2)))
          = add_objects [((l,0),ObjLoc l1), ((l,1),ObjLoc l2)]
        add_binds l (TEVal (VLoc (TLoc l1))) e2
          = do { x2 <- fresh_var
               ; add_objects [((l,0),ObjLoc l1), ((l,1),ObjVar $ var_of_texp x2)]
               ; return $ TEAssert x2 e2
               }
        add_binds l e1 (TEVal (VLoc (TLoc l2)))
          = do { x1 <- fresh_var
               ; add_objects [((l,0),ObjVar $ var_of_texp x1), ((l,1),ObjLoc l2)]
               ; return $ TEAssert x1 e1
               }
        add_binds l e1 e2
          = do { x1 <- fresh_var
               ; x2 <- fresh_var
               ; add_objects [((l,0),ObjVar $ var_of_texp x1),
                              ((l,1),ObjVar $ var_of_texp x2)]
               ; return $ te_seq (TEAssert x1 e1) (TEAssert x2 e2)
               }

fst_pair :: ( Typeable ty1
            , Typeable ty2
            )
         => TExp ('TProd ty1 ty2) Rational
         -> Comp ty1
fst_pair e = get_addr (loc_of_texp e,0)

snd_pair :: ( Typeable ty1
            , Typeable ty2
            )
         => TExp ('TProd ty1 ty2) Rational
         -> Comp ty2
snd_pair e = get_addr (loc_of_texp e,1)

{-----------------------------------------------
 Auxiliary functions
------------------------------------------------}

debug_state :: State Env (TExp 'TUnit a)
debug_state
  = State (\s -> Left $ ErrMsg $ show s)

fresh_var :: State Env (TExp ty a)
fresh_var
  = State (\s -> Right ( TEVar (TVar $ next_var s)
                       , s { next_var = (P.+) (next_var s) 1
                           }
                       )
          )

fresh_input :: State Env (TExp ty a)
fresh_input
  = State (\s -> Right ( TEVar (TVar $ next_var s)
                       , s { next_var   = (P.+) (next_var s) 1
                           , input_vars = next_var s : input_vars s 
                           }
                       )
          )

fresh_loc :: State Env (TExp ty a)
fresh_loc
  = State (\s -> Right ( TEVal (VLoc (TLoc $ next_loc s))
                       , s { next_loc = (P.+) (next_loc s) 1
                           }
                       )
          )

add_objects :: [((Loc,Int),ObjBind)] -> Comp 'TUnit
add_objects binds 
  = State (\s ->
            Right ( unit
                  , s { obj_map = Map.fromList binds `Map.union` obj_map s
                      }
                  ) 
          )

add_statics :: [(Var,AnalBind)] -> Comp 'TUnit
add_statics binds 
  = State (\s ->
            Right ( unit
                  , s { anal_map = Map.fromList binds `Map.union` anal_map s
                      }
                  ) 
          )

-- | Does boolean expression 'e' resolve (statically) to 'b'?
is_bool :: TExp ty Rational -> Bool -> Comp 'TBool
is_bool (TEVal VFalse) False = return true
is_bool (TEVal VTrue)  True  = return true
is_bool e@(TEVar _) b
  = State (\s -> Right ( case Map.lookup (var_of_texp e) (anal_map s) of
                            Nothing -> false
                            Just (AnalBool b') | b/=b' -> false
                            Just (AnalBool b') | b==b' -> true
                            Just _ | otherwise -> false
                       , s
                       )
          )
is_bool _ _ = return false

is_false :: TExp ty Rational -> Comp 'TBool
is_false = flip is_bool False

is_true  :: TExp ty Rational -> Comp 'TBool
is_true  = flip is_bool True

-- | Add binding 'x = b'.
assert_bool :: TExp ty Rational -> Bool -> Comp 'TUnit
assert_bool (TEVar (TVar x)) b = add_statics [(x,AnalBool b)]
assert_bool e _ = raise_err $ ErrMsg $ "expected " ++ show e ++ " a variable"     

assert_false :: TExp ty Rational -> Comp 'TUnit
assert_false = flip assert_bool False

assert_true :: TExp ty Rational -> Comp 'TUnit
assert_true  = flip assert_bool True

is_bot :: TExp ty Rational -> Comp 'TBool
is_bot e@(TEVar (TVar _))
  = State (\s -> Right ( case Map.lookup (var_of_texp e) (anal_map s) of
                            Nothing      -> false
                            Just AnalBot -> true
                            Just _       -> false
                       , s
                       )
          )
is_bot _ = return false    
   
assert_bot :: TExp ty Rational -> Comp 'TUnit
assert_bot (TEVar (TVar x)) = add_statics [(x,AnalBot)]
assert_bot e = raise_err $ ErrMsg $ "expected " ++ show e ++ " a variable"
