{-# LANGUAGE StandaloneDeriving
           , GADTs 
  #-}

module Interp
  ( interp
  ) where

import Data.IntMap ( IntMap )
import qualified Data.IntMap as IntMap
import Control.Monad

import Errors
import Common
import Field
import TExpr

type Env a = IntMap (Maybe a)

newtype InterpM a b
  = InterpM { runInterpM :: Env a -> Either ErrMsg (Env a,b) }

instance Monad (InterpM a) where    
  (>>=) mf mg
    = InterpM (\rho -> case runInterpM mf rho of
                  Left err -> Left err
                  Right (rho',b) -> runInterpM (mg b) rho')
  return b
    = InterpM (\rho -> Right (rho,b))

instance Functor (InterpM a) where
  fmap f mg = return f `ap` mg
    
instance Applicative (InterpM a) where
  pure = return 
  mf <*> ma = ap mf ma

raise_err err
  = InterpM (\_ -> Left err)

add_binds binds
  = InterpM (\rho -> Right (IntMap.union (IntMap.fromList binds) rho,Nothing))

lookup_var x
  = InterpM (\rho -> case IntMap.lookup x rho of
                Nothing -> Left $ ErrMsg $ "unbound var " ++ show x
                                  ++ " in environment " ++ show rho
                Just v -> Right (rho,v))


field_of_bool :: Field a => Bool -> a
field_of_bool b = if b then one else zero

case_of_field :: Field a => Maybe a -> (Maybe Bool -> InterpM a b) -> InterpM a b
case_of_field Nothing f = f Nothing
case_of_field (Just v) f
  = if v == zero then f $ Just False
    else if v == one then f $ Just True
         else raise_err $ ErrMsg $ "expected " ++ show v ++ " to be boolean"

bool_of_field :: Field a => a -> InterpM a Bool
bool_of_field v
  = case_of_field (Just v)
    (\mb -> case mb of
        Nothing -> raise_err $ ErrMsg "internal error in bool_of_field"
        Just b -> return b)

interp_unop :: Field a
            => TUnop ty1 ty2 -> TExp ty1 a -> InterpM a (Maybe a) 
interp_unop op e2
  = do { mv2 <- interp_texp e2
       ; case mv2 of
           Nothing -> return Nothing
           Just v2 ->
             case op of
               TUnop ZEq -> return $ Just $ field_of_bool (v2 == zero)
       }

interp_binop :: Field a
             => TOp ty1 ty2 ty3 -> TExp ty1 a -> TExp ty2 a -> InterpM a (Maybe a) 
interp_binop op e1 e2
  = do { mv1 <- interp_texp e1
       ; mv2 <- interp_texp e2
       ; case (mv1,mv2) of
           (Nothing,_) -> return Nothing
           (_,Nothing) -> return Nothing
           (Just v1,Just v2) ->
             do { v <- interp_val_binop v1 v2
                ; return $ Just v
                }
       }
  where interp_val_binop v1 v2
          = case op of
              TOp Add -> return $ v1 `add` v2
              TOp Sub -> return $ v1 `add` (neg v2)
              TOp Mult -> return $ v1 `mult` v2
              TOp Div ->
                case inv v2 of
                  Nothing -> raise_err $ ErrMsg $ show v2 ++ " not invertible"
                  Just v2' -> return $ v1 `mult` v2'
              TOp And -> interp_boolean_binop v1 v2
              TOp Or  -> interp_boolean_binop v1 v2
              TOp XOr -> interp_boolean_binop v1 v2
              TOp BEq -> interp_boolean_binop v1 v2
              TOp Eq  -> return $ field_of_bool $ v1 == v2

        interp_boolean_binop v1 v2
          = do { b1 <- bool_of_field v1
               ; b2 <- bool_of_field v2
               ; let b = case op of
                           TOp And -> b1 && b2
                           TOp Or  -> b1 || b2 
                           TOp XOr -> (b1 && not b2) || (b2 && not b1)
                           TOp BEq -> b1 == b2
                           _ -> fail_with $ ErrMsg "internal error in interp_binop"
                 in return $ field_of_bool b
               }

interp_val :: Field a => Val ty a -> InterpM a a
interp_val v
  = case v of
      VField v' -> return v'
      VTrue  -> return $ field_of_bool True
      VFalse -> return $ field_of_bool False
      VUnit  -> return one
      VLoc _ -> raise_err $ ErrMsg "location in source program"

interp_texp :: ( Eq a
               , Show a
               , Field a
               )
            => TExp ty1 a
            -> InterpM a (Maybe a)
interp_texp e 
  = case e of
      TEVar (TVar x) -> lookup_var x
      TEVal v -> interp_val v >>= return . Just
      TEUnop op e2 -> interp_unop op e2
      TEBinop op e1 e2 -> interp_binop op e1 e2
      TEIf eb e1 e2 ->
        do { mv <- interp_texp eb
           ; case_of_field mv
             (\mb -> case mb of
                 Nothing -> return Nothing
                 Just b  -> if b then interp_texp e1 else interp_texp e2)
           }
      TEAssert e1 e2 ->
        case (e1,e2) of
          (TEVar (TVar x),_) ->
            do { v2 <- interp_texp e2
               ; add_binds [(x,v2)]
               }
          (_,_) -> raise_err $ ErrMsg $ show e1 ++ " not a variable"
      TESeq e1 e2 ->
        do { interp_texp e1
           ; interp_texp e2
           }
      TEBot -> return Nothing

interp rho e = runInterpM (interp_texp e) $ IntMap.map Just rho
