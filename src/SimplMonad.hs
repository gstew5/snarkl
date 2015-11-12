module SimplMonad
  ( SEnv(..)
  , unite_vars
  , bind_var
  , root_of_var
  , bind_of_var
  , assgn_of_vars
  , SolveMode(..)
  , solve_mode_flag
  ) where

import qualified Data.IntMap.Lazy as Map
import Control.Monad.State

import Field
import Common
import UnionFind

----------------------------------------------------------------
--                  Simplifier State Monad                    --
----------------------------------------------------------------

data SolveMode = UseMagic | JustSimplify
  deriving Show

data SEnv a =
  SEnv { eqs :: UnionFind a   -- ^ Equalities among variables,
                              -- together with a partial map from variables
                              -- to constants (hidden inside the "UnionFind"
                              -- data structure).
       , solve_mode :: SolveMode   -- ^ Use Magic only in 'solve_mode'.
                                   -- In simplify mode, only forced equalities 
                                   -- should be propagated.
       }
  deriving Show

-- | Unify variables 'x' and 'y'.
unite_vars :: Field a => Var -> Var -> State (SEnv a) ()
unite_vars x y
  = do { modify (\senv -> senv { eqs = unite (eqs senv) x y }) }

-- | Bind variable 'x' to 'c'.
bind_var :: Field a => (Var,a) -> State (SEnv a) ()
bind_var (x,c)
  = do { rx <- root_of_var x
       ; senv <- get
       ; let eqs' = (eqs senv) { extras = Map.insert rx c (extras $ eqs senv) }
       ; put $ senv { eqs = eqs' }
       }

-- | Return 'x''s root (the representative of its equivalence class).
root_of_var :: Field a => Var -> State (SEnv a) Var
root_of_var x 
  = do { senv <- get
       ; let (rx,eqs') = root (eqs senv) x
       ; put (senv { eqs = eqs'})
       ; return rx
       }

-- | Return the binding associated with variable 'x', or 'x''s root
-- if no binding exists.
bind_of_var :: Field a => Var -> State (SEnv a) (Either Var a)
bind_of_var x
  = do { rx <- root_of_var x
       ; senv <- get
       ; case extra_of (eqs senv) rx of
           Nothing -> return $ Left rx
           Just c -> return $ Right c
       }

-- | Construct a partial assignment from 'vars' to field elements.
assgn_of_vars :: Field a => [Var] -> State (SEnv a) (Assgn a)
assgn_of_vars vars
  = do { binds <- mapM bind_of_var vars
       ; return
         $ Map.fromList
         $ concatMap (\(x,ec) -> case ec of
                         Left _ -> []
                         Right c -> [(x,c)])
         $ zip vars binds
       }

-- | Are we in solve mode? 
solve_mode_flag :: State (SEnv a) Bool
solve_mode_flag 
  = do { env <- get
       ; case solve_mode env of
           UseMagic -> return True
           JustSimplify -> return False
       }
