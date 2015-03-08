module Solve
  ( solve
  ) where

import Data.Hashable
import qualified Data.IntMap.Lazy as Map

import Common
import Errors
import Field
import Constraints
import Simplify

-- | Starting from an initial partial assignment [env], solve the
-- constraints [cs] and return the resulting complete assignment.
-- If the constraints are unsolvable from [env], report the first
-- constraint that is violated (under normal operation, this error
-- case should NOT occur).
solve :: ( Field a
         , Hashable a
         )
      => ConstraintSystem a -- ^ Constraints to be solved
      -> Assgn a -- ^ Initial assignment
      -> Assgn a -- ^ Resulting assignment
solve cs env = 
  let pinned_vars = cs_in_vars cs ++ cs_out_vars cs
      (assgn,cs') = do_simplify env cs
  in if all_assigned pinned_vars assgn then assgn
     else fail_with
          $ ErrMsg ("some pinned variables are unassigned,\n"
             ++ "in assignment context\n  " ++ show assgn ++ ",\n"
             ++ "in pinned-variable context\n  " ++ show pinned_vars ++ ",\n"
             ++ "in optimized-constraint context\n  " ++ show cs' ++ ",\n"
             ++ "in constraint context\n  " ++ show cs)

  where all_assigned vars0 assgn = all id $ map (is_mapped assgn) vars0
        is_mapped assgn x
          = case Map.lookup x assgn of
              Nothing -> False
              Just _ -> True
