{-# LANGUAGE GeneralizedNewtypeDeriving
           , DeriveDataTypeable #-}

module Errors where

import Data.Typeable
import Control.Exception

newtype ErrMsg = ErrMsg { errMsg :: String }
  deriving (Typeable)

instance Show ErrMsg where
  show (ErrMsg msg) = msg

instance Exception ErrMsg           

fail_with :: ErrMsg -> a
fail_with e = throw e



