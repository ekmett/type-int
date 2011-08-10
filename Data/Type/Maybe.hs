{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, FlexibleInstances, FlexibleContexts, EmptyDataDecls #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Maybe
-- Copyright   :  (C) 2006 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (MPTC)
--
-- Simple type-level Maybe w/ Just/Nothing Types
----------------------------------------------------------------------------

module Data.Type.Maybe 
  ( TNothing(..)
  , tNothing
  , TJust(..), tJust
  , tFromJust
  , TMaybe 
  ) where

import Data.Type.Boolean
import Data.Type.Ord

data Closure
class Closed a | -> a
instance Closed Closure

data TNothing
tNothing :: TNothing
tNothing = undefined

data TJust x

tJust :: t -> TJust t 
tJust = undefined

tFromJust :: TJust t -> t
tFromJust = undefined

instance Show TNothing where show _ = "TNothing"
instance Show a => Show (TJust a) where show x = "TJust " ++ show (tFromJust x)

class TCMaybe c a | a -> c
instance TCMaybe Closure TNothing
instance TCMaybe Closure (TJust a)

class TCMaybe Closure s => TMaybe s
instance TMaybe TNothing
instance TMaybe (TJust a)

instance TEq TNothing TNothing T
instance TEq TNothing  (TJust a) F
instance TEq (TJust a) TNothing F
instance TEq a b r => TEq (TJust a) (TJust b) r

instance TLt a b r => TLt (TJust a) (TJust b) r
instance TLt TNothing  (TJust b) T
instance TLt (TJust b) TNothing F
instance TLt TNothing  TNothing F
