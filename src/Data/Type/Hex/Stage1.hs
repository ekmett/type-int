{-# LANGUAGE TemplateHaskell #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Hex.Stage1
-- Copyright   :  (C) 2006 Edward Kmett
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (MPTC, FD, TH, undecidable instances, missing constructors)
--
-- Stage1: Lay the ground work for all sorts of Template Haskell hackery 
-- in the later stages. Only a handful of class specifications in this file
-- are for later public consumption, and none of those are fleshed out here.
--
-- This multiple-stage implementation is necessitated by the way Template 
-- Haskell is implemented in GHC.
----------------------------------------------------------------------------
module Data.Type.Hex.Stage1 where

import Data.Type.Boolean
import Data.Type.Sign
import Control.Monad
import Language.Haskell.TH

t, f :: Name
t = mkName "T"
f = mkName "F"

hex :: String
hex = "0123456789ABCDEF"

xn, hn :: [Name]
xn = map (\x -> mkName $ "D"++return x) hex 
hn = map (\x -> mkName $ "H"++return x) hex 

x, h :: [Type]
xh :: [(Type, Type)]
x = map ConT xn
h = map ConT hn
xh = zip x h

x0, h0 :: [Type]
xh0 :: [(Type, Type)]
x0 = tail x
h0 = tail h
xh0 = tail xh

xF, hF :: [Type]
xhF :: [(Type, Type)]
xF = init x
hF = init h
xhF = zip xF hF

x0F :: [Type]
x0F = tail xF

a, b, c, d :: Name
a = mkName "a"
b = mkName "b"
c = mkName "c"
d = mkName "d"

mkXT :: Name -> Dec
mkXT n = DataD [] n [PlainTV a] [] []

mkHT :: Name -> Dec
mkHT n = DataD [] n [] [] []

-- imports
tnot, positive, negative, signzero :: Name
tnot = mkName "TNot"
positive = mkName "Positive"
negative = mkName "Negative"
signzero = mkName "SignZero"

-- to be fleshed out when available
class LSN a d a' | a -> d a', d a' -> a
class Trichotomy n s | n -> s
class TEven a b | a -> b
class TSucc n m | n -> m, m -> n
class TAddC' a b c d | a b c -> d
class TNF' a b c | a -> b c
class THex a where fromTHex :: Integral b => a -> b
class SHR1 a b c | a b -> c
lsn, trichotomy, teven, tsucc, taddc', tnf', thex, shr1 :: Name
lsn = mkName "LSN"
trichotomy = mkName "Trichotomy"
teven = mkName "TEven"
tsucc = mkName "TSucc"
taddc' = mkName "TAddC'"
tnf' = mkName "TNF'"
thex = mkName "THex"
shr1 = mkName "SHR1"

wrapI :: [a] -> (a -> Type) -> [Dec]
wrapI list f = map (\v -> InstanceD [] (f v) []) list

concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f
