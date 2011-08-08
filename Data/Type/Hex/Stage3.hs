{-# LANGUAGE TemplateHaskell, CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Type.Hex.Stage3
-- Copyright   :  (C) 2006-2011 Edward Kmett
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (MPTC, FD, TH, undecidable instances, missing constructors)
--
-- Stage3: Define everything else. The juicier bits are then exposed via "Data.Type.Hex"
-----------------------------------------------------------------------------

module Data.Type.Hex.Stage3 where

import Data.Type.Boolean
import Control.Monad
import Data.Type.Hex.Stage1
import Data.Type.Hex.Stage2
import Data.Type.Sign
import Data.Type.Ord
import Data.Bits
import Language.Haskell.TH
import qualified Data.Type.Binary as B

instance TSucc T F
instance TSucc F (D1 F)
instance TSucc (DE T) T
instance (TSucc n m, ExtF n, Ext0 m) => TSucc (DF n) (D0 m)

return $ wrapI (zip (init x0) (tail x0))
                  $ \(x1,x2) -> ConT tsucc
                                `AppT` AppT x1 (ConT f)
                                `AppT` AppT x2 (ConT f)
return $ wrapI (zip (init xF) (tail xF))
                  $ \(x1,x2) -> ConT tsucc
                                `AppT` AppT x1 (ConT t)
                                `AppT` AppT x2 (ConT t)
return $ wrapI (liftM2 (,) (zip xF x0) x)
                  $ \((xn, xm), x) ->
                      let b = AppT x (VarT a)
                      in ConT tsucc
                         `AppT` AppT xn b
                         `AppT` AppT xm b
tSucc :: TSucc n m => n -> m; tSucc = undefined
tPred :: TSucc n m => m -> n; tPred = undefined

class TNeg a b | a -> b, b -> a
instance (TNot a b, TSucc b c) => TNeg a c
tNeg :: TNeg a b => a -> b; tNeg = undefined

instance Trichotomy T Negative
instance Trichotomy F SignZero
return $ wrapI x0 $ \x ->
                        ConT trichotomy
                        `AppT` AppT x (ConT f)
                        `AppT` ConT positive
return $ wrapI xF $ \x ->
                        ConT trichotomy
                        `AppT` AppT x (ConT t)
                        `AppT` ConT negative 
let es = [extf, ext0]
    ext0 = mkName "Ext0"
    extf = mkName "ExtF"
    df = mkName "DF"
 in return $ flip map (zip x es)
                    $ \(x, e) ->
                              InstanceD [ClassP trichotomy [VarT a, VarT b],
                                         ClassP e [VarT a]]
                                        (ConT trichotomy
                                         `AppT` (x `AppT` (ConT df `AppT` VarT a))
                                         `AppT` VarT b)
                                        []

class TIsPositive n b | n -> b
instance (Trichotomy n s, TEq s Positive b) => TIsPositive n b
tIsPositive :: TIsPositive n b => n -> b; tIsPositive = undefined

class TIsNegative n b | n -> b
instance (Trichotomy n s, TEq s Negative b) => TIsNegative n b
tIsNegative :: TIsNegative n b => n -> b; tIsNegative = undefined

class TIsZero n b | n -> b
instance (Trichotomy n s, TEq s SignZero b) => TIsZero n b
tIsZero :: TIsZero n b => n -> b; tIsZero = undefined

instance TAddC' F F F F
instance TAddC' T F T F
instance TAddC' F T F T
instance TAddC' T T T T
instance TAddC' T F F T
instance TAddC' F T T F
instance TAddC' F F T (D1 F)
instance TAddC' T T F (DE T)
instance TSucc a b => TAddC' F (DF a) T (D0 b)
instance TSucc b a => TAddC' T (D0 a) F (DF b)
instance TSucc a b => TAddC' (DF a) F T (D0 b)
instance TSucc b a => TAddC' (D0 a) T F (DF b)
return $ wrapI (liftM2 (,) [t, f] x)
                  $ \(tf, dx) ->
                      let dxa = AppT dx (VarT a)
                      in ConT taddc'
                         `AppT` ConT tf
                         `AppT` dxa
                         `AppT` ConT tf
                         `AppT` dxa
return $ wrapI (liftM2 (,) [t, f] x)
                  $ \(tf, dx) ->
                      let dxa = AppT dx (VarT a)
                      in ConT taddc'
                         `AppT` dxa
                         `AppT` ConT tf
                         `AppT` ConT tf
                         `AppT` dxa
return $ wrapI (zip xF x0)
                  $ \(dn, dm) ->
                      ConT taddc'
                      `AppT` ConT f
                      `AppT` AppT dn (VarT a)
                      `AppT` ConT t
                      `AppT` AppT dm (VarT a)
return $ wrapI (zip xF x0)
                  $ \(dn, dm) ->
                      ConT taddc'
                      `AppT` ConT t
                      `AppT` AppT dm (VarT a)
                      `AppT` ConT f
                      `AppT` AppT dn (VarT a)
return $ wrapI (zip xF x0)
                  $ \(dn, dm) ->
                      ConT taddc'
                      `AppT` AppT dn (VarT a)
                      `AppT` ConT f
                      `AppT` ConT t
                      `AppT` AppT dm (VarT a)
return $ wrapI (zip xF x0)
                  $ \(dn, dm) ->
                      ConT taddc'
                      `AppT` AppT dm (VarT a)
                      `AppT` ConT t
                      `AppT` ConT f
                      `AppT` AppT dn (VarT a)
return $ (flip map)
            (liftM3 (,,) (zip x [0..15]) (zip x [0..15]) [(f, 0), (t, 1)])
            $ \((x0, n0), (x1, n1), (thing1, thing2)) ->
                let total = n0 + n1 + thing2
                    pcarry = if total > 15 then t else f
                    x2 = x !! (total `mod` 16)
                in InstanceD [ClassP taddc'
                                     [VarT a, VarT b, ConT pcarry, VarT c]]
                             (ConT taddc'
                              `AppT` AppT x0 (VarT a)
                              `AppT` AppT x1 (VarT b)
                              `AppT` ConT thing1
                              `AppT` AppT x2 (VarT c))
                             []
tAddC' :: TAddC' a b c d => a -> b -> c -> d; tAddC' = undefined
tAddF' :: TAddC' a b F d => a -> b -> d; tAddF' = undefined

class TNF a b | a -> b
instance TNF' a b c => TNF a b
tNF   :: TNF a b => a -> b;     tNF = undefined

class TAdd' a b c | a b -> c
instance (TAddC' a b F d, TNF d d') => TAdd' a b d'
tAdd' :: (TAdd' a b c ) => a -> b -> c; tAdd' = undefined

class TSub' a b c | a b -> c
instance (TNeg b b', TAdd' a b' c) => TSub' a b c
tSub' :: TSub' a b c => a -> b -> c; tSub' = undefined

class TAdd a b c | a b -> c, a c -> b, b c -> a
instance (TAdd' a b c, TNeg b b', TAdd' c b' a, TNeg a a', TAdd' c a' b) => TAdd a b c
tAdd :: (TAdd a b c) => a -> b -> c;tAdd = undefined
tSub :: (TAdd a b c) => c -> a -> b;tSub = undefined

-- | $(hexT n) returns the appropriate THex instance
hexT :: Integral a => a -> Type
hexT n = case n of
    0  -> ConT f
    -1 -> ConT t
    n  -> AppT (x !! mod (fromIntegral n) 16) $ hexT $ n `div` 16

-- | $(hexE n) returns an undefined value of the appropriate THex instance
hexE :: Integral a => a -> Exp
hexE n = SigE (VarE $ mkName "undefined") $ hexT n

instance THex (D0 a) => Show (D0 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D1 a) => Show (D1 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D2 a) => Show (D2 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D3 a) => Show (D3 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D4 a) => Show (D4 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D5 a) => Show (D5 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D6 a) => Show (D6 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D7 a) => Show (D7 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D8 a) => Show (D8 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (D9 a) => Show (D9 a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DA a) => Show (DA a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DB a) => Show (DB a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DC a) => Show (DC a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DD a) => Show (DD a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DE a) => Show (DE a) where show n = "$(hexE "++ (show $ fromTHex n)++")"
instance THex (DF a) => Show (DF a) where show n = "$(hexE "++ (show $ fromTHex n)++")"

instance SHR1 H0 F F
instance SHR1 H1 F (D1 F)
instance SHR1 H0 T (DE T)
instance SHR1 H1 T (DE T)
return $ wrapI (liftM3 (,,)
                          (zip x [0..15])
                          (zip h [0..1])
                          (zip [t, f] [15, 0]))
                  $ \((d, dn), (c, cn), (tf, tfn)) ->
                      let dlsn = x !! ((dn*2+cn) `mod` 16)
                          dmsn = x !! (((dn `div` 8) + tfn*2) `mod` 16)
                          nmsn = dn `div` 8
                          dcase = if ((tfn .&. 1) `xor` nmsn) /= 0
                                    then AppT dmsn (ConT tf)
                                    else ConT tf
                      in ConT shr1
                         `AppT` c
                         `AppT` AppT d (ConT tf)
                         `AppT` AppT dlsn dcase
return $ (flip map)
            (liftM3 (,,)
                    (zip x [0..15])
                    (zip h [0..1])
                    (zip x [0..15]))
            $ \((dm, dmi), (c, cn), (dn, dni)) ->
                let msb_m = dmi `div` 8
                    dn' = x !! ((msb_m + (dni*2)) `mod` 16)
                    dm' = x !! ((cn + (dmi*2)) `mod` 16)
                    pre_c = h !! msb_m
                    dna = AppT dn (VarT a)
                    dn'b = AppT dn' (VarT b)
                in InstanceD [ClassP shr1 [pre_c, dna, dn'b]]
                             (ConT shr1
                              `AppT` c
                              `AppT` AppT dm dna
                              `AppT` AppT dm' dn'b)
                             []

-- | A simple peasant multiplier. TODO: exploit 2s complement and reverse the worst cases
class TMul a b c | a b -> c
instance TMul a F F 
instance TNeg a b => TMul a T b
instance TMul (D0 a1) b c => TMul a1 (D0 b) c
instance ( TMul (D0 a1) b c
     , TAdd' a1 c d) => TMul a1 (D1 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , TAdd' a2 c d) => TMul a1 (D2 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , TAdd' a1 a2 a3
     , TAdd' a3 c d) => TMul a1 (D3 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , TAdd' a4 c d) => TMul a1 (D4 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , TAdd' a1 a4 a5
     , TAdd' a5 c d) => TMul a1 (D5 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , TAdd' a2 a4 a6
     , TAdd' a6 c d) => TMul a1 (D6 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , TAdd' a2 a4 a6
     , TAdd' a1 a6 a7
     , TAdd' a7 c d) => TMul a1 (D7 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a8 c d) => TMul a1 (D8 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a1 a8 a9
     , TAdd' a9 c d) => TMul a1 (D9 b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a2 a8 aA
     , TAdd' aA c d) => TMul a1 (DA b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a2 a8 a0 
     , TAdd' a1 a0 aB
     , TAdd' aB c d) => TMul a1 (DB b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a4 a8 aC
     , TAdd' aC c d) => TMul a1 (DC b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a4 a8 aC
     , TAdd' a1 aC aD
     , TAdd' aD c d) => TMul a1 (DD b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a4 a8 aC
     , TAdd' a2 aC aE
     , TAdd' aE c d) => TMul a1 (DE b) d
instance ( TMul (D0 a1) b c
     , SHR1 H0 a1 a2
     , SHR1 H0 a2 a4
     , SHR1 H0 a4 a8
     , TAdd' a4 a8 aC
     , TAdd' a2 aC aE
     , TAdd' a1 aE aF
     , TAdd' aF c d) => TMul a1 (DF b) d

tMul :: TMul a b c => a -> b -> c
tMul = undefined

class THex2Binary' a b | a -> b, b -> a
instance THex2Binary' F F 
instance THex2Binary' T T
instance THex2Binary' a b => THex2Binary' (D0 a) (B.O(B.O(B.O(B.O b))))
instance THex2Binary' a b => THex2Binary' (D1 a) (B.I(B.O(B.O(B.O b))))
instance THex2Binary' a b => THex2Binary' (D2 a) (B.O(B.I(B.O(B.O b))))
instance THex2Binary' a b => THex2Binary' (D3 a) (B.I(B.I(B.O(B.O b))))
instance THex2Binary' a b => THex2Binary' (D4 a) (B.O(B.O(B.I(B.O b))))
instance THex2Binary' a b => THex2Binary' (D5 a) (B.I(B.O(B.I(B.O b))))
instance THex2Binary' a b => THex2Binary' (D6 a) (B.O(B.I(B.I(B.O b))))
instance THex2Binary' a b => THex2Binary' (D7 a) (B.I(B.I(B.I(B.O b))))
instance THex2Binary' a b => THex2Binary' (D8 a) (B.O(B.O(B.O(B.I b))))
instance THex2Binary' a b => THex2Binary' (D9 a) (B.I(B.O(B.O(B.I b))))
instance THex2Binary' a b => THex2Binary' (DA a) (B.O(B.I(B.O(B.I b))))
instance THex2Binary' a b => THex2Binary' (DB a) (B.I(B.I(B.O(B.I b))))
instance THex2Binary' a b => THex2Binary' (DC a) (B.O(B.O(B.I(B.I b))))
instance THex2Binary' a b => THex2Binary' (DD a) (B.I(B.O(B.I(B.I b))))
instance THex2Binary' a b => THex2Binary' (DE a) (B.O(B.I(B.I(B.I b))))
instance THex2Binary' a b => THex2Binary' (DF a) (B.I(B.I(B.I(B.I b))))

class THex2Binary a b | a -> b
instance (THex2Binary' a b, B.TNF b b') => THex2Binary a b'
tHex2Binary :: THex2Binary a b => a -> b; tHex2Binary = undefined

class TBinary2Hex a b | a -> b
instance (THex2Binary' a b, TNF a a') => TBinary2Hex b a'
tBinary2Hex :: TBinary2Hex a b => a -> b; tBinary2Hex = undefined

class THexBinary a b | a -> b, b -> a
instance (THex2Binary a b, TBinary2Hex b a) => THexBinary a b

-- | peasant exponentiator with explicit binary exponent
class TPow' a b c | a b -> c
instance TPow' a F (D1 F)
instance (TPow' a k c, TMul c c d) => TPow' a (B.O k) d
instance (TPow' a k c, TMul c c d, TMul a d e) => TPow' a (B.I k) e

-- | peasant exponentiator
class TPow a b c | a b -> c
instance (THex2Binary b b', TPow' a b' c) => TPow a b c
tPow :: TPow a b c => a -> b -> c
tPow = undefined
