{-# OPTIONS -fglasgow-exts #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{--# OPTIONS -fallow-incoherent-instances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Type.Binary
-- Copyright   :  (C) 2006 Edward Kmett
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (FD and MPTC)
--
-- Simple type-level binary numbers, positive and negative with infinite 
-- precision. This forms a nice commutative ring with multiplicative identity
-- like we would expect from a representation for Z.
--
-- The numbers are represented as a Boolean Ring over a countable set of 
-- variables, in which for every element in the set there exists an n
-- such that there exists a B in {T,F} for all n' in N > n x_i = b.
-- for uniqueness we always choose the least such n when representing numbers
-- this allows us to run all computations backwards.
--
-- The goal here was to pull together all of the good ideas I've seen from
-- various sources, and sprinkle a twos complement negative number 
-- representation on top.
--
-- Reuses T and F from the Type.Boolean as the infinite tail of a 2s 
-- complement binary number. 
----------------------------------------------------------------------------

module Type.Binary (
	O, I, 				   -- zero or one digit
	TBinary, fromTBinary,		   -- Infinite precision binary
	TIsZero, TIsPositive, TIsNegative, -- Trichotomy
	tIsZero, tIsPositive, tIsNegative,
	LSB, tLSB, 
	TNeg, TNot, tNot, tNeg,
	TSucc, tSucc, tPred
) where

import Type.Boolean
import Type.Ord

data O a
data I a

-- | Internal closure, not exposed
data Closure
class Closed a | -> a
instance Closed Closure

class (TBool d) => LSB a d a' | a -> d a', d a' -> a
instance LSB F F F
instance LSB T T T
instance LSB (O T) F T
instance LSB (I F) T F
instance LSB (O (O n)) F (O n)
instance LSB (O (I n)) F (I n)
instance LSB (I (O n)) T (O n)
instance LSB (I (I n)) T (I n)
tLSB :: LSB a d a' => a -> d -> a'; tLSB = undefined
tBSL :: LSB a d a' => a' -> d -> a; tBSL = undefined

-- | extract the lsb and assert we aren't at the long tail
class LSB a d a' => X a d a' | a -> d a', d a' -> a, a a' -> d
instance (LSB (O a) F a) => X (O a) F a
instance (LSB (I a) T a) => X (I a) T a

-- | assert 2n !=n
class LSB (O a) F a => XO a
instance (LSB (O a) F a) => XO a

-- | assert 2n+1 !=n
class LSB (I a) T a => XI a
instance (LSB (I a) T a) => XI a

class TSucc n m | n -> m, m -> n
instance TSucc T F
instance TSucc F (I F)
instance TSucc (O T) T
instance TSucc (O (I n)) (I (I n))
instance TSucc (O (O n)) (I (O n))
instance (TSucc n m, XI n, XO m) => TSucc (I n) (O m)
tSucc :: TSucc n m => n -> m
tSucc = undefined
tPred :: TSucc n m => m -> n
tPred = undefined

instance Show (O F) where show n = "({-error-} O F)";
instance Show (I T) where show n = "({-error-} I T)";
instance Show (I F) where show n = "I F";
instance Show (O T) where show n = "O T";
instance (Show (I t)) => Show (O (I t)) where show n = "O (" ++ show (undefined::I t) ++ ")"
instance (Show (I t)) => Show (I (I t)) where show n = "I (" ++ show (undefined::I t) ++ ")" 
instance (Show (O t)) => Show (O (O t)) where show n = "O (" ++ show (undefined::O t) ++ ")"
instance (Show (O t)) => Show (I (O t)) where show n = "I (" ++ show (undefined::O t) ++ ")"

class TCBinary c a | a -> c
instance TCBinary Closure F
instance TCBinary Closure T
instance (TCBinary c a, XO a) => TCBinary c (O a)
instance (TCBinary c a, XI a) => TCBinary c (I a)

class TCBinary Closure a => TBinary a where fromTBinary :: Integral b => a -> b 
instance TBinary F where fromTBinary _ = fromInteger 0
instance TBinary T where fromTBinary _ = fromInteger (-1)
instance (TBinary a, XO a) => TBinary (O a) where fromTBinary _ = let x = fromTBinary (undefined::a) in x+x
instance (TBinary a, XI a) => TBinary (I a) where fromTBinary _ = let x = fromTBinary (undefined::a) in succ(x+x)

instance (TNot a b) => TNot (O a) (I b)
instance (TNot a b) => TNot (I a) (O b)

neg_two  = undefined :: O T
neg_one	 = undefined :: T
zero 	 = undefined :: F
one 	 = undefined :: I F
two 	 = undefined :: O(I F)
three	 = undefined :: I(I F)
four 	 = undefined :: O(O(I F))
five     = undefined :: I(O(I F))
six  	 = undefined :: O(I(I F))
seven 	 = undefined :: I(I(I F))
eight :: O(O(O(I F))); eight = undefined
nine     = undefined :: I(O(O(I F)))
ten      = undefined :: O(I(O(I F)))
eleven   = undefined :: I(I(O(I F)))
twelve   = undefined :: O(O(I(I F)))
thirteen = undefined :: I(O(I(I F)))
fourteen = undefined :: O(O(I(I F)))
fifteen  = undefined :: I(O(I(I F)))
sixteen :: O(O(O(O(I F))));sixteen  = undefined
seventeen= undefined :: I(O(O(O(I F))))
eighteen = undefined :: O(I(O(O(I F))))
nineteen = undefined :: I(I(O(O(I F))))
twenty_  = undefined :: O(O(I(O(I F))))
--twenty _ = undefined :: TAdd O(O(I(O(I F)))) a b => a -> b

instance TEq (I m) (O n) F
instance TEq (O m) (I n) F
instance TEq (O m) F F
instance TEq (O m) T F
instance TEq (I m) T F
instance TEq (I m) F F
instance (TEq m n b) => TEq (I m) (I n) b
instance (TEq m n b) => TEq (O m) (O n) b

class TNeg a b | a -> b, b -> a
instance (TNot a b, TSucc b c) => TNeg a c
tNeg :: TNeg a b => a -> b
tNeg = undefined

data IsNegative
data IsZero
data IsPositive

class TCSign c a | a -> c
instance TCSign Closure IsNegative
instance TCSign Closure IsPositive
instance TCSign Closure IsZero

class TCSign Closure s => TSign s
instance TSign IsNegative
instance TSign IsZero
instance TSign IsPositive

instance TEq IsNegative IsNegative T
instance TEq IsNegative IsZero F
instance TEq IsNegative IsPositive F
instance TEq IsZero IsNegative F
instance TEq IsZero IsZero T
instance TEq IsZero IsPositive F
instance TEq IsPositive IsNegative F
instance TEq IsPositive IsZero F
instance TEq IsPositive IsPositive T

class Trichotomy n s | n -> s
instance Trichotomy T IsNegative
instance Trichotomy F IsZero
instance Trichotomy (I F) IsPositive
instance Trichotomy (O T) IsNegative
instance (Trichotomy a b, XI a) => Trichotomy (I (I a)) b
instance (Trichotomy a b, XI a) => Trichotomy (O (I a)) b
instance (Trichotomy a b, XO a) => Trichotomy (I (O a)) b
instance (Trichotomy a b, XO a) => Trichotomy (O (O a)) b

class TIsPositive n b | n -> b
instance (Trichotomy n s, TEq s IsPositive b)  => TIsPositive n b
tIsPositive :: TIsPositive n b => n -> b; tIsPositive = undefined 

class TIsNegative n b | n -> b
instance (Trichotomy n s, TEq s IsNegative b)  => TIsNegative n b
tIsNegative :: TIsNegative n b => n -> b; tIsNegative = undefined

class TIsZero n b | n -> b
instance (Trichotomy n s, TEq s IsZero b)  => TIsZero n b
tIsZero :: TIsZero n b => n -> b; tIsZero = undefined 

class TEven a b | a -> b
instance LSB a b c => TEven a b
tEven :: (TEven a b) => a -> b; tEven = undefined

class TOdd a b | a -> b
instance (LSB a b c, TNot b b') => TOdd a b'
tOdd :: (TOdd a b) => a -> b; tOdd = undefined

-- | nice adder with carry. does not yield normal form answers.
class TAddC a b c d | a b c -> d
instance TAddC F F F F 
instance TAddC T F T F
instance TAddC F T F T 
instance TAddC T T T T
instance TAddC T F F T
instance TAddC F T T F
instance TAddC F F T (I F) 
instance TAddC T T F (O T)
instance TAddC F (O a) F (O a) 
instance TAddC T (O a) T (O a)
instance TAddC F (I a) F (I a) 
instance TAddC T (I a) T (I a)
instance TAddC (O a) F F (O a) 
instance TAddC (O a) T T (O a)
instance TAddC (I a) F F (I a) 
instance TAddC (I a) T T (I a)
instance TAddC F (O a) T (I a) 
instance TAddC T (I a) F (O a)
instance TAddC (O a) F T (I a) 
instance TAddC (I a) T F (O a)
instance TSucc a b => TAddC F (I a) T (O b) 
instance TSucc b a => TAddC T (O a) F (I b)
instance TSucc a b => TAddC (I a) F T (O b) 
instance TSucc b a => TAddC (O a) T F (I b)
instance TAddC a b F c => TAddC (O a) (O b) F (O c) 
instance TAddC a b F c => TAddC (O a) (O b) T (I c)
instance TAddC a b F c => TAddC (I a) (O b) F (I c) 
instance TAddC a b T c => TAddC (I a) (O b) T (O c)
instance TAddC a b F c => TAddC (O a) (I b) F (I c) 
instance TAddC a b T c => TAddC (O a) (I b) T (O c)
instance TAddC a b T c => TAddC (I a) (I b) F (O c) 
instance TAddC a b T c => TAddC (I a) (I b) T (I c)
tAddC :: TAddC a b c d => a -> b -> c -> d
tAddC = undefined

class TNF' a b c | a -> b c
instance TNF' F F F
instance TNF' T T F
instance TNF' (O F) F F
instance TNF' (I T) T F
instance TNF' (I F) (I F) T
instance TNF' (O T) (O T) T
instance (TNF' (I a) c b, TIf b (I c) T d) => TNF' (I (I a)) d b
instance (TNF' (O a) c b, TIf b (O c) F d) => TNF' (O (O a)) d b
instance (TNF' (O a) c b) 		   => TNF' (I (O a)) (I c) T
instance (TNF' (I a) c b) 		   => TNF' (O (I a)) (O c) T

class TNF a b | a -> b
instance TNF' a b c => TNF a b
tNF :: TNF a b => a -> b
tNF = undefined
tAdd :: (TAddC a b F d, TNF d d') => a -> b -> d'
tAdd = undefined

