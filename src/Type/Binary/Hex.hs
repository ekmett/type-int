module Type.Binary.Hex (
	Ox0, Ox1, Ox2, Ox3, 
	Ox4, Ox5, Ox6, Ox7,
	Ox8, Ox9, OxA, OxB,
	OxC, OxD, OxE, OxF
) where

import Type.Binary (O(..), I(..))

type Ox0 a = O (O (O (O a)))
type Ox1 a = I (O (O (O a)))
type Ox2 a = O (I (O (O a)))
type Ox3 a = I (I (O (O a)))
type Ox4 a = O (O (I (O a)))
type Ox5 a = I (O (I (O a)))
type Ox6 a = O (I (I (O a)))
type Ox7 a = I (I (I (O a)))
type Ox8 a = O (O (O (I a)))
type Ox9 a = I (O (O (I a)))
type OxA a = O (I (O (I a)))
type OxB a = I (I (O (I a)))
type OxC a = O (O (I (I a)))
type OxD a = I (O (I (I a)))
type OxE a = O (I (I (I a)))
type OxF a = I (I (I (I a)))

