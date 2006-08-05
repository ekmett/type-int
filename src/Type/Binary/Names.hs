module Type.Binary.Names (
	neg_two, neg_one, zero, one, two, three, four, five, six, seven, eight, nine, ten,
	eleven, twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen,
	twenty, thirty, forty, fifty, sixty, seventy, eighty, ninety, hundred,
	twenty_, thirty_, forty_, fifty_, sixty_, seventy_, eighty_, ninety_
) where
import Type.Binary.Internals
import Type.Boolean

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
eight    = undefined :: O(O(O(I F)))
nine     = undefined :: I(O(O(I F)))
ten      = undefined :: O(I(O(I F)))
eleven   = undefined :: I(I(O(I F)))
twelve   = undefined :: O(O(I(I F)))
thirteen = undefined :: I(O(I(I F)))
fourteen = undefined :: O(O(I(I F)))
fifteen  = undefined :: I(O(I(I F)))
sixteen  = undefined :: O(O(O(O(I F))))
seventeen= undefined :: I(O(O(O(I F))))
eighteen = undefined :: O(I(O(O(I F))))
nineteen = undefined :: I(I(O(O(I F))))
twenty  :: TAdd (O(O(I(O(I F))))) b c => b -> c;	    twenty  = undefined; twenty_ = twenty zero
thirty  :: TAdd (O(I(I(I(I F))))) b c => b -> c;	    thirty  = undefined; thirty_ = thirty zero
forty   :: TAdd (O(O(O(I(O(I F)))))) b c => b -> c; 	    forty   = undefined; forty_ = forty zero
fifty   :: TAdd (O(I(O(O(I(I F)))))) b c => b -> c; 	    fifty   = undefined; fifty_ = fifty zero
sixty   :: TAdd (O(O(I(I(I(I F)))))) b c => b -> c; 	    sixty   = undefined; sixty_ = sixty zero
seventy :: TAdd (O(I(I(O(O(O(I F))))))) b c => b -> c;      seventy = undefined; seventy_ = seventy zero
eighty  :: TAdd (O(O(O(O(I(O(I F))))))) b c => b -> c;      eighty  = undefined; eighty_ = eighty zero
ninety  :: TAdd (O(I(O(I(I(O(I F))))))) b c => b -> c;      ninety  = undefined; ninety_ = ninety zero
hundred :: (TAdd a' b c, TMul a (O(O(I(O(O(I(I F))))))) a') => a -> b -> c
hundred = undefined;
