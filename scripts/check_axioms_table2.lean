module

import NormalizerDelta.Table2

open NormalizerLean

#print axioms card_BG_GammaDeltaR_hStar
#print axioms Table2.indices

example :
    Nat.card (BG (GammaDeltaR 49 (Table2.delta (ZMod.unitOfCoprime 27 (by decide))
      (ZMod.unitOfCoprime 1 (by decide))))) = 168 :=
  (Table2.indices 0).2.1

example :
    Nat.card (BG (GammaDeltaR 200 (Table2.delta (ZMod.unitOfCoprime 9 (by decide))
      (ZMod.unitOfCoprime 11 (by decide))))) = 480 :=
  (Table2.indices 24).2.1
