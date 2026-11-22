import NormalizerDelta.Table1

open NormalizerLean

#print axioms Table1.indices

example :
    Nat.card (BG (GammaDeltaR 37 (Table1.delta (ZMod.unitOfCoprime 8 (by decide))
      (ZMod.unitOfCoprime 1 (by decide)) (ZMod.unitOfCoprime 1 (by decide))))) = 6 :=
  (Table1.indices 14).2

example :
    Nat.card (BG (GammaDeltaR 63 (Table1.delta (ZMod.unitOfCoprime 59 (by decide))
      (ZMod.unitOfCoprime 37 (by decide)) (ZMod.unitOfCoprime 1 (by decide))))) = 48 :=
  (Table1.indices 30).2
