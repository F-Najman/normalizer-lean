import NormalizerDelta.DefsXN

/-!
# General modular curves (2026-10-10): definitions

Definitions for `StatementsGeneral.lean`.  A modular curve of level N is X_H = Γ_H\ℍ* for a subgroup H ≤ SL₂(ℤ/N),
Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}.  (For H ≤ GL₂(ℤ/N) with det H = (ℤ/N)ˣ, as in Dose–Lido–Mercuri,
arXiv:2610.08998, Γ_H only depends on H ∩ SL₂(ℤ/N); every congruence subgroup Γ ⊇ Γ(N) is a Γ_H,
`GammaH_map`.)  The statements are about `BG (toR (GammaH N H))` = Nor(Γ_H)/Γ_H.  For −1 ∈ H this is the modular
automorphism group of X_H; for −1 ∉ H the curve's group is the one for H ⊔ {±1} (as for Γ(N) and Γ₁(N) in
`NormalizerDelta/Defs.lean`).

The local conditions are about the reduction of H modulo q ∣ N, computed entrywise with `ZMod.cast`
(for q ∣ N this is the reduction map ℤ/N → ℤ/q; the statements only use it for q ∣ N, or where q ∣ N follows
from the other hypotheses):
* `FixesLine H q v`: every h ∈ H maps v ∈ (ℤ/q)² to a multiple of v;
* `IsBorelMod H q`: H mod q lies in a Borel subgroup, i.e. fixes the line spanned by a unimodular vector
  (for q = p^k: a vector with v mod p ≠ 0);
* `IsSplitMod H q`: H mod q lies in a split Cartan subgroup, i.e. fixes the lines spanned by v and w with
  det [v w] a unit (equivalently: H mod q is conjugate in GL₂(ℤ/q) into the diagonal matrices);
* `FixesUniqueLine H` (prime level): H fixes exactly one line of F_p².
`NormalizerDelta/Defs.lean` and all earlier definitions and statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}, for H ≤ SL₂(ℤ/N). -/
def GammaH (N : ℕ) (H : Subgroup SL(2, ZMod N)) : Subgroup SL(2, ℤ) := H.comap (redSL N)

/-- The normalizer N(H) of H in SL₂(ℤ/N). -/
abbrev NormH {N : ℕ} (H : Subgroup SL(2, ZMod N)) : Subgroup SL(2, ZMod N) :=
  Subgroup.normalizer (H : Set SL(2, ZMod N))

instance {N : ℕ} (H : Subgroup SL(2, ZMod N)) : (H.subgroupOf (NormH H)).Normal :=
  Subgroup.normal_in_normalizer

/-- N(H)/H. -/
abbrev QH {N : ℕ} (H : Subgroup SL(2, ZMod N)) : Type := NormH H ⧸ H.subgroupOf (NormH H)

/-- H mod q fixes the line through v ∈ (ℤ/q)²: for every h ∈ H, (h mod q) v ∈ (ℤ/q)·v. -/
def FixesLine {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) (v : Fin 2 → ZMod q) : Prop :=
  ∀ h ∈ H, ∃ c : ZMod q,
    (h : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ZMod q) *ᵥ v = c • v

/-- H mod q lies in a Borel subgroup of GL₂(ℤ/q): it fixes the line through a unimodular v
(a v₀ + b v₁ = 1 for some a, b). -/
def IsBorelMod {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) : Prop :=
  ∃ v : Fin 2 → ZMod q, (∃ a b : ZMod q, a * v 0 + b * v 1 = 1) ∧ FixesLine H q v

/-- H mod q lies in a split Cartan subgroup of GL₂(ℤ/q): it fixes the lines through v and w, where
det [v w] = v₀w₁ − v₁w₀ is a unit. -/
def IsSplitMod {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) : Prop :=
  ∃ v w : Fin 2 → ZMod q, FixesLine H q v ∧ FixesLine H q w ∧ IsUnit (v 0 * w 1 - v 1 * w 0)

/-- H ≤ SL₂(ℤ/p) fixes exactly one line of (ℤ/p)² (used for p prime). -/
def FixesUniqueLine {p : ℕ} (H : Subgroup SL(2, ZMod p)) : Prop :=
  ∃ v : Fin 2 → ZMod p, v ≠ 0 ∧ FixesLine H p v ∧ ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • v

/-- The Fricke involution W_p = (1/√p)·[[0, −1], [p, 0]] ∈ SL₂(ℝ). -/
def frickeP (p : ℕ) : SL(2, ℝ) := projSL !![0, -1; (p : ℝ), 0]

end

end NormalizerLean
