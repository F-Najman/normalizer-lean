import NormalizerDelta.DefsExtra

/-!
# X(N) additions (2026-10-10): definitions

Definitions for `StatementsXN.lean`: Γ(N), SL₂(ℤ) and normalizers inside GL₂⁺(ℚ), for the GL₂⁺(ℚ) form of the
modular automorphism group of X(N) (as for B₀(N) in `DefsExtra.lean`).  `NormalizerDelta/Defs.lean`,
`DefsExtra.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Γ(N) in GL₂⁺(ℚ). -/
def GammaQ (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := (CongruenceSubgroup.Gamma N).map toGLPosQ

/-- SL₂(ℤ) in GL₂⁺(ℚ). -/
def SL2ZQ : Subgroup (GLPos (Fin 2) ℚ) := (⊤ : Subgroup SL(2, ℤ)).map toGLPosQ

/-- The normalizer of a subgroup of GL₂⁺(ℚ). -/
abbrev NormGQ (Γ : Subgroup (GLPos (Fin 2) ℚ)) : Subgroup (GLPos (Fin 2) ℚ) :=
  Subgroup.normalizer (Γ : Set (GLPos (Fin 2) ℚ))

end

end NormalizerLean
