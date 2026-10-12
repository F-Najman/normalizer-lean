import NormalizerDelta.Defs

/-!
# Cartan modular curves (2026-10-10): definitions

The groups Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H} (they depend only on H ∩ SL₂(ℤ/N)) of the split and non-split Cartan
subgroups H and of their normalizers, defined by congruence conditions on the entries of γ = [[a, b], [c, d]]:
* Γ_sp(N): γ ≡ [[*, 0], [0, *]] mod N (C_sp = diagonal matrices);
* Γ_sp⁺(N): γ ≡ [[*, 0], [0, *]] or [[0, *], [*, 0]] mod N (diagonal or antidiagonal; for N = p an odd prime this is
  the normalizer C_sp⁺(p) of C_sp(p); for composite N it is in general a proper subgroup of the normalizer, and the
  statements use it only at prime level);
* Γ_ns(N, ε): γ ≡ [[a, εc], [c, a]] mod N (C_ns = {[[x, εy], [y, x]]}, the non-split Cartan subgroup when N = p is
  an odd prime and ε is not a square mod p, i.e. F_p[√ε]^× in the basis 1, √ε);
* Γ_ns⁺(N, ε): γ ≡ [[a, εc], [c, a]] or [[a, −εc], [c, −a]] mod N (C_ns⁺ = C_ns ∪ C_ns·diag(1, −1)).
Different non-squares ε give SL₂(ℤ)-conjugate groups.  Convention: Dose–Lido–Mercuri (arXiv:2005.09009) define Γ_H
with a transpose, so their Γ_{C_ns(ξ)} is `GammaNs p ξ⁻¹` here.
The curves are X_sp(N), X_sp⁺(N), X_ns(p), X_ns⁺(p); as before their modular automorphism groups are
`BG (toR Γ)` (all four groups contain −1).  `NormalizerDelta/Defs.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- The entries of γ⁻¹ = adj γ for γ ∈ SL₂(ℤ). -/
theorem SL2Z_inv_apply (γ : SL(2, ℤ)) :
    (γ⁻¹ : SL(2, ℤ)) 0 0 = γ 1 1 ∧ (γ⁻¹ : SL(2, ℤ)) 0 1 = -γ 0 1 ∧ (γ⁻¹ : SL(2, ℤ)) 1 0 = -γ 1 0 ∧
      (γ⁻¹ : SL(2, ℤ)) 1 1 = γ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]

/-- Γ_sp(N) = {γ ∈ SL₂(ℤ) : γ ≡ diagonal mod N}. -/
def GammaSp (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | ((γ 0 1 : ℤ) : ZMod N) = 0 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ γ' ⟨hb, hc⟩ ⟨hb', hc'⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hb, hc, hb', hc', mul_zero, zero_mul, add_zero,
      zero_add, and_self]
  inv_mem' := by
    rintro γ ⟨hb, hc⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hb, hc]

/-- Γ_sp⁺(N) = {γ ∈ SL₂(ℤ) : γ ≡ diagonal or antidiagonal mod N} (the normalizer of the split Cartan for N an odd
prime). -/
def GammaSpPlus (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | (((γ 0 1 : ℤ) : ZMod N) = 0 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0) ∨
    (((γ 0 0 : ℤ) : ZMod N) = 0 ∧ ((γ 1 1 : ℤ) : ZMod N) = 0)}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro γ γ' (⟨hb, hc⟩ | ⟨ha, hd⟩) (⟨hb', hc'⟩ | ⟨ha', hd'⟩)
    · left
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, hb, hc, hb', hc', mul_zero, zero_mul, add_zero, and_self]
    · right
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, hb, hc, ha', hd', mul_zero, zero_mul, add_zero, and_self]
    · right
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, ha, hd, hb', hc', mul_zero, zero_mul, add_zero, and_self]
    · left
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, ha, hd, ha', hd', mul_zero, zero_mul, add_zero, and_self]
  inv_mem' := by
    rintro γ (⟨hb, hc⟩ | ⟨ha, hd⟩)
    · exact Or.inl (by simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hb, hc])
    · exact Or.inr (by simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, ha, hd])

/-- Γ_ns(N, ε) = {γ ∈ SL₂(ℤ) : γ ≡ [[a, εc], [c, a]] mod N}. -/
def GammaNs (N : ℕ) (ε : ZMod N) : Subgroup SL(2, ℤ) where
  carrier := {γ | ((γ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) ∧
    ((γ 0 1 : ℤ) : ZMod N) = ε * ((γ 1 0 : ℤ) : ZMod N)}
  one_mem' := by simp
  mul_mem' := by
    rintro γ γ' ⟨hd, hb⟩ ⟨hd', hb'⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hd, hb, hd', hb']
    constructor <;> ring
  inv_mem' := by
    rintro γ ⟨hd, hb⟩
    obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply γ
    show (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = _ ∧ _
    rw [e00, e01, e10, e11]
    push_cast
    exact ⟨by linear_combination -hd, by linear_combination -hb⟩

/-- Γ_ns⁺(N, ε) = {γ ∈ SL₂(ℤ) : γ ≡ [[a, εc], [c, a]] or [[a, −εc], [c, −a]] mod N}. -/
def GammaNsPlus (N : ℕ) (ε : ZMod N) : Subgroup SL(2, ℤ) where
  carrier := {γ | (((γ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) ∧
      ((γ 0 1 : ℤ) : ZMod N) = ε * ((γ 1 0 : ℤ) : ZMod N)) ∨
    (((γ 1 1 : ℤ) : ZMod N) = -((γ 0 0 : ℤ) : ZMod N) ∧
      ((γ 0 1 : ℤ) : ZMod N) = -(ε * ((γ 1 0 : ℤ) : ZMod N)))}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro γ γ' (⟨hd, hb⟩ | ⟨hd, hb⟩) (⟨hd', hb'⟩ | ⟨hd', hb'⟩) <;>
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hd, hb, hd', hb']
    · exact Or.inl ⟨by ring, by ring⟩
    · exact Or.inr ⟨by ring, by ring⟩
    · exact Or.inr ⟨by ring, by ring⟩
    · exact Or.inl ⟨by ring, by ring⟩
  inv_mem' := by
    rintro γ h
    obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply γ
    show ((((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = _ ∧ _) ∨ _
    rw [e00, e01, e10, e11]
    push_cast
    rcases h with ⟨hd, hb⟩ | ⟨hd, hb⟩
    · exact Or.inl ⟨by linear_combination -hd, by linear_combination -hb⟩
    · exact Or.inr ⟨by linear_combination hd, by linear_combination -hb⟩

end

end NormalizerLean
