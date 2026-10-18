module

public import NormalizerDelta.CartanNonsplit

@[expose] public section

/-!
# §N: [SL₂(ℤ) : Γ_ns(p)] = p(p − 1)

* The conic a² − εc² = 1 over F_p (ε not a square) has p + 1 points: t ↦ ((1 + εt²)/(1 − εt²), 2t/(1 − εt²))
  together with (−1, 0) is a bijection from F_p ∪ {∞} (`conicEquiv`; the inverse is (a, c) ↦ c/(a + 1)).
* The image of Γ_ns(p) in SL₂(F_p) is {[[a, εc], [c, a]] : a² − εc² = 1} (reduction is onto), with kernel Γ(p), so
  [Γ_ns(p) : Γ(p)] = p + 1, and [SL₂(ℤ) : Γ(p)] = p(p² − 1) gives the index.
-/

open Matrix MatrixGroups

-- As in `CartanNonsplit.lean`: Mathlib v4.35.0-rc3's instance making `ZMod p` an `AddCommGroup` breaks `ring` on
-- negations.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace NormalizerLean

noncomputable section

section

variable {p : ℕ} [Fact p.Prime]

theorem conic_param_mem {ε : ZMod p} (hε : ¬ IsSquare ε) (t : ZMod p) :
    ((1 + ε * t ^ 2) / (1 - ε * t ^ 2)) ^ 2 - ε * (2 * t / (1 - ε * t ^ 2)) ^ 2 = 1 := by
  have hD := one_sub_ne_zero hε t
  field_simp
  ring

/-- F_p ∪ {∞} ≃ the conic a² − εc² = 1. -/
def conicEquiv (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Option (ZMod p) ≃ {x : ZMod p × ZMod p // x.1 ^ 2 - ε * x.2 ^ 2 = 1} where
  toFun o := o.elim ⟨(-1, 0), by ring⟩
    (fun t => ⟨((1 + ε * t ^ 2) / (1 - ε * t ^ 2), 2 * t / (1 - ε * t ^ 2)), conic_param_mem hε t⟩)
  invFun x := if x.1.1 = -1 then none else some (x.1.2 / (x.1.1 + 1))
  left_inv o := by
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (by have := (Fact.out : p.Prime).two_le; omega)
    rcases o with _ | t
    · simp
    · have hD := one_sub_ne_zero hε t
      have hne : (1 + ε * t ^ 2) / (1 - ε * t ^ 2) ≠ -1 := by
        intro h
        rw [div_eq_iff hD] at h
        apply h2; linear_combination h
      simp only [Option.elim_some, hne, if_false, Option.some.injEq]
      have key : (1 + ε * t ^ 2) / (1 - ε * t ^ 2) + 1 = 2 / (1 - ε * t ^ 2) := by
        field_simp; ring
      rw [key, div_div_div_cancel_right₀ hD, mul_div_cancel_left₀ t h2]
  right_inv x := by
    obtain ⟨⟨a, c⟩, h⟩ := x
    have hε0 := not_isSquare_ne_zero hε
    by_cases ha : a = -1
    · have hc : c = 0 := by
        rw [ha] at h
        have : ε * c ^ 2 = 0 := by linear_combination -h
        exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left hε0)
      simp only [ha, if_true, Option.elim_none]
      subst ha hc
      rfl
    · simp only [ha, if_false, Option.elim_some]
      have hu : a + 1 ≠ 0 := fun h' => ha (eq_neg_of_add_eq_zero_left h')
      have hD := one_sub_ne_zero hε (c / (a + 1))
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      constructor
      · rw [div_eq_iff hD]
        field_simp
        linear_combination (-(a + 1)) * h
      · rw [div_eq_iff hD]
        field_simp
        linear_combination (-c) * h

theorem card_conic (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Nat.card {x : ZMod p × ZMod p // x.1 ^ 2 - ε * x.2 ^ 2 = 1} = p + 1 := by
  rw [← Nat.card_congr (conicEquiv hp2 hε), Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

/-- Reduction mod p on Γ_ns(p). -/
def nsRed (ε : ZMod p) : GammaNs p ε →* SL(2, ZMod p) := (redSL p).comp (GammaNs p ε).subtype

theorem nsRed_ker (ε : ZMod p) : (nsRed ε).ker = (CongruenceSubgroup.Gamma p).subgroupOf (GammaNs p ε) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, CongruenceSubgroup.Gamma_mem']
  rfl

theorem mem_range_nsRed {ε : ZMod p} {x : SL(2, ZMod p)} :
    x ∈ (nsRed ε).range ↔ (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = ε * (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · rintro ⟨⟨γ, hγ⟩, rfl⟩
    show ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 =
        ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ∧
      ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 =
        ε * ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0
    simp only [redSL_apply]
    exact hγ
  · rintro ⟨h1, h2⟩
    obtain ⟨γ, hγ⟩ := redSL_surjective p x
    have hent : ∀ i j, ((γ i j : ℤ) : ZMod p) = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := by
      intro i j; rw [← hγ, redSL_apply]
    exact ⟨⟨γ, by rw [GammaNs]; exact ⟨by rw [hent, hent, h1], by rw [hent, hent, h2]⟩⟩, hγ⟩

/-- The image of Γ_ns(p) in SL₂(F_p) ≃ the conic. -/
def rangeEquiv {ε : ZMod p} :
    (nsRed ε).range ≃ {x : ZMod p × ZMod p // x.1 ^ 2 - ε * x.2 ^ 2 = 1} where
  toFun y := ⟨((y.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0, (y.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0), by
    obtain ⟨h1, h2⟩ := mem_range_nsRed.1 y.2
    have hdet := y.1.2
    rw [det_fin_two, h1, h2] at hdet
    linear_combination hdet⟩
  invFun z := ⟨⟨!![z.1.1, ε * z.1.2; z.1.2, z.1.1], by rw [det_fin_two_of]; linear_combination z.2⟩,
    mem_range_nsRed.2 ⟨rfl, rfl⟩⟩
  left_inv y := by
    obtain ⟨h1, h2⟩ := mem_range_nsRed.1 y.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h2.symm
    · rfl
    · exact h1.symm
  right_inv z := rfl

theorem relIndex_Gamma_GammaNs (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    (CongruenceSubgroup.Gamma p).relIndex (GammaNs p ε) = p + 1 := by
  rw [Subgroup.relIndex, ← nsRed_ker, Subgroup.index_ker, Nat.card_congr rangeEquiv, card_conic hp2 hε]

end

theorem index_GammaNs' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    (GammaNs p ε).index = p * (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := Subgroup.relIndex_mul_index (Gamma_le_GammaNs ε)
  rw [relIndex_Gamma_GammaNs hp2 hε, index_Gamma_eq_card] at h
  have hSL := card_SL2_ZMod' p
  rw [hp.primeFactors, Finset.prod_singleton] at hSL
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq : ((p + 1 : ℕ) : ℚ) * ((GammaNs p ε).index : ℚ) = ((p + 1 : ℕ) : ℚ) * (p * (p - 1)) := by
    rw [← Nat.cast_mul, h, hSL]
    field_simp
    push_cast
    ring
  have hp1 : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hidx := mul_left_cancel₀ hp1 hq
  have h1 : 1 ≤ p := hp.one_lt.le
  have : (((p * (p - 1) : ℕ)) : ℚ) = p * (p - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
  exact_mod_cast hidx.trans this.symm

end

end NormalizerLean
