import NormalizerDelta.CartanSplit

/-!
# §N: non-split Cartan curves of prime level

p is an odd prime and ε is not a square mod p.
* Norm-one elements: for s ≠ 0, a = (1 + εs²)/(1 − εs²), b = 2s/(1 − εs²) satisfy a² − εb² = 1, b ≠ 0
  (`exists_norm_one`); [[a, εb], [b, a]] (b ≠ 0) has no eigenvector in F_p² (`no_eigenvector`), so Γ_ns(p) and
  Γ_ns⁺(p) fix no line mod p and their normalizers lie in SL₂(ℤ).
* If σ t σ⁻¹ ≡ [[a', εb'], [b', a']] for t ≡ [[a, εb], [b, a]] (b ≠ 0), then a' = a (trace), b' = ±b (determinant),
  and comparing σ t = t' σ gives σ ≡ [[s, ±εv], [v, ±s]], i.e. σ ∈ Γ_ns⁺(p) (`mem_GammaNsPlus_of_conj`).
* For Γ_ns⁺(p) with p ≥ 5 take a ≠ 0: then σ t σ⁻¹ cannot be of the second kind (trace 0).
* The index: the image of Γ_ns(p) in SL₂(F_p) is in bijection with the conic a² − εc² = 1, which has p + 1 points
  (parametrization t ↦ ((1 + εt²)/(1 − εt²), 2t/(1 − εt²)) and the point (−1, 0)).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem not_isSquare_ne_zero {ε : ZMod p} (hε : ¬ IsSquare ε) : ε ≠ 0 := by
  rintro rfl; exact hε ⟨0, by simp⟩

theorem one_sub_ne_zero {ε : ZMod p} (hε : ¬ IsSquare ε) (s : ZMod p) : 1 - ε * s ^ 2 ≠ 0 := by
  intro h
  have hs : s ≠ 0 := by rintro rfl; simp at h
  apply hε
  refine ⟨s⁻¹, ?_⟩
  field_simp
  linear_combination -h

theorem exists_norm_one (hp : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) {s : ZMod p} (hs : s ≠ 0) :
    ((1 + ε * s ^ 2) / (1 - ε * s ^ 2)) ^ 2 - ε * (2 * s / (1 - ε * s ^ 2)) ^ 2 = 1 ∧
      2 * s / (1 - ε * s ^ 2) ≠ 0 := by
  have hD := one_sub_ne_zero hε s
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (by have := (Fact.out : p.Prime).two_le; omega)
  refine ⟨?_, div_ne_zero (mul_ne_zero h2 hs) hD⟩
  field_simp
  ring

theorem no_eigenvector {ε a b : ZMod p} (hε : ¬ IsSquare ε) (hb : b ≠ 0) {v : Fin 2 → ZMod p}
    (hv : v ≠ 0) (c : ZMod p) : a * v 0 + ε * b * v 1 ≠ c * v 0 ∨ b * v 0 + a * v 1 ≠ c * v 1 := by
  by_contra h
  push_neg at h
  obtain ⟨h0, h1⟩ := h
  by_cases hv1 : v 1 = 0
  · have : v 0 = 0 := by
      rw [hv1, mul_zero, add_zero, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hb
    exact hv (by ext i; fin_cases i <;> simp [this, hv1])
  · apply hε
    refine ⟨(c - a) / b, ?_⟩
    have e1 : b * v 0 = (c - a) * v 1 := by linear_combination h1
    have e2 : ε * b * v 1 = (c - a) * v 0 := by linear_combination h0
    have : ε * b ^ 2 * v 1 = (c - a) ^ 2 * v 1 := by
      linear_combination b * e2 + (c - a) * e1
    have := mul_right_cancel₀ hv1 this
    field_simp
    linear_combination this

/-! ### Γ_ns -/

theorem Gamma_le_GammaNs (ε : ZMod p) : CongruenceSubgroup.Gamma p ≤ GammaNs p ε := fun γ h => by
  obtain ⟨ha, hb, hc, hd⟩ := CongruenceSubgroup.Gamma_mem.1 h
  exact ⟨by rw [ha, hd], by rw [hb, hc, mul_zero]⟩

theorem GammaNs_le_GammaNsPlus (ε : ZMod p) : GammaNs p ε ≤ GammaNsPlus p ε := fun _ h => Or.inl h

/-- A lift to Γ_ns(p) of [[a, εb], [b, a]], a² − εb² = 1. -/
theorem exists_lift_ns {ε a b : ZMod p} (h : a ^ 2 - ε * b ^ 2 = 1) :
    ∃ t : SL(2, ℤ), ((t 0 0 : ℤ) : ZMod p) = a ∧ ((t 0 1 : ℤ) : ZMod p) = ε * b ∧
      ((t 1 0 : ℤ) : ZMod p) = b ∧ ((t 1 1 : ℤ) : ZMod p) = a := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let x : SL(2, ZMod p) := ⟨!![a, ε * b; b, a], by rw [det_fin_two_of]; linear_combination h⟩
  obtain ⟨t, ht⟩ := redSL_surjective p x
  have hent : ∀ i j, ((t i j : ℤ) : ZMod p) = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := by
    intro i j; rw [← ht]; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  exact ⟨t, by rw [hent]; simp [x], by rw [hent]; simp [x], by rw [hent]; simp [x], by rw [hent]; simp [x]⟩

/-- The normalizer computation: if t ≡ [[a, εb], [b, a]] (b ≠ 0, a² − εb² = 1) and σ t σ⁻¹ ≡ [[a', εb'], [b', a']],
then σ ∈ Γ_ns⁺(p). -/
theorem mem_GammaNsPlus_of_conj (hp : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) {σ t : SL(2, ℤ)}
    {a b : ZMod p} (hb : b ≠ 0) (hab : a ^ 2 - ε * b ^ 2 = 1)
    (t00 : ((t 0 0 : ℤ) : ZMod p) = a) (t01 : ((t 0 1 : ℤ) : ZMod p) = ε * b)
    (t10 : ((t 1 0 : ℤ) : ZMod p) = b) (t11 : ((t 1 1 : ℤ) : ZMod p) = a)
    (h1 : (((σ * t * σ⁻¹) 1 1 : ℤ) : ZMod p) = (((σ * t * σ⁻¹) 0 0 : ℤ) : ZMod p))
    (h2 : (((σ * t * σ⁻¹) 0 1 : ℤ) : ZMod p) = ε * (((σ * t * σ⁻¹) 1 0 : ℤ) : ZMod p)) :
    σ ∈ GammaNsPlus p ε := by
  have h2' : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (by have := (Fact.out : p.Prime).two_le; omega)
  have hε0 := not_isSquare_ne_zero hε
  set t' := σ * t * σ⁻¹ with ht'
  have htσ : t' * σ = σ * t := by rw [ht']; group
  -- trace and determinant
  have htr := congrArg (fun z : ℤ => (z : ZMod p)) (conj_trace σ t)
  simp only [Int.cast_add, t00, t11] at htr
  rw [← ht'] at htr
  have hα : ((t' 0 0 : ℤ) : ZMod p) = a := by
    rw [h1] at htr
    apply mul_left_cancel₀ h2'
    linear_combination htr
  have hdt := det_mod (N := p) t'
  rw [h1, h2, hα] at hdt
  have hβ : ((t' 1 0 : ℤ) : ZMod p) = b ∨ ((t' 1 0 : ℤ) : ZMod p) = -b := by
    have : (((t' 1 0 : ℤ) : ZMod p) - b) * (((t' 1 0 : ℤ) : ZMod p) + b) = 0 := by
      apply mul_left_cancel₀ hε0
      linear_combination -hdt + hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  -- σ t = t' σ, entries (0, 0) and (1, 0)
  have E : ∀ i j, (((t' * σ) i j : ℤ) : ZMod p) = (((σ * t) i j : ℤ) : ZMod p) := by
    intro i j; rw [htσ]
  have E00 := E 0 0
  have E10 := E 1 0
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
    Int.cast_mul, t00, t10, h1, h2, hα] at E00 E10
  rcases hβ with hβ | hβ
  · left
    rw [hβ] at E00 E10
    constructor
    · apply mul_right_cancel₀ hb
      linear_combination -E10
    · apply mul_right_cancel₀ hb
      linear_combination -E00
  · right
    rw [hβ] at E00 E10
    constructor
    · apply mul_right_cancel₀ hb
      linear_combination -E10
    · apply mul_right_cancel₀ hb
      linear_combination -E00

/-- The residue types multiply: type s times type s' is type s s' (s, s' = ±1). -/
theorem type_mul {ε A B C D A' B' C' D' s s' : ZMod p} (hs : s * s = 1)
    (hD : D = s * A) (hB : B = s * (ε * C)) (hD' : D' = s' * A') (hB' : B' = s' * (ε * C')) :
    C * B' + D * D' = s * s' * (A * A' + B * C') ∧
      A * B' + B * D' = s * s' * (ε * (C * A' + D * C')) := by
  subst hD hB hD' hB'
  constructor
  · linear_combination (-(s' * ε * C * C')) * hs
  · linear_combination (-(s' * ε * A * C')) * hs

theorem not_both_types (hp : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) (γ : SL(2, ℤ))
    (h1 : ((γ 1 1 : ℤ) : ZMod p) = (γ 0 0 : ℤ) ∧ ((γ 0 1 : ℤ) : ZMod p) = ε * (γ 1 0 : ℤ))
    (h2 : ((γ 1 1 : ℤ) : ZMod p) = -((γ 0 0 : ℤ) : ZMod p) ∧
      ((γ 0 1 : ℤ) : ZMod p) = -(ε * ((γ 1 0 : ℤ) : ZMod p))) : False := by
  have h2' : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (by have := (Fact.out : p.Prime).two_le; omega)
  have hε0 := not_isSquare_ne_zero hε
  have ha : ((γ 0 0 : ℤ) : ZMod p) = 0 := by
    have : (2 : ZMod p) * ((γ 0 0 : ℤ) : ZMod p) = 0 := by linear_combination h2.1 - h1.1
    exact (mul_eq_zero.1 this).resolve_left h2'
  have hc : ((γ 1 0 : ℤ) : ZMod p) = 0 := by
    have : (2 * ε) * ((γ 1 0 : ℤ) : ZMod p) = 0 := by linear_combination h2.2 - h1.2
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2' hε0)
  have hdet := det_mod (N := p) γ
  rw [h1.1, h1.2, ha, hc] at hdet
  simp at hdet

theorem hirr_ns (hp : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) {H : Subgroup SL(2, ℤ)}
    (hH : GammaNs p ε ≤ H) : ∀ q : ℕ, q.Prime → q ∣ p → ∀ v : Fin 2 → ZMod q, v ≠ 0 →
      ∃ γ ∈ H, ∀ c : ZMod q, (redSL q γ : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v ≠ c • v := by
  intro q hq hqp v hv
  obtain rfl := ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hqp).symm
  obtain ⟨hab, hb⟩ := exists_norm_one hp hε (one_ne_zero (α := ZMod p))
  obtain ⟨t, t00, t01, t10, t11⟩ := exists_lift_ns hab
  refine ⟨t, hH ⟨by rw [t11, t00], by rw [t01, t10]⟩, fun c hc => ?_⟩
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, redSL_apply, t00, t01, t10, t11,
    Pi.smul_apply, smul_eq_mul] at c0 c1
  rcases no_eigenvector (a := (1 + ε * 1 ^ 2) / (1 - ε * 1 ^ 2)) hε hb hv c with h | h
  · exact h (by linear_combination c0)
  · exact h (by linear_combination c1)

theorem GammaNsPlus_le_normG_GammaNs (ε : ZMod p) :
    toR (GammaNsPlus p ε) ≤ NormG (toR (GammaNs p ε)) := by
  apply toR_le_normG
  intro g hg γ hγ
  obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply g
  obtain ⟨hγd, hγb⟩ := hγ
  show (((g * γ * g⁻¹) 1 1 : ℤ) : ZMod p) = (((g * γ * g⁻¹) 0 0 : ℤ) : ZMod p) ∧
    (((g * γ * g⁻¹) 0 1 : ℤ) : ZMod p) = ε * (((g * γ * g⁻¹) 1 0 : ℤ) : ZMod p)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]
  push_cast
  rw [hγd, hγb]
  rcases hg with ⟨hd, hb⟩ | ⟨hd, hb⟩
  · rw [hd, hb]; constructor <;> ring
  · rw [hd, hb]; constructor <;> ring

end

theorem normG_GammaNs' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    NormG (toR (GammaNs p ε)) = toR (GammaNsPlus p ε) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine le_antisymm (fun g hg => ?_) (GammaNsPlus_le_normG_GammaNs ε)
  obtain ⟨hab, hb⟩ := exists_norm_one hp2 hε (one_ne_zero (α := ZMod p))
  obtain ⟨t, t00, t01, t10, t11⟩ := exists_lift_ns hab
  have ht : t ∈ GammaNs p ε := ⟨by rw [t11, t00], by rw [t01, t10]⟩
  obtain ⟨σ, -, rfl⟩ := normG_level_le_SL2ZR' (N := p) inferInstance (Gamma_le_GammaNs ε) (hirr_ns hp2 hε le_rfl) hg
  have h := conj_mem_of_normG hg ht
  exact ofZ_mem_toR (mem_GammaNsPlus_of_conj hp2 hε hb hab t00 t01 t10 t11 h.1 h.2)

theorem exists_type_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    ∃ w : SL(2, ℤ), w ∈ GammaNsPlus p ε ∧ w ∉ GammaNs p ε := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hε0 := not_isSquare_ne_zero hε
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
    (g := Polynomial.C (-ε) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C 1)
    (Polynomial.degree_quadratic one_ne_zero) (Polynomial.degree_quadratic (neg_ne_zero.2 hε0)) hcard
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at hxy
  let u : SL(2, ZMod p) := ⟨!![x, -(ε * y); y, -x], by rw [det_fin_two_of]; linear_combination -hxy⟩
  obtain ⟨w, hw⟩ := redSL_surjective p u
  have hent : ∀ i j, ((w i j : ℤ) : ZMod p) = (u : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := by
    intro i j; rw [← hw]; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have h2 : ((w 1 1 : ℤ) : ZMod p) = -((w 0 0 : ℤ) : ZMod p) ∧
      ((w 0 1 : ℤ) : ZMod p) = -(ε * ((w 1 0 : ℤ) : ZMod p)) := by
    rw [hent, hent, hent, hent]; simp [u]
  exact ⟨w, Or.inr h2, fun h1 => not_both_types hp2 hε w h1 h2⟩

theorem relIndex_GammaNs_GammaNsPlus {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ε : ZMod p}
    (hε : ¬ IsSquare ε) : (GammaNs p ε).relIndex (GammaNsPlus p ε) = 2 := by
  obtain ⟨w, hw, hw'⟩ := exists_type_two hp2 hε
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨w, hw⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hmul : ∀ x y : SL(2, ℤ), ∀ i j, (((x * y) i j : ℤ) : ZMod p) =
      ((x i 0 : ℤ) : ZMod p) * (y 0 j : ℤ) + (x i 1 : ℤ) * (y 1 j : ℤ) := by
    intro x y i j
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hw2 := hw.resolve_left hw'
  have hmem : ∀ x : SL(2, ℤ), x ∈ GammaNs p ε ↔ (((x 1 1 : ℤ) : ZMod p) = (x 0 0 : ℤ) ∧
      ((x 0 1 : ℤ) : ZMod p) = ε * (x 1 0 : ℤ)) := fun x => Iff.rfl
  rcases b.2 with hb | hb
  · -- b of type 1: b w of type 2
    have hbw := type_mul (A := ((b : SL(2, ℤ)) 0 0 : ZMod p)) (B := ((b : SL(2, ℤ)) 0 1 : ZMod p))
      (C := ((b : SL(2, ℤ)) 1 0 : ZMod p)) (D := ((b : SL(2, ℤ)) 1 1 : ZMod p))
      (A' := ((w 0 0 : ℤ) : ZMod p)) (B' := ((w 0 1 : ℤ) : ZMod p)) (C' := ((w 1 0 : ℤ) : ZMod p))
      (D' := ((w 1 1 : ℤ) : ZMod p)) (s := 1) (s' := -1) (by ring) (by rw [hb.1, one_mul])
      (by rw [hb.2, one_mul]) (by rw [hw2.1]; ring) (by rw [hw2.2]; ring)
    right
    refine ⟨hb, fun h => not_both_types hp2 hε _ h ⟨?_, ?_⟩⟩
    · rw [hmul, hmul, hbw.1]; ring
    · rw [hmul, hmul, hbw.2]; ring
  · -- b of type 2: b w of type 1
    have hbw := type_mul (A := ((b : SL(2, ℤ)) 0 0 : ZMod p)) (B := ((b : SL(2, ℤ)) 0 1 : ZMod p))
      (C := ((b : SL(2, ℤ)) 1 0 : ZMod p)) (D := ((b : SL(2, ℤ)) 1 1 : ZMod p))
      (A' := ((w 0 0 : ℤ) : ZMod p)) (B' := ((w 0 1 : ℤ) : ZMod p)) (C' := ((w 1 0 : ℤ) : ZMod p))
      (D' := ((w 1 1 : ℤ) : ZMod p)) (s := -1) (s' := -1) (by ring) (by rw [hb.1]; ring)
      (by rw [hb.2]; ring) (by rw [hw2.1]; ring) (by rw [hw2.2]; ring)
    left
    refine ⟨⟨?_, ?_⟩, fun h => not_both_types hp2 hε _ h hb⟩
    · rw [hmul, hmul, hbw.1]; ring
    · rw [hmul, hmul, hbw.2]; ring

theorem card_BG_GammaNs' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Nat.card (BG (toR (GammaNs p ε))) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  show (toR (GammaNs p ε)).relIndex (NormG (toR (GammaNs p ε))) = 2
  rw [normG_GammaNs' hp hp2 hε, relIndex_toR, relIndex_GammaNs_GammaNsPlus hp2 hε]

theorem normG_GammaNsPlus' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    NormG (toR (GammaNsPlus p ε)) = toR (GammaNsPlus p ε) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast zmod_ne_zero_of_lt (n := 3) (by norm_num) (by omega)
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  -- a norm-one element with a ≠ 0, b ≠ 0
  obtain ⟨s, hs, hs'⟩ : ∃ s : ZMod p, s ≠ 0 ∧ 1 + ε * s ^ 2 ≠ 0 := by
    by_cases h : 1 + ε * 1 ^ 2 = 0
    · refine ⟨2, h2, fun h' => h3 ?_⟩
      linear_combination 4 * h - h'
    · exact ⟨1, one_ne_zero, h⟩
  obtain ⟨hab, hb⟩ := exists_norm_one hp2 hε hs
  have ha : (1 + ε * s ^ 2) / (1 - ε * s ^ 2) ≠ 0 := div_ne_zero hs' (one_sub_ne_zero hε s)
  obtain ⟨t, t00, t01, t10, t11⟩ := exists_lift_ns hab
  have ht : t ∈ GammaNsPlus p ε := Or.inl ⟨by rw [t11, t00], by rw [t01, t10]⟩
  obtain ⟨σ, -, rfl⟩ := normG_level_le_SL2ZR' (N := p) inferInstance
    ((Gamma_le_GammaNs ε).trans (GammaNs_le_GammaNsPlus ε))
    (hirr_ns hp2 hε (GammaNs_le_GammaNsPlus ε)) hg
  refine ofZ_mem_toR ?_
  rcases conj_mem_of_normG hg ht with h | h
  · exact mem_GammaNsPlus_of_conj hp2 hε hb hab t00 t01 t10 t11 h.1 h.2
  · exfalso
    have htr := congrArg (fun z : ℤ => (z : ZMod p)) (conj_trace σ t)
    simp only [Int.cast_add, t00, t11] at htr
    rw [h.1] at htr
    apply ha
    have : (2 : ZMod p) * ((1 + ε * s ^ 2) / (1 - ε * s ^ 2)) = 0 := by linear_combination -htr
    exact (mul_eq_zero.1 this).resolve_left h2

theorem card_BG_GammaNsPlus' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Nat.card (BG (toR (GammaNsPlus p ε))) = 1 :=
  card_BG_eq_one_of (normG_GammaNsPlus' hp hp5 hε)

/-! ### p = 3 -/

/-- [[0, 1], [−1, 1]]. -/
def sigma3 : SL(2, ℤ) := mkSL 0 1 (-1) 1 (by ring)

theorem ns3_aux : ∀ a b c d : ZMod 3, ((d = a ∧ b = 2 * c) ∨ (d = -a ∧ b = -(2 * c))) →
    a * d - b * c = 1 →
    ((a - c = c + d ∧ -c = 2 * (c - a + d - b)) ∨ (a - c = -(c + d) ∧ -c = -(2 * (c - a + d - b)))) := by
  decide

theorem ns3_aux' : ∀ a b c d : ZMod 3, ((d = a ∧ b = 2 * c) ∨ (d = -a ∧ b = -(2 * c))) →
    a * d - b * c = 1 →
    ((a + b = d - b ∧ a - c + b - d = 2 * -b) ∨ (a + b = -(d - b) ∧ a - c + b - d = -(2 * -b))) := by
  decide

theorem zmod3_nonsq {ε : ZMod 3} (hε : ¬ IsSquare ε) : ε = 2 := by
  fin_cases ε
  · exact absurd ⟨0, rfl⟩ hε
  · exact absurd ⟨1, rfl⟩ hε
  · rfl

theorem GammaNsPlus_three_lt' {ε : ZMod 3} (hε : ¬ IsSquare ε) :
    toR (GammaNsPlus 3 ε) < NormG (toR (GammaNsPlus 3 ε)) := by
  obtain rfl := zmod3_nonsq hε
  refine lt_of_le_of_ne Subgroup.le_normalizer (fun h => ?_)
  obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply sigma3
  have hmem : ofZ sigma3 ∈ NormG (toR (GammaNsPlus 3 2)) := by
    apply mem_normG_of_SL
    · intro γ hγ
      have key := ns3_aux _ _ _ _ hγ (det_mod (N := 3) γ)
      show ((((sigma3 * γ * sigma3⁻¹) 1 1 : ℤ) : ZMod 3) = _ ∧ _) ∨ _
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10,
        e11]
      simp only [sigma3, mkSL, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, head_cons]
      push_cast
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left; exact ⟨by linear_combination k1, by linear_combination k2⟩
      · right; exact ⟨by linear_combination k1, by linear_combination k2⟩
    · intro γ hγ
      have key := ns3_aux' _ _ _ _ hγ (det_mod (N := 3) γ)
      show ((((sigma3⁻¹ * γ * sigma3) 1 1 : ℤ) : ZMod 3) = _ ∧ _) ∨ _
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10,
        e11]
      simp only [sigma3, mkSL, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, head_cons]
      push_cast
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left; exact ⟨by linear_combination k1, by linear_combination k2⟩
      · right; exact ⟨by linear_combination k1, by linear_combination k2⟩
  have hnot : ofZ sigma3 ∉ toR (GammaNsPlus 3 2) := by
    rw [ofZ_mem_toR_iff]
    rintro (⟨hd, -⟩ | ⟨hd, -⟩)
    · exact absurd hd (by simp [sigma3, mkSL])
    · exact absurd hd (by simp [sigma3, mkSL])
  exact hnot (h ▸ hmem)

end NormalizerLean
