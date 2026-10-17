module

public import NormalizerDelta.GammaIso

@[expose] public section

/-!
# §K, easy part: Γ₀(N) and the w_Q normalize ±Γ₁(N); the case Q = 1; the exception N = 4

* ι_Q fixes ±1, so every w_Q normalizes Γ_{±1}(N) (`al_mem_normG_iff`).
* (ℤ/4)ˣ = {±1}, so ±Γ₁(4) = Γ₀(4), whose normalizer contains S₂ (h(4) = 2); S₂ is not an
  Atkin–Lehner element (its (0,0) entry would be √Q·x = 1, forcing Q = 1, and then y = 1/2).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem Gamma0R_le_normG_pmGamma1R' (N : ℕ) [NeZero N] : Gamma0R N ≤ NormG (pmGamma1R N) :=
  Gamma0R_le_normG_GammaDeltaR' N (pmOne N)

theorem isAtkinLehner_one_iff' (N : ℕ) (g : SL(2, ℝ)) : IsAtkinLehner N 1 g ↔ g ∈ Gamma0R N := by
  constructor
  · rintro ⟨x, y, z, w, hdet, hgm⟩
    refine mem_Gamma0R_of_entries x y (N * z) w ?_ (dvd_mul_right _ _)
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro hg
    obtain ⟨a, b, c, d, hdet, ⟨z, rfl⟩, hgm⟩ := exists_entries_of_mem_Gamma0R hg
    refine ⟨a, b, z, d, by push_cast; linear_combination hdet, ?_⟩
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp

theorem isIota_pm {N Q : ℕ} (hQ : Q ∣ N) {d : (ZMod N)ˣ} (hd : d = 1 ∨ d = -1) : IsIota N Q d d := by
  have hK : N / Q ∣ N := Nat.div_dvd_of_dvd hQ
  unfold IsIota
  rcases hd with rfl | rfl
  · simp [ZMod.cast_one hQ, ZMod.cast_one hK]
  · simp [ZMod.cast_neg hQ, ZMod.cast_one hQ]

theorem isAtkinLehner_mem_normG_pmGamma1R' {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : g ∈ NormG (pmGamma1R N) := by
  have hcop := coprime_of_isAtkinLehner hQ hg
  refine (al_mem_normG_iff hQ hcop hg (pmOne N)).2 (fun u => ⟨fun hu => ?_, ?_⟩)
  · exact ⟨u, hu, isIota_pm hQ (mem_pmOne.1 hu)⟩
  · rintro ⟨d, hd, hdu⟩
    rw [← isIota_unique hQ hcop (isIota_pm hQ (mem_pmOne.1 hd)) hdu]
    exact hd

/-! ### N = 4 -/

theorem pmOne_four : pmOne 4 = ⊤ :=
  eq_top_iff.2 fun u _ => mem_pmOne.2 (by
    have h : ∀ v : (ZMod 4)ˣ, v = 1 ∨ v = -1 := by decide
    exact h u)

theorem pmGamma1R_four' : pmGamma1R 4 = Gamma0R 4 := by
  unfold pmGamma1R GammaDeltaR
  rw [pmOne_four, GammaDelta_top']
  rfl

theorem factorization_four (p : ℕ) : (4 : ℕ).factorization p = if p = 2 then 2 else 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.prime_two.factorization_pow, Finsupp.single_apply]
  simp [eq_comm]

theorem hPart_four : hPart 4 = 2 := by
  unfold hPart; rw [factorization_four, factorization_four]; norm_num

theorem not_isAtkinLehner_S2 {Q : ℕ} : ¬ IsAtkinLehner 4 Q (S 2) := by
  rintro ⟨x, y, z, w, hdet, hgm⟩
  rw [coe_S] at hgm
  have h00 := congrFun (congrFun hgm 0) 0
  have h01 := congrFun (congrFun hgm 0) 1
  simp at h00 h01
  by_cases hQ0 : Q = 0
  · subst hQ0; simp at h00
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ0
  have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.2 hQr).ne'
  have hsq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQr.le
  -- (0,0): √Q x = 1, so Q x² = 1
  have h2 : Real.sqrt Q = Q * x := by
    have := congrArg (Real.sqrt Q * ·) h00
    simp only [mul_one] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have h1 : (Q : ℝ) * x ^ 2 = 1 := by
    have h4 : (Q : ℝ) = (Q * x) * (Q * x) := by rw [← h2, hsq]
    have h3 : (Q : ℝ) * 1 = Q * (Q * x ^ 2) := by
      rw [mul_one]; nth_rewrite 1 [h4]; ring
    exact (mul_left_cancel₀ hQr.ne' h3).symm
  have h1z : (Q : ℤ) * x ^ 2 = 1 := by exact_mod_cast h1
  have hQ1 : Q = 1 := by
    have := Int.eq_one_of_mul_eq_one_right (by positivity) h1z
    exact_mod_cast this
  subst hQ1
  have hy : (y : ℝ) = 2⁻¹ := by simpa using h01.symm
  have : (2 * y : ℤ) = 1 := by exact_mod_cast (show (2 : ℝ) * y = 1 by rw [hy]; norm_num)
  omega

theorem S2_mem_normG_pmGamma1R_four' :
    S 2 ∈ NormG (pmGamma1R 4) ∧ ∀ Q : ℕ, Q ∣ 4 → ¬ IsAtkinLehner 4 Q (S 2) := by
  refine ⟨?_, fun Q _ => not_isAtkinLehner_S2⟩
  rw [pmGamma1R_four']
  exact S_mem_normalizer' (by rw [hPart_four])

theorem card_BG_pmGamma1R_four' : Nat.card (BG (pmGamma1R 4)) = 6 := by
  rw [pmGamma1R_four']
  change Nat.card (B 4) = 6
  rw [card_B_explicit', factorization_four, factorization_four,
    show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  decide

end

end NormalizerLean
