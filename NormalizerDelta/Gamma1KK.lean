module

public import NormalizerDelta.Gamma1Basic

@[expose] public section

/-!
# §K: Kim–Koo / Lang: for N ≠ 4, Nor(±Γ₁(N)) is the union of the Atkin–Lehner cosets

Let g ∈ Nor(±Γ₁(N)).  By `newman_delta'` with Δ = {±1} (ε_Δ = N), g = ±(1/√e)[[ae, b/h], [Nc/h, de]] with
h = h_Δ (h² ∣ N), n = N/h², e ∣ n, ade² − bcn = e, i.e. ade − (n/e)bc = 1.
* **Step A.** The lower right entries of gTg⁻¹ and gUg⁻¹ are 1 + acN/h and 1 − bdN/h, and must be
  ≡ ±1 (mod N).  The sign −1 forces (N/h) ∣ 2 and h ∣ N/h, i.e. N ∈ {1, 2, 4}; so for N ≠ 4,
  h ∣ ac and h ∣ bd (`dvd_of_conj_entry`).
* **Step B.** ade − (n/e)bc = 1 makes a coprime to b and c, and d coprime to b and c.  With
  h_F = gcd(h, a), h_G = gcd(h, c): h = h_F h_G (h ∣ ac), h_F ∣ d, h_G ∣ b (h ∣ bd), and
  g = (1/√Q)[[Qx, y], [Nz, Qw]] with Q = e h_F², x = ±a/h_F, y = ±b/h_G, z = ±c/h_G, w = ±d/h_F
  (`isAtkinLehner_of_newmanForm`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### The lower right entries of g T g⁻¹ and g U g⁻¹ -/

theorem conj_matT_11 (g : SL(2, ℝ)) :
    ((g * matT * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
  have hdet := g.2
  rw [det_fin_two] at hdet
  rw [coe_conj, adjugate_fin_two]
  simp [matT, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination hdet

theorem conj_matU_11 (N : ℕ) (g : SL(2, ℝ)) :
    ((g * matU N * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      1 - N * ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
  have hdet := g.2
  rw [det_fin_two] at hdet
  rw [coe_conj, adjugate_fin_two]
  simp [matU, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination hdet

/-- If g normalizes ±Γ₁(N) and Y ∈ ±Γ₁(N), the lower right entry of g Y g⁻¹ is an integer ≡ ±1. -/
theorem conj_entry_pm {N : ℕ} {g Y : SL(2, ℝ)} (hg : g ∈ NormG (pmGamma1R N)) (hY : Y ∈ pmGamma1R N) :
    ∃ t : ℤ, ((g * Y * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = t ∧
      ((N : ℤ) ∣ t - 1 ∨ (N : ℤ) ∣ t + 1) := by
  have := (Subgroup.mem_normalizer_iff.1 hg Y).1 hY
  obtain ⟨γ, ⟨-, u, hu, hud⟩, hγ⟩ := mem_toR.1 this
  refine ⟨γ 1 1, by rw [← hγ, coe_ofZ]; simp, ?_⟩
  rcases mem_pmOne.1 hu with rfl | rfl
  · left; exact dvd_of_zmod_eq_one (by rw [← hud]; simp)
  · right; exact dvd_of_zmod_eq_neg_one (by rw [← hud]; simp)

/-- Step A: h t = h + X N with t ≡ ±1 (mod N), h² ∣ N, N ≠ 4 give h ∣ X. -/
theorem dvd_of_conj_entry {N h : ℕ} (hN0 : N ≠ 0) (hN4 : N ≠ 4) (hh : 0 < h) (hhN : h ^ 2 ∣ N) {t X : ℤ}
    (ht : (h : ℤ) * t = h + X * N) (hpm : (N : ℤ) ∣ t - 1 ∨ (N : ℤ) ∣ t + 1) : (h : ℤ) ∣ X := by
  obtain ⟨K, hK⟩ : h ∣ N := (dvd_pow_self h two_ne_zero).trans hhN
  have hhK : h ∣ K := by
    rw [hK, pow_two] at hhN; exact Nat.dvd_of_mul_dvd_mul_left hh hhN
  have hhz : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
  rcases hpm with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨m, ?_⟩
    have : (N : ℤ) * ((h : ℤ) * m - X) = 0 := by linear_combination ht - (h : ℤ) * hm
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (by exact_mod_cast h0) hN0
    · linarith
  · -- K (h m − X) = 2, so K ∣ 2, and h ∣ K forces h = 1
    have hK2 : (K : ℤ) * ((h : ℤ) * m - X) = 2 := by
      apply mul_left_cancel₀ hhz
      have hN : (N : ℤ) = h * K := by exact_mod_cast hK
      rw [hN] at ht hm
      linear_combination ht - (h : ℤ) * hm
    have hKpos : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · subst h0; simp at hK2
      · exact h0
    have hKle : K ≤ 2 := by
      have : (K : ℤ) ∣ 2 := ⟨_, hK2.symm⟩
      have := Int.le_of_dvd (by norm_num) this
      omega
    have hhle : h ≤ K := Nat.le_of_dvd hKpos hhK
    have h1 : h = 1 := by
      by_contra h1
      have : h = 2 := by omega
      have : K = 2 := by omega
      subst_vars
      exact hN4 (by omega)
    rw [h1]; exact one_dvd _

/-! ### Step B -/

theorem isAtkinLehner_of_newmanForm {N h : ℕ} [NeZero N] (hh : 0 < h) (hhN : h ^ 2 ∣ N)
    {g : SL(2, ℝ)} (hg : IsNewmanFormH N h g) {a b c d : ℤ} {e : ℕ} {ε : ℝ}
    (he0 : 0 < e) (hen : e ∣ N / h ^ 2) (hdet : a * d * (e : ℤ) ^ 2 - b * c * ((N / h ^ 2 : ℕ) : ℤ) = e)
    (hε : ε = 1 ∨ ε = -1)
    (hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (ε / Real.sqrt e) • !![(a : ℝ) * e, (b : ℝ) / h; (N : ℝ) * c / h, (d : ℝ) * e])
    (hac : (h : ℤ) ∣ a * c) (hbd : (h : ℤ) ∣ b * d) :
    ∃ Q : ℕ, Q ∣ N ∧ IsAtkinLehner N Q g := by
  clear hg
  set n := N / h ^ 2 with hndef
  have hN : N = h ^ 2 * n := (Nat.mul_div_cancel' hhN).symm
  obtain ⟨m, hm⟩ := hen
  have hred : a * d * e - b * c * m = 1 := by
    apply mul_left_cancel₀ (show (e : ℤ) ≠ 0 by exact_mod_cast he0.ne')
    rw [hm] at hdet; push_cast at hdet; linear_combination hdet
  have cab : IsCoprime a b := ⟨d * e, -(c * m), by linear_combination hred⟩
  have cac : IsCoprime a c := ⟨d * e, -(b * m), by linear_combination hred⟩
  have cdb : IsCoprime d b := ⟨a * e, -(c * m), by linear_combination hred⟩
  have ccd : IsCoprime c d := ⟨-(b * m), a * e, by linear_combination hred⟩
  set hF := Int.gcd h a
  set hG := Int.gcd h c
  have hFa : (hF : ℤ) ∣ a := Int.gcd_dvd_right _ _
  have hFh : (hF : ℤ) ∣ h := Int.gcd_dvd_left _ _
  have hGc : (hG : ℤ) ∣ c := Int.gcd_dvd_right _ _
  have hGh : (hG : ℤ) ∣ h := Int.gcd_dvd_left _ _
  have hFd : (hF : ℤ) ∣ d :=
    (IsCoprime.of_isCoprime_of_dvd_left cab hFa).dvd_of_dvd_mul_left (hFh.trans hbd)
  have hGb : (hG : ℤ) ∣ b := by
    have h1 : IsCoprime (hG : ℤ) d := IsCoprime.of_isCoprime_of_dvd_left ccd hGc
    exact h1.dvd_of_dvd_mul_right (hGh.trans hbd)
  have hFG : hF * hG = h := by
    have hcop : Nat.Coprime a.natAbs c.natAbs := Int.isCoprime_iff_gcd_eq_one.1 cac
    have h1 := Nat.Coprime.gcd_mul h hcop
    have h2 : h ∣ a.natAbs * c.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hac
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
    rw [Nat.gcd_eq_left h2] at h1
    exact h1.symm
  obtain ⟨a₁, ha₁⟩ := hFa
  obtain ⟨d₁, hd₁⟩ := hFd
  obtain ⟨b₁, hb₁⟩ := hGb
  obtain ⟨c₁, hc₁⟩ := hGc
  have hF0 : 0 < hF := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hFG; omega)
  have hG0 : 0 < hG := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hFG; omega)
  refine ⟨e * hF ^ 2, ⟨hG ^ 2 * m, by rw [hN, hm, ← hFG]; ring⟩, ?_⟩
  -- real-number bookkeeping
  have hs0 : 0 < Real.sqrt e := Real.sqrt_pos.2 (by exact_mod_cast he0)
  set s := Real.sqrt (e : ℝ) with hsdef
  have hse : (e : ℝ) = s ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
  have hsQ : Real.sqrt ((e * hF ^ 2 : ℕ) : ℝ) = s * hF := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  have hNr : (N : ℝ) = (hF : ℝ) ^ 2 * hG ^ 2 * e * m := by
    have : (N : ℤ) = (hF : ℤ) ^ 2 * hG ^ 2 * e * m := by rw [hN, hm, ← hFG]; push_cast; ring
    exact_mod_cast this
  have hhr : (h : ℝ) = hF * hG := by exact_mod_cast hFG.symm
  have hFr : (hF : ℝ) ≠ 0 := by exact_mod_cast hF0.ne'
  have hGr : (hG : ℝ) ≠ 0 := by exact_mod_cast hG0.ne'
  have hred' : a₁ * d₁ * e * hF ^ 2 - b₁ * c₁ * m * hG ^ 2 = 1 := by
    rw [ha₁, hd₁, hb₁, hc₁] at hred; linear_combination hred
  rcases hε with rfl | rfl
  · refine ⟨a₁, b₁, c₁, d₁, ?_, ?_⟩
    · push_cast
      have : (N : ℤ) = (hF : ℤ) ^ 2 * hG ^ 2 * e * m := by rw [hN, hm, ← hFG]; push_cast; ring
      rw [this]
      linear_combination ((e : ℤ) * hF ^ 2) * hred'
    · rw [hgm, hsQ, ha₁, hd₁, hb₁, hc₁, hhr, hNr]
      push_cast
      rw [hse]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · refine ⟨-a₁, -b₁, -c₁, -d₁, ?_, ?_⟩
    · push_cast
      have : (N : ℤ) = (hF : ℤ) ^ 2 * hG ^ 2 * e * m := by rw [hN, hm, ← hFG]; push_cast; ring
      rw [this]
      linear_combination ((e : ℤ) * hF ^ 2) * hred'
    · rw [hgm, hsQ, ha₁, hd₁, hb₁, hc₁, hhr, hNr]
      push_cast
      rw [hse]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **Kim–Koo, Lang.** -/
theorem normG_pmGamma1R' {N : ℕ} [NeZero N] (hN : N ≠ 4) (g : SL(2, ℝ)) :
    g ∈ NormG (pmGamma1R N) ↔
      ∃ Q : ℕ, Q ∣ N ∧ Nat.Coprime Q (N / Q) ∧ IsAtkinLehner N Q g := by
  constructor
  · intro hg
    have hN0 := NeZero.ne N
    have hh : 0 < hDelta N (pmOne N) := (newmanData_delta N (pmOne N)).h_pos
    have hhN := hDelta_sq_dvd' N (pmOne N)
    have hNF := newman_delta' (pmOne N) hg
    obtain ⟨a, b, c, d, e, he0, hen, hdet, ε, hε, hgm⟩ := hNF
    set h := hDelta N (pmOne N)
    have her : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have hk : (ε / Real.sqrt e) ^ 2 = 1 / e := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      rcases hε with rfl | rfl <;> norm_num
    have g00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = ε / Real.sqrt e * (a * e) := by rw [hgm]; simp
    have g01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = ε / Real.sqrt e * (b / h) := by rw [hgm]; simp
    have g10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = ε / Real.sqrt e * (N * c / h) := by rw [hgm]; simp
    have g11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = ε / Real.sqrt e * (d * e) := by rw [hgm]; simp
    -- Step A with T
    obtain ⟨t, ht, htpm⟩ := conj_entry_pm hg (matT_mem_GammaDeltaR (Δ := pmOne N))
    rw [conj_matT_11, g00, g10] at ht
    have ht' : (h : ℤ) * t = h + (a * c) * N := by
      have : (h : ℝ) * t = h + (a * c) * N := by
        rw [← ht]
        have e1 : ε / Real.sqrt e * (a * e) * (ε / Real.sqrt e * (N * c / h)) =
            (ε / Real.sqrt e) ^ 2 * (a * e * (N * c / h)) := by ring
        rw [e1, hk]; field_simp
      exact_mod_cast this
    have hac := dvd_of_conj_entry hN0 hN hh hhN ht' htpm
    -- Step A with U
    obtain ⟨t', ht2, htpm'⟩ := conj_entry_pm hg (matU_mem_GammaDeltaR (Δ := pmOne N))
    rw [conj_matU_11, g01, g11] at ht2
    have ht2' : (h : ℤ) * t' = h + (-(b * d)) * N := by
      have : (h : ℝ) * t' = h + (-(b * d)) * N := by
        rw [← ht2]
        have e1 : ε / Real.sqrt e * (b / h) * (ε / Real.sqrt e * (d * e)) =
            (ε / Real.sqrt e) ^ 2 * (b / h * (d * e)) := by ring
        rw [e1, hk]; field_simp; ring
      exact_mod_cast this
    have hbd := (dvd_neg).1 (dvd_of_conj_entry hN0 hN hh hhN ht2' htpm')
    -- Step B
    obtain ⟨Q, hQ, hAL⟩ := isAtkinLehner_of_newmanForm hh hhN
      ⟨a, b, c, d, e, he0, hen, hdet, ε, hε, hgm⟩ he0 hen hdet hε hgm hac hbd
    exact ⟨Q, hQ, coprime_of_isAtkinLehner hQ hAL, hAL⟩
  · rintro ⟨Q, hQ, -, hg⟩
    exact isAtkinLehner_mem_normG_pmGamma1R' hQ hg

end

end NormalizerLean
