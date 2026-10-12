import NormalizerDelta.GammaConj

/-!
# §G: Nor(±Γ(N)) = Nor(Γ(N)) = SL₂(ℤ); the S₇ example at level 49

* For Δ = {d ≡ ±1 mod M} at level M², M ∣ ε_Δ, so h_Δ = M and n_Δ = 1 (`hDelta_deltaPm_sq`).
* Nor(±Γ(M)) = D Nor(Γ_Δ(M²)) D⁻¹ (`conj_GammaDelta_sq'`, `Subgroup.map_equiv_normalizer_eq`), and by
  `newman_delta'` every element of Nor(Γ_Δ(M²)) is ±[[a, b/M], [Mc, d]] (e ∣ n_Δ = 1), whose D-conjugate
  ±[[a, b], [c, d]] is integral.
* Nor(Γ(N)) ≤ Nor(±Γ(N)) since −1 is central; SL₂(ℤ) normalizes both since Γ(N) is normal.
* S₇ = D⁻¹ T D normalizes Γ_Δ(49) because T normalizes ±Γ(7); S₇ ∉ Nor(Γ₀(49)) by the frozen T2
  (h(49) = 1 would force 7 b = ±1).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem ofZ_neg (γ : SL(2, ℤ)) : ofZ (-γ) = -ofZ γ := by
  ext i j; simp [SpecialLinearGroup.coe_neg]

theorem pmGammaR_eq (N : ℕ) : pmGammaR N = toR (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1)) := by
  rw [toR_sup_zpowers]; rfl

theorem mem_pmGammaR {N : ℕ} {Y : SL(2, ℝ)} : Y ∈ pmGammaR N ↔ Y ∈ GammaR N ∨ -Y ∈ GammaR N := by
  rw [pmGammaR_eq]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rcases mem_sup_pm_iff.1 hγ with h | h
    · exact Or.inl (ofZ_mem_toR h)
    · right; rw [← ofZ_neg]; exact ofZ_mem_toR h
  · rintro (⟨γ, hγ, rfl⟩ | ⟨γ, hγ, hγY⟩)
    · exact ofZ_mem_toR (mem_sup_pm_iff.2 (Or.inl hγ))
    · refine ⟨-γ, mem_sup_pm_iff.2 (Or.inr (by rwa [neg_neg])), ?_⟩
      show ofZ (-γ) = Y
      rw [ofZ_neg]
      change -ofZ γ = Y
      rw [show ofZ γ = -Y from hγY, neg_neg]

theorem SL2ZR_le_normG_GammaR (N : ℕ) : SL2ZR ≤ NormG (GammaR N) :=
  toR_le_normG (fun g _ γ hγ => (CongruenceSubgroup.Gamma_normal N).conj_mem γ hγ g)

theorem SL2ZR_le_normG_pmGammaR (N : ℕ) : SL2ZR ≤ NormG (pmGammaR N) := by
  rw [pmGammaR_eq]
  refine toR_le_normG (fun g _ γ hγ => ?_)
  rcases mem_sup_pm_iff.1 hγ with h | h
  · exact mem_sup_pm_iff.2 (Or.inl ((CongruenceSubgroup.Gamma_normal N).conj_mem γ h g))
  · refine mem_sup_pm_iff.2 (Or.inr ?_)
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h g
    rwa [mul_neg, neg_mul] at this

theorem normG_GammaR_le_normG_pmGammaR (N : ℕ) : NormG (GammaR N) ≤ NormG (pmGammaR N) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro Y
  rw [mem_pmGammaR, mem_pmGammaR, hg Y, hg (-Y), mul_neg, neg_mul]

/-! ### h_Δ for Δ = ±1 mod M at level M² -/

theorem hDelta_deltaPm_sq (M : ℕ) (hM : 0 < M) [NeZero (M ^ 2)] :
    hDelta (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)) = M := by
  have hMε : M ∣ epsDelta (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)) := by
    refine dvd_epsDelta_iff.2 ⟨dvd_pow_self M two_ne_zero, fun u hu => ?_⟩
    by_cases hM1 : M = 1
    · subst hM1; exact one_dvd _
    have h2 : 2 ≤ M ^ 2 := by nlinarith [Nat.pos_of_ne_zero hM.ne', show 2 ≤ M by omega]
    have h1 := one_le_val_unit h2 u
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ h1)]
    push_cast
    rw [mem_deltaPm, ZMod.castHom_apply, ZMod.cast_eq_val] at hu
    rcases hu with hu | hu <;> rw [hu] <;> ring
  have hε0 := (epsDelta_pos (Δ := deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero))).ne'
  apply Nat.eq_of_factorization_eq (hDelta_ne_zero _) hM.ne'
  intro p
  rw [factorization_hDelta, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have := (Nat.factorization_le_iff_dvd hM.ne' hε0).2 hMε p
  omega

/-! ### Nor(±Γ(N)) and Nor(Γ(N)) -/

theorem normG_pmGammaR' (N : ℕ) [NeZero N] : NormG (pmGammaR N) = SL2ZR := by
  apply le_antisymm _ (SL2ZR_le_normG_pmGammaR N)
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (N ^ 2) := ⟨by positivity⟩
  set Δ := deltaPm (N ^ 2) N (dvd_pow_self N two_ne_zero)
  have hconj := conj_GammaDelta_sq' N hN
  intro g hg
  have key := Subgroup.map_equiv_normalizer_eq (GammaDeltaR (N ^ 2) Δ) (MulAut.conj (Dm N))
  have hg' : g ∈ (Subgroup.normalizer (GammaDeltaR (N ^ 2) Δ : Set SL(2, ℝ))).map
      (MulAut.conj (Dm N)).toMonoidHom := by
    rw [key, hconj]; exact hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg'
  obtain ⟨a, b, c, d, e, he0, hen, hdet, ε, hε, hgm⟩ := newman_delta' Δ hg₀
  rw [hDelta_deltaPm_sq N hN] at hen hdet hgm
  rw [Nat.div_self (by positivity)] at hen hdet
  have he1 : e = 1 := Nat.dvd_one.1 hen
  subst he1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdet' : a * d - b * c = 1 := by push_cast at hdet; linear_combination hdet
  have hgm' : (g₀ : Matrix (Fin 2) (Fin 2) ℝ) = !![ε * a, ε * b / N; ε * (N * c), ε * d] := by
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> (try ring) <;> simp
  have hconjm := coe_conj_Dm hN hgm'
  rcases hε with rfl | rfl
  · refine ⟨mkSL a b c d hdet', Subgroup.mem_top _, Subtype.ext ?_⟩
    change _ = ((MulAut.conj (Dm N) g₀ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hconjm, coe_ofZ_mkSL]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · refine ⟨mkSL (-a) (-b) (-c) (-d) (by linear_combination hdet'), Subgroup.mem_top _,
      Subtype.ext ?_⟩
    change _ = ((MulAut.conj (Dm N) g₀ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hconjm, coe_ofZ_mkSL]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem normG_GammaR' (N : ℕ) [NeZero N] : NormG (GammaR N) = SL2ZR :=
  le_antisymm ((normG_GammaR_le_normG_pmGammaR N).trans (normG_pmGammaR' N).le)
    (SL2ZR_le_normG_GammaR N)

/-! ### S₇ at level 49 -/

theorem S7_mem_normG_GammaDeltaR_49' :
    S 7 ∈ NormG (GammaDeltaR 49 (deltaPm 49 7 (by norm_num))) ∧ S 7 ∉ Norm0 49 := by
  constructor
  · have hconj := conj_GammaDelta_sq' 7 (by norm_num)
    have hT : ofZ (mkSL 1 1 0 1 (by norm_num)) ∈ NormG (pmGammaR 7) :=
      SL2ZR_le_normG_pmGammaR 7 (ofZ_mem_toR (Subgroup.mem_top _))
    have key := Subgroup.map_equiv_normalizer_eq
      (GammaDeltaR (7 ^ 2) (deltaPm (7 ^ 2) 7 (dvd_pow_self 7 two_ne_zero))) (MulAut.conj (Dm 7))
    have hT' : ofZ (mkSL 1 1 0 1 (by norm_num)) ∈ (Subgroup.normalizer
        (GammaDeltaR (7 ^ 2) (deltaPm (7 ^ 2) 7 (dvd_pow_self 7 two_ne_zero)) : Set SL(2, ℝ))).map
        (MulAut.conj (Dm 7)).toMonoidHom := by
      rw [key, hconj]; exact hT
    obtain ⟨g₀, hg₀, hg₀T⟩ := hT'
    have hS : (MulAut.conj (Dm 7)) (S 7) = ofZ (mkSL 1 1 0 1 (by norm_num)) := by
      apply Subtype.ext
      rw [coe_conj_Dm (by norm_num) (coe_S 7), coe_ofZ_mkSL]
      ext i j; fin_cases i <;> fin_cases j <;> norm_num
    have : g₀ = S 7 := (MulAut.conj (Dm 7)).injective (hg₀T.trans hS.symm)
    rw [this] at hg₀
    exact hg₀
  · intro hS
    obtain ⟨a, b, c, d, e, he0, hen, hdet, ε, hε, hgm⟩ := newman' hS
    have h4 : ¬ 4 ∣ 49 := by norm_num
    have h9 : ¬ 9 ∣ 49 := by norm_num
    rw [nPart_eq_of h4 h9] at hen hdet
    rw [hPart_eq_one_of h4 h9, coe_S] at hgm
    have hsq : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast he0)).ne'
    have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have e10 := congrFun (congrFun hgm 1) 0
    have e01 := congrFun (congrFun hgm 0) 1
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      smul_eq_mul, Nat.cast_one, div_one] at e10 e01
    have hc : c = 0 := by
      rcases mul_eq_zero.1 e10.symm with h | h
      · exact absurd h (div_ne_zero hε0 hsq)
      · have : (c : ℝ) = 0 := by
          rcases mul_eq_zero.1 h with h' | h'
          · norm_num at h'
          · exact h'
        exact_mod_cast this
    rw [hc] at hdet
    have he1 : e = 1 := by
      have h1 : (e : ℤ) * (a * d * e - 1) = 0 := by linear_combination hdet
      rcases mul_eq_zero.1 h1 with h | h
      · omega
      · have : (e : ℤ) ∣ 1 := ⟨a * d, by linear_combination -h⟩
        exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    subst he1
    simp only [Nat.cast_one, Real.sqrt_one, div_one] at e01
    have h7 : (7 : ℝ) * (ε * b) = 1 := by rw [← e01]; norm_num
    rcases hε with rfl | rfl
    · have : (7 * b : ℤ) = 1 := by exact_mod_cast (show (7 : ℝ) * b = 1 by linarith)
      omega
    · have : (7 * b : ℤ) = -1 := by exact_mod_cast (show (7 : ℝ) * b = -1 by linarith)
      omega

end

end NormalizerLean
