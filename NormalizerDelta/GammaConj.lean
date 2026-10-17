module

public import NormalizerDelta.SIota

@[expose] public section

/-!
# §G: conjugation by diag(M, 1): X_Δ(N) ≅ X₁(M, N/M) and X_Δ(M²) ≅ X(M)

D = projSL diag(M, 1) = diag(√M, 1/√M) acts by D [[a, b], [c, d]] D⁻¹ = [[a, Mb], [c/M, d]].
For M² ∣ N and Δ = {d ≡ ±1 mod N/M} this maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)): for γ ∈ Γ_Δ(N) with
d ≡ ε (ε = ±1) mod N/M, ε·DγD⁻¹ ∈ Γ(M) ∩ Γ₁(N/M) (M ∣ N/M, and a ≡ d⁻¹); conversely the preimage of
ζ ∈ Γ(M) ∩ Γ₁(N/M) is [[a, b/M], [Mc, d]] ∈ Γ_Δ(N), and −1 ∈ Γ_Δ(N).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- D = diag(M, 1) in SL₂(ℝ). -/
abbrev Dm (M : ℕ) : SL(2, ℝ) := projSL !![(M : ℝ), 0; 0, 1]

theorem coe_Dm {M : ℕ} (hM : 0 < M) :
    (Dm M : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.sqrt M, 0; 0, (Real.sqrt M)⁻¹] := by
  have hdet : 0 < (!![(M : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [det_fin_two_of]; simp; exact_mod_cast hM
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  rw [Dm, coe_projSL _ hdet]
  simp only [det_fin_two_of, mul_one, mul_zero, sub_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Conjugation by D: [[a, b], [c, d]] ↦ [[a, Mb], [c/M, d]]. -/
theorem coe_conj_Dm {M : ℕ} (hM : 0 < M) {Y : SL(2, ℝ)} {a b c d : ℝ}
    (hY : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M) Y : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, M * b; c / M, d] := by
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [MulAut.conj_apply, coe_conj, coe_Dm hM, hY, adjugate_fin_two_of]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

theorem mem_deltaPm {N K : ℕ} {h : K ∣ N} {u : (ZMod N)ˣ} :
    u ∈ deltaPm N K h ↔ (ZMod.castHom h (ZMod K) (u : ZMod N) = 1 ∨
      ZMod.castHom h (ZMod K) (u : ZMod N) = -1) := by
  unfold deltaPm
  rw [Subgroup.mem_comap]
  have := @mem_pmOne K (Units.map (ZMod.castHom h (ZMod K)).toMonoidHom u)
  unfold pmOne at this
  rw [this, Units.ext_iff, Units.ext_iff]
  simp

theorem deltaPm_congr {N K K' : ℕ} (hK : K = K') (h : K ∣ N) (h' : K' ∣ N) :
    deltaPm N K h = deltaPm N K' h' := by subst hK; rfl

theorem toR_sup_zpowers (H : Subgroup SL(2, ℤ)) :
    toR (H ⊔ Subgroup.zpowers (-1)) = toR H ⊔ Subgroup.zpowers (-1) := by
  rw [toR, Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mem_sup_pm_iff {H : Subgroup SL(2, ℤ)} {x : SL(2, ℤ)} :
    x ∈ H ⊔ Subgroup.zpowers (-1) ↔ x ∈ H ∨ -x ∈ H := by
  let S : Subgroup SL(2, ℤ) :=
    { carrier := {x | x ∈ H ∨ -x ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (H.mul_mem hx hy)
        · right; have := H.mul_mem hx hy; rwa [mul_neg] at this
        · right; have := H.mul_mem hx hy; rwa [neg_mul] at this
        · left; have := H.mul_mem hx hy; rwa [neg_mul_neg] at this
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (H.inv_mem hx)
        · right; have := H.inv_mem hx
          rwa [show (-x)⁻¹ = -x⁻¹ by
            rw [inv_eq_iff_eq_inv]; ext i j; simp] at this }
  constructor
  · intro hx
    have hle : H ⊔ Subgroup.zpowers (-1) ≤ S := sup_le (fun y hy => Or.inl hy)
      (by rw [Subgroup.zpowers_le]; right; simp [H.one_mem])
    exact hle hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : x = (-1) * -x := by rw [neg_mul, one_mul, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left hx)

theorem zmod_eq_one {m : ℕ} {x : ℤ} (h : (m : ℤ) ∣ x - 1) : (x : ZMod m) = 1 := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub x 1 m).2 (by have := h.neg_right; convert this using 1; ring)
  simpa using this

theorem dvd_of_zmod_eq_one {m : ℕ} {x : ℤ} (h : (x : ZMod m) = 1) : (m : ℤ) ∣ x - 1 := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub x 1 m).1 (by simpa using h)
  have := this.neg_right; convert this using 1; ring

theorem dvd_of_zmod_eq_neg_one {m : ℕ} {x : ℤ} (h : (x : ZMod m) = -1) : (m : ℤ) ∣ x + 1 := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub x (-1) m).1 (by simpa using h)
  have := this.neg_right; convert this using 1; ring

theorem zmod_eq_neg_one {m : ℕ} {x : ℤ} (h : (m : ℤ) ∣ x + 1) : (x : ZMod m) = -1 := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub x (-1) m).2 (by have := h.neg_right; convert this using 1; ring)
  simpa using this

/-- The element of Γ(M) ∩ Γ₁(K) given by the entries. -/
theorem mkSL_mem_GammaGamma1 {M K : ℕ} (hMK : M ∣ K) {a b c d : ℤ} (h : a * d - b * c = 1)
    (hb : (M : ℤ) ∣ b) (hc : (K : ℤ) ∣ c) (hd : (K : ℤ) ∣ d - 1) (ha : (K : ℤ) ∣ a - 1) :
    mkSL a b c d h ∈ CongruenceSubgroup.Gamma M ⊓ CongruenceSubgroup.Gamma1 K := by
  have hMK' : (M : ℤ) ∣ K := Int.natCast_dvd_natCast.2 hMK
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma_mem]
    simp only [mkSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    exact ⟨zmod_eq_one (hMK'.trans ha), (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hMK'.trans hc), zmod_eq_one (hMK'.trans hd)⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp only [mkSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    exact ⟨zmod_eq_one ha, zmod_eq_one hd, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc⟩

/-- **X_Δ(N) ≅ X₁(M, N/M)** (general form). -/
theorem conj_GammaDelta_X1MN' {M N : ℕ} [NeZero N] (hM : 0 < M) (hMN : M ^ 2 ∣ N) :
    (GammaDeltaR N (deltaPm N (N / M)
        (Nat.div_dvd_of_dvd ((dvd_pow_self M two_ne_zero).trans hMN)))).map
        (MulAut.conj (projSL !![(M : ℝ), 0; 0, 1])).toMonoidHom =
      toR (CongruenceSubgroup.Gamma M ⊓ CongruenceSubgroup.Gamma1 (N / M)) ⊔
        Subgroup.zpowers (-1) := by
  have hMd : M ∣ N := (dvd_pow_self M two_ne_zero).trans hMN
  set hKN := Nat.div_dvd_of_dvd hMd
  set K := N / M with hKdef
  have hNK : N = M * K := (Nat.mul_div_cancel' hMd).symm
  have hMK : M ∣ K := by
    rw [hNK, pow_two] at hMN; exact Nat.dvd_of_mul_dvd_mul_left hM hMN
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← toR_sup_zpowers]
  apply le_antisymm
  · rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨γ, ⟨h0, u, hu, hud⟩, rfl⟩ := mem_toR.1 hY
    have hc : (N : ℤ) ∣ γ 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 h0)
    obtain ⟨c₂, hc₂⟩ := hc
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by have := γ.2; rwa [det_fin_two] at this
    have hdet' : γ 0 0 * γ 1 1 - (M * γ 0 1) * (K * c₂) = 1 := by
      rw [hc₂, hNK] at hdet; push_cast at hdet; linear_combination hdet
    have hconj : (MulAut.conj (Dm M)).toMonoidHom (ofZ γ) =
        ofZ (mkSL (γ 0 0) (M * γ 0 1) (K * c₂) (γ 1 1) hdet') := by
      apply Subtype.ext
      change ((MulAut.conj (Dm M) (ofZ γ) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = _
      rw [coe_conj_Dm hM (coe_ofZ γ), coe_ofZ_mkSL, hc₂, hNK]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp
    rw [hconj]
    apply ofZ_mem_toR
    -- d ≡ ±1 (mod K), and a ≡ d (mod K)
    have hKd : ((ZMod.castHom hKN (ZMod K)) (u : ZMod N)) = ((γ 1 1 : ℤ) : ZMod K) := by
      rw [hud, map_intCast]
    have hKc : (K : ℤ) ∣ γ 0 0 * γ 1 1 - 1 :=
      ⟨M * γ 0 1 * c₂, by linear_combination hdet'⟩
    rcases mem_deltaPm.1 hu with h1 | h1 <;> rw [hKd] at h1
    · have hd := dvd_of_zmod_eq_one h1
      have ha : (K : ℤ) ∣ γ 0 0 - 1 := by
        have := dvd_sub hKc (dvd_mul_of_dvd_right hd (γ 0 0))
        convert this using 1; ring
      exact mem_sup_pm_iff.2 (Or.inl (mkSL_mem_GammaGamma1 hMK hdet' (dvd_mul_right _ _)
        (dvd_mul_right _ _) hd ha))
    · have hd := dvd_of_zmod_eq_neg_one h1
      have ha : (K : ℤ) ∣ γ 0 0 + 1 := by
        have := dvd_sub (dvd_mul_of_dvd_right hd (γ 0 0)) hKc
        convert this using 1; ring
      have hneg : -mkSL (γ 0 0) (M * γ 0 1) (K * c₂) (γ 1 1) hdet' =
          mkSL (-γ 0 0) (-(M * γ 0 1)) (-(K * c₂)) (-γ 1 1) (by linear_combination hdet') := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mkSL, SpecialLinearGroup.coe_neg] <;> rfl
      refine mem_sup_pm_iff.2 (Or.inr ?_)
      rw [hneg]
      exact mkSL_mem_GammaGamma1 hMK _ ((dvd_mul_right _ _).neg_right) ((dvd_mul_right _ _).neg_right)
        (by have := hd.neg_right; convert this using 1; ring)
        (by have := ha.neg_right; convert this using 1; ring)
  · rintro _ ⟨ζ, hζ, rfl⟩
    -- M ∣ b, K ∣ c, d ≡ ±1 (mod K)
    have key : (M : ℤ) ∣ ζ 0 1 ∧ (K : ℤ) ∣ ζ 1 0 ∧ ((K : ℤ) ∣ ζ 1 1 - 1 ∨ (K : ℤ) ∣ ζ 1 1 + 1) := by
      rcases mem_sup_pm_iff.1 hζ with hζ' | hζ'
      · obtain ⟨hG, hG1⟩ := Subgroup.mem_inf.1 hζ'
        rw [CongruenceSubgroup.Gamma_mem] at hG
        rw [CongruenceSubgroup.Gamma1_mem] at hG1
        exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hG.2.1,
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hG1.2.2, Or.inl (dvd_of_zmod_eq_one hG1.2.1)⟩
      · obtain ⟨hG, hG1⟩ := Subgroup.mem_inf.1 hζ'
        rw [CongruenceSubgroup.Gamma_mem] at hG
        rw [CongruenceSubgroup.Gamma1_mem] at hG1
        simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at hG hG1
        refine ⟨?_, ?_, Or.inr ?_⟩
        · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (-ζ 0 1) M).1 (by simpa using hG.2.1)
          exact (dvd_neg).1 this
        · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (-ζ 1 0) K).1 (by simpa using hG1.2.2)
          exact (dvd_neg).1 this
        · have := dvd_of_zmod_eq_one (m := K) (x := -ζ 1 1) (by simpa using hG1.2.1)
          have := this.neg_right; convert this using 1; ring
    obtain ⟨⟨b₁, hb₁⟩, ⟨c₁, hc₁⟩, hd⟩ := key
    have hdet : ζ 0 0 * ζ 1 1 - ζ 0 1 * ζ 1 0 = 1 := by have := ζ.2; rwa [det_fin_two] at this
    have hdet' : ζ 0 0 * ζ 1 1 - b₁ * (N * c₁) = 1 := by
      rw [hb₁, hc₁] at hdet; rw [hNK]; push_cast; linear_combination hdet
    set γ := mkSL (ζ 0 0) b₁ (N * c₁) (ζ 1 1) hdet'
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [γ, mkSL]
    obtain ⟨u, hu⟩ := exists_unit_of_mem_Gamma0 hγ0
    have hu' : (u : ZMod N) = ((ζ 1 1 : ℤ) : ZMod N) := by rw [hu]; simp [γ, mkSL]
    have huΔ : u ∈ deltaPm N K hKN := by
      rw [mem_deltaPm, hu', map_intCast]
      rcases hd with hd | hd
      · exact Or.inl (zmod_eq_one hd)
      · exact Or.inr (zmod_eq_neg_one hd)
    refine ⟨ofZ γ, ofZ_mem_toR ⟨hγ0, u, huΔ, hu⟩, ?_⟩
    apply Subtype.ext
    change ((MulAut.conj (Dm M) (ofZ γ) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [coe_conj_Dm hM (coe_ofZ γ), coe_ofZ]
    ext i j; fin_cases i <;> fin_cases j <;> simp [γ, mkSL, hb₁, hc₁, hNK] <;> field_simp

/-- **X_Δ(N) ≅ X₁(M, N/M)** for N = M²: X_Δ(M²) ≅ X(M). -/
theorem conj_GammaDelta_sq' (M : ℕ) (hM : 0 < M) :
    (GammaDeltaR (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero))).map
        (MulAut.conj (projSL !![(M : ℝ), 0; 0, 1])).toMonoidHom = pmGammaR M := by
  haveI : NeZero (M ^ 2) := ⟨by positivity⟩
  have hK : M ^ 2 / M = M := by rw [pow_two, Nat.mul_div_cancel _ hM]
  have h := conj_GammaDelta_X1MN' (N := M ^ 2) hM dvd_rfl
  rw [deltaPm_congr hK _ (dvd_pow_self M two_ne_zero)] at h
  rw [h, hK, inf_eq_left.2 (fun γ hγ => by
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩)]
  rfl

end

end NormalizerLean
