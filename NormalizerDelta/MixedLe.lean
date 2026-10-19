module

public import NormalizerDelta.MixedBasic

@[expose] public section

/-!
# Part 8: §A for H₁ of type I

* The local conditions on H = Γ mod N₁N₂ at q ∣ N₁ are those on H₁ (`isBorelMod_inf_iff`, `isSplitMod_inf_iff`),
  as Γ maps onto H₁.
* `isUnit_det_inf` (DLM26, Prop. 4.5(1), (4)): det m is prime to N₁.
* `normG_inf_le'`: with D = det m prime to N₁, Γ_{H₂}(N₂) = Γ·Γ(N₂D), and conjugation by (det m)^{-1/2}·m maps
  Γ(N₂D) into Γ(N₂) (`conj_mem_Gamma_of_mem_Gamma_mul`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

section Local

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

theorem fixesLine_inf_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {q : ℕ} (hq : q ∣ N₁) (v : Fin 2 → ZMod q) :
    FixesLine ((GammaH N₁ H₁ ⊓ GammaH N₂ H₂).map (redSL (N₁ * N₂))) q v ↔ FixesLine H₁ q v := by
  have hqN : q ∣ N₁ * N₂ := hq.trans (dvd_mul_right _ _)
  constructor
  · intro h h₁ hh₁
    obtain ⟨γ, hγ, rfl⟩ := exists_mem_inf_redSL hcop H₁ H₂ hh₁
    obtain ⟨c, hc⟩ := h (redSL (N₁ * N₂) γ) (Subgroup.mem_map_of_mem _ hγ)
    refine ⟨c, ?_⟩
    rw [map_cast_redSL hq]
    rw [map_cast_redSL hqN] at hc
    exact hc
  · rintro h _ ⟨γ, hγ, rfl⟩
    obtain ⟨c, hc⟩ := h (redSL N₁ γ) (Subgroup.mem_inf.1 hγ).1
    refine ⟨c, ?_⟩
    rw [map_cast_redSL hqN]
    rw [map_cast_redSL hq] at hc
    exact hc

theorem isBorelMod_inf_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {q : ℕ} (hq : q ∣ N₁) :
    IsBorelMod ((GammaH N₁ H₁ ⊓ GammaH N₂ H₂).map (redSL (N₁ * N₂))) q ↔ IsBorelMod H₁ q := by
  simp only [IsBorelMod, fixesLine_inf_iff hcop H₁ H₂ hq]

theorem isSplitMod_inf_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {q : ℕ} (hq : q ∣ N₁) :
    IsSplitMod ((GammaH N₁ H₁ ⊓ GammaH N₂ H₂).map (redSL (N₁ * N₂))) q ↔ IsSplitMod H₁ q := by
  simp only [IsSplitMod, fixesLine_inf_iff hcop H₁ H₂ hq]

theorem isUnit_intCast_iff_coprime {N : ℕ} {x : ℤ} (hx : 0 ≤ x) :
    IsUnit ((x : ℤ) : ZMod N) ↔ Nat.Coprime x.toNat N := by
  rw [← ZMod.isUnit_iff_coprime, ← Int.cast_natCast, Int.toNat_of_nonneg hx]

theorem isUnit_det_inf (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)}
    (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ N₁ → ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) :
    IsUnit ((m.det : ℤ) : ZMod N₁) := by
  have : NeZero (N₁ * N₂) := ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  rw [← GammaH_map' (Gamma_le_inf H₁ H₂)] at hg
  have hnd : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ (p : ℤ) ∣ m.det := by
    intro p hp hpN hpd
    have hpd1 : (p : ℤ) ^ 1 ∣ m.det := by rwa [pow_one]
    rcases hloc p hp hpN with hB | hS
    · apply hB
      have := isBorelMod_of_dvd_det' hdet hg hp (hprim p hp hpN) hpd1
      rw [pow_one] at this
      exact (isBorelMod_inf_iff hcop H₁ H₂ hpN).1 this
    · have hk : p ^ N₁.factorization p ∣ N₁ := Nat.ordProj_dvd N₁ p
      have hS' := (isSplitMod_inf_iff hcop H₁ H₂ hk).2 hS
      have hle := le_of_isSplitMod' hdet hg hp (hprim p hp hpN) (hk.trans (dvd_mul_right _ _)) hS' hpd1
      have hpN₂ : ¬ p ∣ N₂ := fun h =>
        hp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpN hcop) h)
      rw [Nat.factorization_mul (NeZero.ne N₁) (NeZero.ne N₂), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpN₂, add_zero] at hle
      omega
  rw [isUnit_intCast_iff_coprime hdet.le]
  exact Nat.coprime_of_dvd fun k hk h1 h2 =>
    hnd k hk h2 (by
      have := Int.natCast_dvd_natCast.2 h1
      rwa [Int.toNat_of_nonneg hdet.le] at this)

end Local

/-! ### Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)) -/

/-- Conjugation by (det m)^{-1/2}·m maps Γ(K·det m) into Γ(K). -/
theorem conj_mem_Gamma_of_mem_Gamma_mul {K : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    {s : SL(2, ℤ)} (hs : s ∈ CongruenceSubgroup.Gamma (K * m.det.toNat)) :
    projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ s * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈
      toR (CongruenceSubgroup.Gamma K) := by
  set D := m.det with hD
  have hKD : ((K * D.toNat : ℕ) : ℤ) = K * D := by push_cast; rw [Int.toNat_of_nonneg hdet.le]
  -- s = 1 + (K D) T
  have hdvd : ∀ i j, ((K * D.toNat : ℕ) : ℤ) ∣ (s : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    rw [CongruenceSubgroup.Gamma_mem'] at hs
    have := congrArg (fun X : SL(2, ZMod (K * D.toNat)) => (X : Matrix (Fin 2) (Fin 2) (ZMod (K * D.toNat))) i j) hs
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast, Matrix.SpecialLinearGroup.coe_one] at this
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set T : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j =>
    ((s : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) / (K * D) with hT
  have hsT : (s : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (K * D) • T := by
    ext i j
    simp only [hT, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [mul_comm, Int.ediv_mul_cancel (hKD ▸ hdvd i j)]
    ring
  set S : Matrix (Fin 2) (Fin 2) ℤ := 1 + (K : ℤ) • (m * T * adjugate m) with hS
  have hrel : m * (s : Matrix (Fin 2) (Fin 2) ℤ) = S * m := by
    rw [hsT, hS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.adjugate_mul]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul, ← hD]
  have hSdet : S.det = 1 := by
    have h1 := congrArg Matrix.det hrel
    rw [det_mul, det_mul, s.2, mul_one] at h1
    have : D * (S.det - 1) = 0 := by rw [hD]; linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hdet.ne'
    · linear_combination h
  let σ : SL(2, ℤ) := ⟨S, hSdet⟩
  have hSmem : σ ∈ CongruenceSubgroup.Gamma K := by
    apply CongruenceSubgroup.Gamma_mem'.2
    apply Subtype.ext
    ext i j
    show ((S i j : ℤ) : ZMod K) = (1 : Matrix (Fin 2) (Fin 2) (ZMod K)) i j
    rw [hS]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have he : projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ s = ofZ σ * projSL (m.map (Int.cast : ℤ → ℝ)) :=
    (projSL_mul_ofZ_eq_iff hdet s σ).2 hrel
  rw [he, mul_inv_cancel_right]
  exact ofZ_mem_toR hSmem

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- For x = (det m)^{-1/2}·m ∈ Nor(Γ) with det m prime to N₁: x Γ_{H₂}(N₂) x⁻¹ ⊆ Γ_{H₂}(N₂). -/
theorem conj_mem_GammaH_of_mem_normG_inf (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hu : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hY : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)))
    {δ : SL(2, ℤ)} (hδ : δ ∈ GammaH N₂ H₂) :
    projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ δ * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈
      toR (GammaH N₂ H₂) := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ))
  set D := m.det.toNat
  have hD0 : D ≠ 0 := by simp [D]; exact hdet
  have : NeZero (N₂ * D) := ⟨Nat.mul_ne_zero (NeZero.ne N₂) hD0⟩
  have hcopD : N₁.Coprime D := ((isUnit_intCast_iff_coprime hdet.le).1 hu).symm
  obtain ⟨s, hs1, hs⟩ := exists_lift_mod_one (Nat.Coprime.mul_right hcop hcopD) (redSL N₁ δ)
  have hs2 : redSL N₂ s = 1 := by
    have := Gamma_le_Gamma_of_dvd (dvd_mul_right N₂ D) hs
    rwa [CongruenceSubgroup.Gamma_mem'] at this
  have hγ : δ * s⁻¹ ∈ GammaH N₁ H₁ ⊓ GammaH N₂ H₂ := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show redSL N₁ (δ * s⁻¹) ∈ H₁
      rw [map_mul, map_inv, hs1, mul_inv_cancel]; exact H₁.one_mem
    · show redSL N₂ (δ * s⁻¹) ∈ H₂
      rw [map_mul, map_inv, hs2, inv_one, mul_one]; exact hδ
  have h1 : P * ofZ (δ * s⁻¹) * P⁻¹ ∈ toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂) :=
    ((Subgroup.mem_normalizer_iff.1 hY) _).1 (ofZ_mem_toR hγ)
  have h2 := conj_mem_Gamma_of_mem_Gamma_mul (K := N₂) hdet hs
  have e : P * ofZ δ * P⁻¹ = (P * ofZ (δ * s⁻¹) * P⁻¹) * (P * ofZ s * P⁻¹) := by
    rw [show ofZ (δ * s⁻¹) = ofZ δ * (ofZ s)⁻¹ by simp [map_mul, map_inv]]; group
  rw [e]
  exact mul_mem (Subgroup.map_mono inf_le_right h1) (Subgroup.map_mono (Gamma_le_GammaH N₂ H₂) h2)

theorem normG_inf_le' (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p)) :
    NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ≤ NormG (toR (GammaH N₂ H₂)) := by
  intro Y hY
  have : NeZero (N₁ * N₂) := ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  obtain ⟨m, hdet, -, hprim, rfl⟩ := normG_level_form' (Gamma_le_inf H₁ H₂) hY
  have hu := isUnit_det_inf hcop H₂ hloc hdet (fun p hp _ => hprim p hp) hY
  have hdet' : 0 < (adjugate m).det := by rwa [det_adjugate_two]
  have hu' : IsUnit (((adjugate m).det : ℤ) : ZMod N₁) := by rwa [det_adjugate_two]
  have hY' := adjugate_mem_normG hdet hY
  rw [Subgroup.mem_normalizer_iff]
  intro Z
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact conj_mem_GammaH_of_mem_normG_inf hcop H₁ H₂ hdet hu hY hδ
  · intro hZ
    obtain ⟨δ, hδ, he⟩ := mem_toR.1 hZ
    have := conj_mem_GammaH_of_mem_normG_inf hcop H₁ H₂ hdet' hu' hY' hδ
    rw [projSL_adjugate hdet, inv_inv, he] at this
    rwa [show (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * (projSL (m.map (Int.cast : ℤ → ℝ)) * Z *
      (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹) * projSL (m.map (Int.cast : ℤ → ℝ)) = Z by group] at this


/-- `isUnit_det_inf` with `NeZero N₂` as an explicit argument (N₂ does not occur in the conclusion, so `apply`
cannot synthesize the instance). -/
theorem isUnit_det_of_mem_normG_inf' {N₁ N₂ : ℕ} [NeZero N₁] (hN₂ : NeZero N₂) (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ N₁ → ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) :
    IsUnit ((m.det : ℤ) : ZMod N₁) :=
  isUnit_det_inf hcop H₂ hloc hdet hprim hg

end

end NormalizerLean
