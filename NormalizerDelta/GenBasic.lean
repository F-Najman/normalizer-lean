module

public import NormalizerDelta.CartanIndex
public import NormalizerDelta.DefsGeneral

@[expose] public section

/-!
# General modular curves: basics, §H and §R

* Helpers on P = projSL m for an integer matrix m with det m > 0: P γ = γ' P iff m γ = γ' m
  (`projSL_mul_ofZ_eq_iff`); if P normalizes Γ, then for γ ∈ Γ there are γ' ∈ Γ with γ m = m γ' and m γ = γ' m;
  projSL (adj m) = P⁻¹; and det m ∣ N m_ij² (conjugate [[1, N], [0, 1]] and [[1, 0], [N, 1]]).
* §H: Γ_H = comap of H under the reduction, whose kernel is Γ(N).
* §R: conjugation by γ ∈ SL₂(ℤ) on Γ_H is conjugation by γ mod N on H (the reduction is onto).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### projSL of integer matrices -/

theorem det_map_intCast (m : Matrix (Fin 2) (Fin 2) ℤ) : (m.map (Int.cast : ℤ → ℝ)).det = (m.det : ℝ) := by
  have := RingHom.map_det (Int.castRingHom ℝ) m
  simpa using this.symm

theorem coe_projSL_int {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det) :
    ((projSL (m.map (Int.cast : ℤ → ℝ)) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt m.det)⁻¹ • m.map (Int.cast : ℤ → ℝ) := by
  have hDr : (0 : ℝ) < m.det := by exact_mod_cast hD
  rw [coe_projSL _ (by rw [det_map_intCast]; exact hDr), det_map_intCast]

theorem coe_ofZ_eq_map (γ : SL(2, ℤ)) :
    (ofZ γ : Matrix (Fin 2) (Fin 2) ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe]

/-- P γ = γ' P iff m γ = γ' m, for P = projSL m. -/
theorem projSL_mul_ofZ_eq_iff {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det) (γ γ' : SL(2, ℤ)) :
    projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ = ofZ γ' * projSL (m.map (Int.cast : ℤ → ℝ)) ↔
      m * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  have hDr : (0 : ℝ) < m.det := by exact_mod_cast hD
  have hs : (Real.sqrt m.det)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hDr).ne'
  constructor
  · intro h
    have h2 := congrArg (fun X : SL(2, ℝ) => (X : Matrix (Fin 2) (Fin 2) ℝ)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hD, coe_ofZ_eq_map, Matrix.smul_mul,
      Matrix.mul_smul] at h2
    have h3 := smul_right_injective _ hs h2
    ext i j
    have := congrFun (congrFun h3 i) j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at this
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact_mod_cast this
  · intro h
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hD, coe_ofZ_eq_map, Matrix.smul_mul,
      Matrix.mul_smul]
    congr 1
    ext i j
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => ((M i j : ℤ) : ℝ)) h
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
    push_cast at this
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    exact this

theorem exists_rel_right {Γ : Subgroup SL(2, ℤ)} {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    ∃ γ' ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ) * m = m * (γ' : Matrix (Fin 2) (Fin 2) ℤ) := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hP
  have hmem : P⁻¹ * ofZ γ * P ∈ toR Γ := by
    apply ((Subgroup.mem_normalizer_iff.1 hg) (P⁻¹ * ofZ γ * P)).2
    rw [show P * (P⁻¹ * ofZ γ * P) * P⁻¹ = ofZ γ by group]
    exact ofZ_mem_toR hγ
  obtain ⟨γ', hγ', he⟩ := mem_toR.1 hmem
  refine ⟨γ', hγ', ((projSL_mul_ofZ_eq_iff hD γ' γ).1 ?_).symm⟩
  rw [he, ← hP]; group

theorem exists_rel_left {Γ : Subgroup SL(2, ℤ)} {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    ∃ γ' ∈ Γ, m * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hP
  have hmem : P * ofZ γ * P⁻¹ ∈ toR Γ := ((Subgroup.mem_normalizer_iff.1 hg) (ofZ γ)).1 (ofZ_mem_toR hγ)
  obtain ⟨γ', hγ', he⟩ := mem_toR.1 hmem
  refine ⟨γ', hγ', (projSL_mul_ofZ_eq_iff hD γ γ').1 ?_⟩
  rw [he, ← hP]; group

theorem det_adjugate_two (m : Matrix (Fin 2) (Fin 2) ℤ) : (adjugate m).det = m.det := by
  rw [adjugate_fin_two, det_fin_two_of, det_fin_two]; ring

theorem projSL_adjugate {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det) :
    projSL ((adjugate m).map (Int.cast : ℤ → ℝ)) = (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ := by
  have hD' : 0 < (adjugate m).det := by rwa [det_adjugate_two]
  apply Subtype.ext
  rw [coe_projSL_int hD', Matrix.SpecialLinearGroup.coe_inv, coe_projSL_int hD, det_adjugate_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two]

theorem adjugate_mem_normG {Γ : Subgroup SL(2, ℤ)} {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ)) :
    projSL ((adjugate m).map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ) := by
  rw [projSL_adjugate hD]; exact inv_mem hg

/-- det m ∣ N m_ij² (DLM26, proof of Prop. 4.3(2)). -/
theorem det_dvd_mul_sq {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ)) (i j : Fin 2) : m.det ∣ N * m i j ^ 2 := by
  obtain ⟨γ₁, -, h1⟩ := exists_rel_left hD hg (hΓ (tN_mem N))
  obtain ⟨γ₂, -, h2⟩ := exists_rel_left hD hg (hΓ (uN_mem N))
  have E1 := congrArg (fun M => M * adjugate m) h1
  have E2 := congrArg (fun M => M * adjugate m) h2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at E1 E2
  have a01 := congrFun (congrFun E1 0) 1
  have a10 := congrFun (congrFun E1 1) 0
  have b01 := congrFun (congrFun E2 0) 1
  have b10 := congrFun (congrFun E2 1) 0
  simp [tN, uN, mkSL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b01 b10
  have h00 : m.det ∣ N * m 0 0 ^ 2 := ⟨γ₁ 0 1, by linear_combination a01⟩
  have h01 : m.det ∣ N * m 0 1 ^ 2 := ⟨-γ₂ 0 1, by linear_combination -b01⟩
  have h10 : m.det ∣ N * m 1 0 ^ 2 := ⟨-γ₁ 1 0, by linear_combination -a10⟩
  have h11 : m.det ∣ N * m 1 1 ^ 2 := ⟨γ₂ 1 0, by linear_combination b10⟩
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem isCoprime_pow_of_not_dvd {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) (k n : ℕ) :
    IsCoprime ((p : ℤ) ^ k) (x ^ n) :=
  ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp)).2 hx).pow

/-- If m is not divisible by p and p^k ∣ det m, then p^k ∣ N. -/
theorem pow_dvd_of_dvd_det {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ)) {p k : ℕ} (hp : p.Prime)
    (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j) (hk : (p : ℤ) ^ k ∣ m.det) : p ^ k ∣ N := by
  obtain ⟨i, j, hij⟩ := hprim
  have h := hk.trans (det_dvd_mul_sq hΓ hD hg i j)
  have := (isCoprime_pow_of_not_dvd hp hij k 2).dvd_of_dvd_mul_right h
  exact_mod_cast this

/-! ### Γ_H -/

theorem mem_GammaH {N : ℕ} {H : Subgroup SL(2, ZMod N)} {γ : SL(2, ℤ)} : γ ∈ GammaH N H ↔ redSL N γ ∈ H :=
  Iff.rfl

theorem Gamma_le_GammaH (N : ℕ) (H : Subgroup SL(2, ZMod N)) : CongruenceSubgroup.Gamma N ≤ GammaH N H :=
  fun γ h => by
    rw [mem_GammaH, show redSL N γ = 1 from h]; exact H.one_mem

theorem GammaH_mono {N : ℕ} {H K : Subgroup SL(2, ZMod N)} (h : H ≤ K) : GammaH N H ≤ GammaH N K :=
  Subgroup.comap_mono h

theorem GammaH_map' {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    GammaH N (Γ.map (redSL N)) = Γ := by
  rw [GammaH, Subgroup.comap_map_eq, show (redSL N).ker = CongruenceSubgroup.Gamma N from rfl,
    sup_eq_left.2 hΓ]

theorem index_GammaH' (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) : (GammaH N H).index = H.index :=
  Subgroup.index_comap_of_surjective H (redSL_surjective N)

/-! ### §R -/

theorem ofZ_mem_normG_GammaH_iff' (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) (γ : SL(2, ℤ)) :
    ofZ γ ∈ NormG (toR (GammaH N H)) ↔ redSL N γ ∈ NormH H := by
  constructor
  · intro hγ
    have hγ' : ofZ γ⁻¹ ∈ NormG (toR (GammaH N H)) := by
      have e : ofZ γ⁻¹ = (ofZ γ)⁻¹ := map_inv _ γ
      rw [e]; exact inv_mem hγ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    obtain ⟨δ, rfl⟩ := redSL_surjective N h
    constructor
    · intro hδ
      have := conj_mem_of_normG hγ (show δ ∈ GammaH N H from hδ)
      rw [mem_GammaH, map_mul, map_mul, map_inv] at this
      exact this
    · intro hδ
      have hδ' : γ * δ * γ⁻¹ ∈ GammaH N H := by
        rw [mem_GammaH, map_mul, map_mul, map_inv]; exact hδ
      have := conj_mem_of_normG hγ' hδ'
      rw [inv_inv, show γ⁻¹ * (γ * δ * γ⁻¹) * γ = δ by group] at this
      exact this
  · intro hn
    apply mem_normG_of_SL
    · intro δ hδ
      rw [mem_GammaH, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hn _).1 hδ
    · intro δ hδ
      rw [mem_GammaH, map_mul, map_mul, map_inv]
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) (redSL N δ)).1 hδ
      rwa [inv_inv] at this

theorem normG_GammaH_inf_SL2ZR' (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    NormG (toR (GammaH N H)) ⊓ SL2ZR = toR (GammaH N (NormH H)) := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, hS⟩
    obtain ⟨γ, -, rfl⟩ := (mem_toR (Γ := ⊤)).1 hS
    exact ofZ_mem_toR ((ofZ_mem_normG_GammaH_iff' N H γ).1 hg)
  · intro hg
    obtain ⟨γ, hγ, rfl⟩ := mem_toR.1 hg
    exact ⟨(ofZ_mem_normG_GammaH_iff' N H γ).2 hγ, ofZ_mem_toR (Subgroup.mem_top γ)⟩

theorem relIndex_GammaH_GammaH_normH (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    (GammaH N H).relIndex (GammaH N (NormH H)) = H.relIndex (NormH H) := by
  rw [GammaH, GammaH, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (redSL_surjective N)]

theorem relIndex_normG_inf_SL2ZR' (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    (toR (GammaH N H)).relIndex (NormG (toR (GammaH N H)) ⊓ SL2ZR) = H.relIndex (NormH H) := by
  rw [normG_GammaH_inf_SL2ZR', relIndex_toR, relIndex_GammaH_GammaH_normH]

theorem GammaH_normH_le_normG (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    toR (GammaH N (NormH H)) ≤ NormG (toR (GammaH N H)) := by
  rw [← normG_GammaH_inf_SL2ZR']; exact inf_le_left

end

end NormalizerLean
