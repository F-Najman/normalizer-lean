module

public import NormalizerDelta.DefsMixed
public import NormalizerDelta.GenMain
public import NormalizerDelta.GenFinite
public import NormalizerDelta.GenLocal

@[expose] public section

/-!
# Part 8: basics, and §A without conditions on H₁

* `exists_lift_mod_one` (Chinese remainder theorem): for N₁ prime to K, every g ∈ SL₂(ℤ/N₁) is γ mod N₁ for some
  γ ∈ Γ(K).  Hence Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) maps onto H₁, and Γ_{H₂}(N₂) onto SL₂(ℤ/N₁).
* `NormalizesMat` for invertible matrices: the adjugate also normalizes, and for g ∈ SL₂(ℤ/N) it means
  g ∈ N(H) (H is finite).
* §A, the statements without a condition on H₁: `mem_normG_inf_iff'`, `normG_inf_inf_eq'`, `relIndex_inf_normG'`,
  `exists_mul_mem_normG_inf_iff'`.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### The Chinese remainder theorem -/

theorem intCast_mul_natCast_self {N : ℕ} (a : ℤ) : ((a * N : ℤ) : ZMod N) = 0 := by
  push_cast; rw [ZMod.natCast_self, mul_zero]

/-- For N₁ prime to K, every g ∈ SL₂(ℤ/N₁) is γ mod N₁ for some γ ≡ 1 mod K. -/
theorem exists_lift_mod_one {N₁ K : ℕ} [NeZero N₁] [NeZero K] (hcop : N₁.Coprime K) (g : SL(2, ZMod N₁)) :
    ∃ γ : SL(2, ℤ), redSL N₁ γ = g ∧ γ ∈ CongruenceSubgroup.Gamma K := by
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hcop
  set G : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => (ZMod.cast ((g : Matrix (Fin 2) (Fin 2) (ZMod N₁)) i j) : ℤ)
  set M : Matrix (Fin 2) (Fin 2) ℤ := (b * K) • G + (a * N₁) • (1 : Matrix (Fin 2) (Fin 2) ℤ) with hMdef
  have e1 : ((b * K : ℤ) : ZMod N₁) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N₁) hab
    rw [Int.cast_add, intCast_mul_natCast_self, zero_add, Int.cast_one] at this
    exact this
  have e2 : ((a * N₁ : ℤ) : ZMod K) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod K) hab
    rw [Int.cast_add, intCast_mul_natCast_self, add_zero, Int.cast_one] at this
    exact this
  have hM1 : M.map (Int.cast : ℤ → ZMod N₁) = (g : Matrix (Fin 2) (Fin 2) (ZMod N₁)) := by
    ext i j
    simp only [hMdef, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add,
      Int.cast_mul, G, Matrix.of_apply, ZMod.intCast_cast, ZMod.cast_id', id]
    rw [← Int.cast_mul, e1, ← Int.cast_mul, intCast_mul_natCast_self, one_mul, zero_mul, add_zero]
  have hMK : M.map (Int.cast : ℤ → ZMod K) = 1 := by
    ext i j
    simp only [hMdef, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add,
      Int.cast_mul]
    rw [← Int.cast_mul (b : ℤ), intCast_mul_natCast_self, zero_mul, zero_add, ← Int.cast_mul, e2, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hdet_cast : ∀ q : ℕ, ((M.det : ℤ) : ZMod q) = (M.map (Int.cast : ℤ → ZMod q)).det := fun q => by
    simpa using RingHom.map_det (Int.castRingHom (ZMod q)) M
  have hd1 : ((M.det - 1 : ℤ) : ZMod N₁) = 0 := by
    rw [Int.cast_sub, hdet_cast, hM1, g.2, Int.cast_one, sub_self]
  have hdK : ((M.det - 1 : ℤ) : ZMod K) = 0 := by
    rw [Int.cast_sub, hdet_cast, hMK, Matrix.det_one, Int.cast_one, sub_self]
  have hdvd : ((N₁ * K : ℕ) : ℤ) ∣ M.det - 1 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hd1 hdK
    push_cast
    exact (Nat.Coprime.isCoprime hcop).mul_dvd hd1 hdK
  have : NeZero (N₁ * K) := ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne K)⟩
  have hdetNK : (M.map (Int.cast : ℤ → ZMod (N₁ * K))).det = 1 := by
    rw [← hdet_cast, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  obtain ⟨γ, hγ⟩ := redSL_surjective (N₁ * K) ⟨_, hdetNK⟩
  have hent : ∀ i j, ((γ i j : ℤ) : ZMod (N₁ * K)) = ((M i j : ℤ) : ZMod (N₁ * K)) := fun i j => by
    have := congrArg (fun X : SL(2, ZMod (N₁ * K)) => (X : Matrix (Fin 2) (Fin 2) (ZMod (N₁ * K))) i j) hγ
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
  have hcast : ∀ (q : ℕ), q ∣ N₁ * K → ∀ i j, ((γ i j : ℤ) : ZMod q) = ((M i j : ℤ) : ZMod q) := by
    intro q hq i j
    rw [← ZMod.cast_intCast hq, hent, ZMod.cast_intCast hq]
  refine ⟨γ, ?_, ?_⟩
  · apply Subtype.ext
    ext i j
    have := congrFun (congrFun hM1 i) j
    simp only [Matrix.map_apply] at this
    rw [← this, ← hcast N₁ (dvd_mul_right N₁ K) i j]
    simp
  · rw [CongruenceSubgroup.Gamma_mem']
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun hMK i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.SpecialLinearGroup.coe_one, ← this, ← hcast K (dvd_mul_left K N₁) i j]
    simp

/-- Every g ∈ SL₂(ℤ/N₁) is γ mod N₁ for some γ ∈ Γ(N₂) ≤ Γ_{H₂}(N₂). -/
theorem exists_mem_GammaH_redSL {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₂ : Subgroup SL(2, ZMod N₂)) (g : SL(2, ZMod N₁)) :
    ∃ γ ∈ GammaH N₂ H₂, redSL N₁ γ = g ∧ γ ∈ CongruenceSubgroup.Gamma N₂ := by
  obtain ⟨γ, h1, h2⟩ := exists_lift_mod_one hcop g
  exact ⟨γ, Gamma_le_GammaH N₂ H₂ h2, h1, h2⟩

/-- Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) maps onto H₁. -/
theorem exists_mem_inf_redSL {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) {h : SL(2, ZMod N₁)} (hh : h ∈ H₁) :
    ∃ γ ∈ GammaH N₁ H₁ ⊓ GammaH N₂ H₂, redSL N₁ γ = h := by
  obtain ⟨γ, hγ, h1, -⟩ := exists_mem_GammaH_redSL hcop H₂ h
  exact ⟨γ, Subgroup.mem_inf.2 ⟨show γ ∈ GammaH N₁ H₁ by rw [mem_GammaH, h1]; exact hh, hγ⟩, h1⟩

theorem Gamma_le_Gamma_of_dvd {M N : ℕ} (h : M ∣ N) :
    CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma M := fun γ hγ => by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ ⊢
  apply Subtype.ext
  have e := map_cast_redSL h γ
  rw [hγ, Matrix.SpecialLinearGroup.coe_one] at e
  ext i j
  have := congrFun (congrFun e i) j
  simp only [Matrix.map_apply] at this
  rw [Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  rw [← this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.cast_one h]

theorem Gamma_le_inf {N₁ N₂ : ℕ} (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) :
    CongruenceSubgroup.Gamma (N₁ * N₂) ≤ GammaH N₁ H₁ ⊓ GammaH N₂ H₂ :=
  le_inf ((Gamma_le_Gamma_of_dvd (dvd_mul_right N₁ N₂)).trans (Gamma_le_GammaH N₁ H₁))
    ((Gamma_le_Gamma_of_dvd (dvd_mul_left N₂ N₁)).trans (Gamma_le_GammaH N₂ H₂))

/-! ### Matrices over ℤ/N -/

theorem coe_redSL_eq_map {N : ℕ} (γ : SL(2, ℤ)) :
    ((redSL N γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) := by
  ext i j; simp

theorem det_map_intCast_zmod {N : ℕ} (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (m.map (Int.cast : ℤ → ZMod N)).det = ((m.det : ℤ) : ZMod N) := by
  simpa using (RingHom.map_det (Int.castRingHom (ZMod N)) m).symm

theorem map_mul_intCast_zmod {N : ℕ} (m m' : Matrix (Fin 2) (Fin 2) ℤ) :
    (m * m').map (Int.cast : ℤ → ZMod N) = m.map (Int.cast : ℤ → ZMod N) * m'.map (Int.cast : ℤ → ZMod N) :=
  Matrix.map_mul (f := Int.castRingHom (ZMod N))

theorem map_adjugate_intCast_zmod {N : ℕ} (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (adjugate m).map (Int.cast : ℤ → ZMod N) = adjugate (m.map (Int.cast : ℤ → ZMod N)) := by
  simpa using RingHom.map_adjugate (Int.castRingHom (ZMod N)) m

/-- For invertible g normalizing H, every element of H is a conjugate g h g⁻¹ (H is finite). -/
theorem normalizesMat_surj {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det) (hg : NormalizesMat H g) :
    ∀ k ∈ H, ∃ h ∈ H, g * (h : Matrix (Fin 2) (Fin 2) (ZMod N)) = (k : Matrix (Fin 2) (Fin 2) (ZMod N)) * g := by
  have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hu
  choose f hfH hf using hg
  let F : H → H := fun h => ⟨f h h.2, hfH h h.2⟩
  have hinj : Function.Injective F := by
    intro a b hab
    have e : g * (a : Matrix (Fin 2) (Fin 2) (ZMod N)) = g * (b : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
      rw [hf a a.2, hf b b.2]
      have := congrArg (fun x : H => ((x : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) hab
      simp only [F] at this
      rw [this]
    exact Subtype.ext (Subtype.ext (hgu.mul_right_injective e))
  intro k hk
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨k, hk⟩
  refine ⟨h, h.2, ?_⟩
  rw [hf h h.2]
  have := congrArg (fun x : H => ((x : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) hh
  simp only [F] at this
  rw [this]

theorem normalizesMat_adjugate {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det) (hg : NormalizesMat H g) :
    NormalizesMat H (adjugate g) := by
  intro k hk
  obtain ⟨h, hh, e⟩ := normalizesMat_surj hu hg k hk
  refine ⟨h, hh, ?_⟩
  -- adj g · (g h) · adj g = adj g · (k g) · adj g
  have e2 := congrArg (fun X => adjugate g * X * adjugate g) e
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul] at e2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate] at e2
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at e2
  have hdu : IsUnit g.det := hu
  obtain ⟨u, hu'⟩ := hdu
  have := congrArg (fun X => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) • X) e2
  simp only [smul_smul, ← hu', Units.inv_mul, one_smul] at this
  exact this.symm

/-- For g ∈ SL₂(ℤ/N), `NormalizesMat H g` means g ∈ N(H). -/
theorem normalizesMat_iff_mem_normH {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} (g : SL(2, ZMod N)) :
    NormalizesMat H (g : Matrix (Fin 2) (Fin 2) (ZMod N)) ↔ g ∈ NormH H := by
  constructor
  · intro hg
    have hu : IsUnit (g : Matrix (Fin 2) (Fin 2) (ZMod N)).det := by rw [g.2]; exact isUnit_one
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨h', hh', e⟩ := hg h hh
      have : g * h * g⁻¹ = h' := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, e, Matrix.mul_assoc,
          ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
          Matrix.mul_one]
      rw [this]; exact hh'
    · intro hk
      obtain ⟨h₀, hh₀, e⟩ := normalizesMat_surj hu hg _ hk
      have : h₀ = h := by
        have e' : g * h₀ = (g * h * g⁻¹) * g := Subtype.ext (by
          rw [Matrix.SpecialLinearGroup.coe_mul g h₀, e, ← Matrix.SpecialLinearGroup.coe_mul])
        have : g * h₀ = g * h := by rw [e']; group
        exact mul_left_cancel this
      rw [← this]; exact hh₀
  · intro hg h hh
    refine ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg h).1 hh, ?_⟩
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    simp

/-! ### §A without conditions on H₁ -/

section A

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- ⇒ of `mem_normG_inf_iff`: if (det m)^{-1/2}·m normalizes Γ, then m mod N₁ normalizes H₁. -/
theorem normalizesMat_of_mem_normG_inf (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hP : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) :
    NormalizesMat H₁ (m.map (Int.cast : ℤ → ZMod N₁)) := by
  intro h hh
  obtain ⟨γ, hγ, rfl⟩ := exists_mem_inf_redSL hcop H₁ H₂ hh
  obtain ⟨γ', hγ', e⟩ := exists_rel_left hdet hP hγ
  refine ⟨redSL N₁ γ', (Subgroup.mem_inf.1 hγ').1, ?_⟩
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X.map (Int.cast : ℤ → ZMod N₁)) e
  simp only [map_mul_intCast_zmod] at this
  rw [coe_redSL_eq_map, coe_redSL_eq_map]
  exact this

omit [NeZero N₁] [NeZero N₂] in
theorem isUnit_map_of_isUnit_det {m : Matrix (Fin 2) (Fin 2) ℤ} (hunit : IsUnit ((m.det : ℤ) : ZMod N₁)) :
    IsUnit (m.map (Int.cast : ℤ → ZMod N₁)) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_map_intCast_zmod]; exact hunit

omit [NeZero N₁] [NeZero N₂] in
/-- The conjugation step of ⇐ in `mem_normG_inf_iff`. -/
theorem conj_mem_inf_of_normalizesMat (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂)))
    (hn : NormalizesMat H₁ (m.map (Int.cast : ℤ → ZMod N₁))) {γ : SL(2, ℤ)}
    (hγ : γ ∈ GammaH N₁ H₁ ⊓ GammaH N₂ H₂) :
    projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈
      toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂) := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ))
  obtain ⟨hγ1, hγ2⟩ := Subgroup.mem_inf.1 hγ
  have h2 : P * ofZ γ * P⁻¹ ∈ toR (GammaH N₂ H₂) :=
    ((Subgroup.mem_normalizer_iff.1 hg) (ofZ γ)).1 (ofZ_mem_toR hγ2)
  obtain ⟨γ', hγ', he⟩ := mem_toR.1 h2
  have e : m * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * m := by
    apply (projSL_mul_ofZ_eq_iff hdet γ γ').1
    rw [he]
    show P * ofZ γ = P * ofZ γ * P⁻¹ * P
    group
  obtain ⟨h', hh', e'⟩ := hn (redSL N₁ γ) hγ1
  have e1 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => X.map (Int.cast : ℤ → ZMod N₁)) e
  simp only [map_mul_intCast_zmod] at e1
  rw [coe_redSL_eq_map] at e'
  rw [e'] at e1
  have hγ'1 : redSL N₁ γ' = h' := by
    apply Subtype.ext
    rw [coe_redSL_eq_map]
    exact ((isUnit_map_of_isUnit_det hunit).mul_left_injective e1).symm
  rw [← he]
  refine ofZ_mem_toR (Subgroup.mem_inf.2 ⟨?_, hγ'⟩)
  show redSL N₁ γ' ∈ H₁
  rw [hγ'1]; exact hh'

/-- ⇐ of `mem_normG_inf_iff`. -/
theorem mem_normG_inf_of_normalizesMat (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂)))
    (hn : NormalizesMat H₁ (m.map (Int.cast : ℤ → ZMod N₁))) :
    projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hPdef
  have hdet' : 0 < (adjugate m).det := by rwa [det_adjugate_two]
  have hunit' : IsUnit (((adjugate m).det : ℤ) : ZMod N₁) := by rwa [det_adjugate_two]
  have hg' := adjugate_mem_normG hdet hg
  have hn' : NormalizesMat H₁ ((adjugate m).map (Int.cast : ℤ → ZMod N₁)) := by
    rw [map_adjugate_intCast_zmod]
    exact normalizesMat_adjugate (by rw [det_map_intCast_zmod]; exact hunit) hn
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact conj_mem_inf_of_normalizesMat H₁ H₂ hdet hunit hg hn hγ
  · intro hY
    obtain ⟨δ, hδ, he⟩ := mem_toR.1 hY
    have := conj_mem_inf_of_normalizesMat H₁ H₂ hdet' hunit' hg' hn' hδ
    rw [projSL_adjugate hdet, ← hPdef, he, inv_inv] at this
    rwa [show P⁻¹ * (P * Y * P⁻¹) * P = Y by group] at this

theorem mem_normG_inf_iff' (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂))) :
    projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ↔
      NormalizesMat H₁ (m.map (Int.cast : ℤ → ZMod N₁)) :=
  ⟨normalizesMat_of_mem_normG_inf hcop H₁ H₂ hdet, mem_normG_inf_of_normalizesMat H₁ H₂ hdet hunit hg⟩

theorem ofZ_mem_normG_inf_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) {γ : SL(2, ℤ)} (hγ : γ ∈ GammaH N₂ H₂) :
    ofZ γ ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ↔ redSL N₁ γ ∈ NormH H₁ := by
  have hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; exact one_pos
  rw [show ofZ γ = projSL ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) from
    ofZ_eq_projSL (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) hd γ.2]
  rw [mem_normG_inf_iff' hcop H₁ H₂ hd (by rw [γ.2, Int.cast_one]; exact isUnit_one)
    (by rw [← ofZ_eq_projSL (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) hd γ.2]
        exact Subgroup.le_normalizer (ofZ_mem_toR hγ)),
    ← coe_redSL_eq_map, normalizesMat_iff_mem_normH]

theorem normG_inf_inf_eq' (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ⊓ toR (GammaH N₂ H₂) =
      toR (GammaH N₁ (NormH H₁) ⊓ GammaH N₂ H₂) := by
  ext Y
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hY, hY2⟩
    obtain ⟨γ, hγ, rfl⟩ := mem_toR.1 hY2
    exact ofZ_mem_toR (Subgroup.mem_inf.2 ⟨(ofZ_mem_normG_inf_iff hcop H₁ H₂ hγ).1 hY, hγ⟩)
  · intro hY
    obtain ⟨γ, hγ, rfl⟩ := mem_toR.1 hY
    obtain ⟨hγ1, hγ2⟩ := Subgroup.mem_inf.1 hγ
    exact ⟨(ofZ_mem_normG_inf_iff hcop H₁ H₂ hγ2).2 hγ1, ofZ_mem_toR hγ2⟩

theorem relIndex_inf_normG' (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)).relIndex
        (NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ⊓ toR (GammaH N₂ H₂)) =
      H₁.relIndex (NormH H₁) := by
  rw [normG_inf_inf_eq' hcop, relIndex_toR]
  have hle : GammaH N₁ (NormH H₁) ⊓ GammaH N₂ H₂ ≤ GammaH N₂ H₂ := inf_le_right
  rw [show GammaH N₁ H₁ ⊓ GammaH N₂ H₂ = GammaH N₁ H₁ ⊓ (GammaH N₁ (NormH H₁) ⊓ GammaH N₂ H₂) by
    rw [← inf_assoc, show GammaH N₁ H₁ ⊓ GammaH N₁ (NormH H₁) = GammaH N₁ H₁ from
      inf_eq_left.2 (GammaH_mono Subgroup.le_normalizer)]]
  rw [Subgroup.inf_relIndex_right, GammaH, Subgroup.relIndex_comap]
  congr 1
  apply le_antisymm
  · rintro _ ⟨γ, hγ, rfl⟩
    exact (Subgroup.mem_inf.1 hγ).1
  · intro g hg
    obtain ⟨γ, hγ, hγ1, -⟩ := exists_mem_GammaH_redSL hcop H₂ g
    exact ⟨γ, Subgroup.mem_inf.2 ⟨show redSL N₁ γ ∈ NormH H₁ by rw [hγ1]; exact hg, hγ⟩, hγ1⟩

theorem exists_mul_mem_normG_inf_iff' (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂))) :
    (∃ γ ∈ GammaH N₂ H₂,
        projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) ↔
      IsNormDet H₁ ((m.det : ℤ) : ZMod N₁) := by
  constructor
  · rintro ⟨γ, -, hmem⟩
    have hdγ : (m * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = m.det := by rw [det_mul, γ.2, mul_one]
    rw [← projSL_mul_ofZ hdet γ] at hmem
    refine ⟨(m * (γ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ZMod N₁), ?_,
      normalizesMat_of_mem_normG_inf hcop H₁ H₂ (hdγ ▸ hdet) hmem⟩
    rw [det_map_intCast_zmod, hdγ]
  · rintro ⟨g, hgdet, hgn⟩
    set mb := m.map (Int.cast : ℤ → ZMod N₁)
    have hmu : IsUnit mb.det := by rw [det_map_intCast_zmod]; exact hunit
    have hk : (mb⁻¹ * g).det = 1 := by
      rw [det_mul, det_nonsing_inv, hgdet, ← det_map_intCast_zmod]
      exact Ring.inverse_mul_cancel _ hmu
    obtain ⟨γ, hγ, hγ1, -⟩ := exists_mem_GammaH_redSL hcop H₂ ⟨mb⁻¹ * g, hk⟩
    have hdγ : (m * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = m.det := by rw [det_mul, γ.2, mul_one]
    have hmap : (m * (γ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ZMod N₁) = g := by
      rw [map_mul_intCast_zmod, ← coe_redSL_eq_map, hγ1]
      show mb * (mb⁻¹ * g) = g
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hmu, Matrix.one_mul]
    refine ⟨γ, hγ, ?_⟩
    rw [← projSL_mul_ofZ hdet γ]
    apply mem_normG_inf_of_normalizesMat H₁ H₂ (hdγ ▸ hdet) (by rw [hdγ]; exact hunit)
    · rw [projSL_mul_ofZ hdet γ]
      exact mul_mem hg (Subgroup.le_normalizer (ofZ_mem_toR hγ))
    · rw [hmap]; exact hgn

end A

end

end NormalizerLean
