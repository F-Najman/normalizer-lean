module

public import NormalizerDelta.B0
public import NormalizerDelta.XNOrder

@[expose] public section

/-!
# X(N): the modular automorphism group computed in GL₂⁺(ℚ)

The arguments of `B0.lean` for Γ₀(N), for any Γ ≤ SL₂(ℤ):
* X ∈ Γ ≤ GL₂⁺(ℚ) iff det X = 1 and normSL X ∈ Γ (`mem_map_toGLPosQ_iff`), so g normalizes Γ in GL₂⁺(ℚ) iff
  normSL g normalizes Γ in SL₂(ℝ) (`mem_NormGQ_map_iff`);
* normSL g = γ ∈ SL₂(ℤ) forces g = γ·q, q ∈ ℚ^× (`eq_mul_scalQ_of_normSL_eq`), so for −1 ∈ Γ:
  normSL g ∈ Γ iff g ∈ Γ·ℚ^× (`normSL_mem_toR_iff`).
For Γ(N): Nor = SL₂(ℤ)·ℚ^× (`normG_GammaR'`), and normSL g ∈ ±Γ(N) iff g ∈ Γ(N)·ℚ^× (−1 is a scalar).
-/

open Matrix MatrixGroups Pointwise

namespace NormalizerLean

noncomputable section

/-! ### General Γ ≤ SL₂(ℤ) -/

theorem mem_map_toGLPosQ_iff {Γ : Subgroup SL(2, ℤ)} {X : GLPos (Fin 2) ℚ} :
    X ∈ Γ.map toGLPosQ ↔ (matQ X).det = 1 ∧ normSL X ∈ toR Γ := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨det_toGLPosQ γ, by rw [normSL_toGLPosQ]; exact Subgroup.mem_map_of_mem _ hγ⟩
  · rintro ⟨hdet, γ, hγ, hXγ⟩
    refine ⟨γ, hγ, ?_⟩
    have hm := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) hXγ
    simp only [coe_normSL, hdet, Rat.cast_one, Real.sqrt_one, inv_one, one_smul] at hm
    apply Subtype.ext; apply Units.ext
    ext i j
    have := congrFun (congrFun hm i) j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      eq_intCast] at this
    have h2 : ((matQ (toGLPosQ γ) i j : ℚ) : ℝ) = ((matQ X i j : ℚ) : ℝ) := by
      rw [matQ_toGLPosQ, map_apply]; push_cast; exact this
    exact Rat.cast_injective h2

theorem mem_NormGQ_map_iff {Γ : Subgroup SL(2, ℤ)} {g : GLPos (Fin 2) ℚ} :
    g ∈ NormGQ (Γ.map toGLPosQ) ↔ normSL g ∈ NormG (toR Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg Y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have hX : toGLPosQ γ ∈ Γ.map toGLPosQ := ⟨γ, hγ, rfl⟩
      have h1 := (mem_map_toGLPosQ_iff.1 ((hg _).1 hX)).2
      rwa [normSL_mul, normSL_mul, normSL_inv, normSL_toGLPosQ] at h1
    · intro hY
      obtain ⟨γ, hγ, hγY⟩ := hY
      have hX : toGLPosQ γ ∈ Γ.map toGLPosQ := ⟨γ, hγ, rfl⟩
      have h2 : g⁻¹ * toGLPosQ γ * g ∈ Γ.map toGLPosQ := by
        apply (hg _).2
        rw [show g * (g⁻¹ * toGLPosQ γ * g) * g⁻¹ = toGLPosQ γ by group]
        exact hX
      have h3 := (mem_map_toGLPosQ_iff.1 h2).2
      rw [normSL_mul, normSL_mul, normSL_inv, normSL_toGLPosQ] at h3
      have hγY' : ofZ γ = normSL g * Y * (normSL g)⁻¹ := hγY
      rw [hγY'] at h3
      simpa [mul_assoc] using h3
  · intro hg X
    rw [mem_map_toGLPosQ_iff, mem_map_toGLPosQ_iff, det_conj, normSL_mul, normSL_mul, normSL_inv]
    exact and_congr_right fun _ => hg _

theorem eq_mul_scalQ_of_normSL_eq {g : GLPos (Fin 2) ℚ} {γ : SL(2, ℤ)} (hγg : ofZ γ = normSL g) :
    ∃ (q : ℚ) (hq : q ≠ 0), g = toGLPosQ γ * scalQ q hq := by
  have hd := det_matQ_pos g
  set s := Real.sqrt ((matQ g).det : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hm := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) hγg
  simp only [coe_normSL] at hm
  have hent : ∀ i j, ((matQ g i j : ℚ) : ℝ) = s * (γ i j : ℝ) := by
    intro i j
    have := congrFun (congrFun hm i) j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      eq_intCast, Matrix.smul_apply, smul_eq_mul] at this
    rw [← hsdef] at this
    field_simp at this
    linarith
  set q : ℚ := matQ g 0 0 * γ 1 1 - matQ g 0 1 * γ 1 0 with hqdef
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [det_fin_two] at this
  have hq : (q : ℝ) = s := by
    rw [hqdef]; push_cast; rw [hent 0 0, hent 0 1]
    have : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ℝ) = 1 := by exact_mod_cast hdetγ
    push_cast at this
    linear_combination s * this
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, Rat.cast_zero] at hq; exact hs.ne' hq.symm
  refine ⟨q, hq0, ?_⟩
  apply GLPos_ext
  rw [matQ_mul, matQ_toGLPosQ, matQ_scalQ]
  ext i j
  have h1 := hent i j
  rw [← hq] at h1
  have h2 : matQ g i j = q * γ i j := by exact_mod_cast h1
  simp [h2, mul_comm]

theorem normSL_mem_toR_iff {Γ : Subgroup SL(2, ℤ)} (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    {g : GLPos (Fin 2) ℚ} :
    normSL g ∈ toR Γ ↔ g ∈ Γ.map toGLPosQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by
  constructor
  · rintro ⟨γ, hγ, hγg⟩
    obtain ⟨q, hq0, rfl⟩ := eq_mul_scalQ_of_normSL_eq hγg
    exact Subgroup.mul_mem_sup ⟨γ, hγ, rfl⟩ (scalQ_mem_center hq0)
  · intro hg
    have : g ∈ (Γ.map toGLPosQ : Set (GLPos (Fin 2) ℚ)) *
        ((Subgroup.center (GLPos (Fin 2) ℚ) : Subgroup (GLPos (Fin 2) ℚ)) : Set (GLPos (Fin 2) ℚ)) := by
      rw [← Subgroup.mul_normal]; exact hg
    obtain ⟨y, hy, z, hz, rfl⟩ := this
    rw [normSL_mul]
    refine mul_mem (mem_map_toGLPosQ_iff.1 hy).2 ?_
    obtain ⟨c, hc0, hc⟩ := (mem_center_GLPos_iff' z).1 hz
    rcases normSL_of_smul hc0 hc with h | h <;> rw [h]
    · exact one_mem _
    · have h1 : ofZ (-1) = -1 := by rw [ofZ_neg]; simp
      rw [← h1]
      exact ofZ_mem_toR hneg

/-! ### Γ(N) -/

theorem toGLPosQ_neg_one_mem_center : toGLPosQ (-1) ∈ Subgroup.center (GLPos (Fin 2) ℚ) := by
  apply mem_center_of_smul (c := -1)
  rw [matQ_toGLPosQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg]

theorem GammaQ_sup_center (N : ℕ) :
    (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1)).map toGLPosQ ⊔
        Subgroup.center (GLPos (Fin 2) ℚ) = GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  show _ = (CongruenceSubgroup.Gamma N).map toGLPosQ ⊔ _
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left ?_) le_sup_right
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right toGLPosQ_neg_one_mem_center
  · exact sup_le_sup_right le_sup_left _

theorem normSL_mem_pmGammaR_iff {N : ℕ} {g : GLPos (Fin 2) ℚ} :
    normSL g ∈ pmGammaR N ↔ g ∈ GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by
  rw [pmGammaR_eq, normSL_mem_toR_iff (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)),
    GammaQ_sup_center]

theorem normGQ_GammaQ' (N : ℕ) [NeZero N] :
    NormGQ (GammaQ N) = SL2ZQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by
  ext g
  rw [GammaQ, mem_NormGQ_map_iff]
  change normSL g ∈ NormG (GammaR N) ↔ _
  rw [normG_GammaR' N, SL2ZR, normSL_mem_toR_iff (Subgroup.mem_top _)]
  rfl

theorem normSL_mem_normG_pmGammaR {N : ℕ} [NeZero N] (g : NormGQ (GammaQ N)) :
    normSL g ∈ NormG (pmGammaR N) := by
  have h : normSL g ∈ NormG (toR (CongruenceSubgroup.Gamma N)) :=
    (mem_NormGQ_map_iff (Γ := CongruenceSubgroup.Gamma N)).1 g.2
  exact normG_GammaR_le_normG_pmGammaR N h

/-- g ↦ normSL g, Nor_{GL₂⁺(ℚ)}(Γ(N)) → Nor_{SL₂(ℝ)}(±Γ(N)). -/
def psiQ (N : ℕ) [NeZero N] : NormGQ (GammaQ N) →* NormG (pmGammaR N) where
  toFun g := ⟨normSL g, normSL_mem_normG_pmGammaR g⟩
  map_one' := Subtype.ext normSL_one
  map_mul' x y := Subtype.ext (normSL_mul x y)

/-- Nor_{GL₂⁺(ℚ)}(Γ(N)) → Nor(±Γ(N))/±Γ(N). -/
def phiQ (N : ℕ) [NeZero N] : NormGQ (GammaQ N) →* BG (pmGammaR N) :=
  (QuotientGroup.mk' ((pmGammaR N).subgroupOf (NormG (pmGammaR N)))).comp (psiQ N)

theorem toGLPosQ_mem_NormGQ (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) : toGLPosQ γ ∈ NormGQ (GammaQ N) := by
  rw [GammaQ, mem_NormGQ_map_iff, normSL_toGLPosQ]
  exact SL2ZR_le_normG_GammaR N (ofZ_mem_toR (Subgroup.mem_top _))

theorem phiQ_toGLPosQ (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγ : toGLPosQ γ ∈ NormGQ (GammaQ N)) :
    (phiQ N ⟨toGLPosQ γ, hγ⟩).IsClassOf (ofZ γ) := by
  have hmem : ofZ γ ∈ NormG (pmGammaR N) := by
    rw [← normSL_toGLPosQ]; exact normSL_mem_normG_pmGammaR ⟨toGLPosQ γ, hγ⟩
  refine ⟨hmem, ?_⟩
  show (QuotientGroup.mk (psiQ N ⟨toGLPosQ γ, hγ⟩) : BG (pmGammaR N)) = QuotientGroup.mk ⟨ofZ γ, hmem⟩
  congr 1
  exact Subtype.ext (normSL_toGLPosQ γ)

theorem phiQ_surjective (N : ℕ) [NeZero N] : Function.Surjective (phiQ N) := by
  intro x
  obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hh' := hh
  rw [normG_pmGammaR' N, SL2ZR] at hh'
  obtain ⟨γ, -, rfl⟩ := mem_toR.1 hh'
  refine ⟨⟨toGLPosQ γ, toGLPosQ_mem_NormGQ N γ⟩, ?_⟩
  obtain ⟨hmem, he⟩ := phiQ_toGLPosQ N γ (toGLPosQ_mem_NormGQ N γ)
  rw [he]

theorem phiQ_ker (N : ℕ) [NeZero N] :
    (phiQ N).ker = (GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (GammaQ N)) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← normSL_mem_pmGammaR_iff]
  show (QuotientGroup.mk (psiQ N g) : BG (pmGammaR N)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem BQ_GammaQ_equiv_BG' (N : ℕ) [NeZero N] :
    ∃ φ : NormGQ (GammaQ N) →* BG (pmGammaR N), Function.Surjective φ ∧
      φ.ker = (GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (GammaQ N)) ∧
      ∀ g : NormGQ (GammaQ N), (φ g).IsClassOf (normSL g) :=
  ⟨phiQ N, phiQ_surjective N, phiQ_ker N, fun g => ⟨normSL_mem_normG_pmGammaR g, rfl⟩⟩

theorem BQ_GammaQ_equiv' (N : ℕ) [NeZero N] :
    ∃ φ : NormGQ (GammaQ N) →* SL(2, ZMod N) ⧸ pmOneSL N, Function.Surjective φ ∧
      φ.ker = (GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (GammaQ N)) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : toGLPosQ γ ∈ NormGQ (GammaQ N)),
        φ ⟨toGLPosQ γ, hγ⟩ = QuotientGroup.mk (redSL N γ) := by
  obtain ⟨e, he⟩ := BG_pmGammaR_equiv' N
  refine ⟨e.toMonoidHom.comp (phiQ N), e.surjective.comp (phiQ_surjective N), ?_, fun γ hγ => ?_⟩
  · ext g
    rw [MonoidHom.mem_ker, ← phiQ_ker, MonoidHom.mem_ker]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff e e.injective
  · exact he γ _ (phiQ_toGLPosQ N γ hγ)

end

end NormalizerLean
