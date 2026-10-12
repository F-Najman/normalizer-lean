import NormalizerDelta.GammaN
import NormalizerDelta.SL2Surj

/-!
# §G: Nor(Γ(N))/Γ(N) ≅ SL₂(ℤ/N) and Nor(±Γ(N))/±Γ(N) ≅ SL₂(ℤ/N)/{±1}

Both normalizers are SL₂(ℤ) (`normG_GammaR'`, `normG_pmGammaR'`).  Reduction mod N, read through the
inverse of SL₂(ℤ) ≅ SL₂(ℤ) ≤ SL₂(ℝ), is onto SL₂(ℤ/N) (`redSL_surjective`) with kernel Γ(N), and onto
SL₂(ℤ/N)/{±1} with kernel ±Γ(N) (γ mod N = ±1 iff γ or −γ lies in Γ(N)).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem SL2ZR_eq_range : SL2ZR = (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range := by
  rw [SL2ZR, toR, MonoidHom.range_eq_map]

/-- The integer matrix of an element of SL₂(ℤ) ≤ SL₂(ℝ). -/
def toZ : (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range ≃* SL(2, ℤ) :=
  (MonoidHom.ofInjective ofZ_injective).symm

theorem toZ_ofZ (γ : SL(2, ℤ)) (h) : toZ ⟨ofZ γ, h⟩ = γ := by
  rw [toZ, MulEquiv.symm_apply_eq]
  rfl

theorem ofZ_mem_toR_iff {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} : ofZ γ ∈ toR Γ ↔ γ ∈ Γ :=
  Subgroup.mem_map_iff_mem ofZ_injective

/-- Reduction mod N on a subgroup of SL₂(ℤ) ≤ SL₂(ℝ). -/
def redOn {H : Subgroup SL(2, ℝ)} (h : H ≤ (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range)
    (N : ℕ) : H →* SL(2, ZMod N) :=
  (redSL N).comp (toZ.toMonoidHom.comp (Subgroup.inclusion h))

theorem redOn_ofZ {H : Subgroup SL(2, ℝ)}
    (h : H ≤ (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range) (N : ℕ)
    (γ : SL(2, ℤ)) (hγ : ofZ γ ∈ H) : redOn h N ⟨ofZ γ, hγ⟩ = redSL N γ := by
  simp only [redOn, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1
  exact toZ_ofZ γ _

theorem mem_pmOneSL {N : ℕ} {x : SL(2, ZMod N)} : x ∈ pmOneSL N ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rcases Int.even_or_odd k with hk | hk
    · left; exact hk.neg_one_zpow
    · right; exact hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem redSL_neg (N : ℕ) (γ : SL(2, ℤ)) : redSL N (-γ) = -redSL N γ := by
  ext i j; simp [SpecialLinearGroup.coe_neg]

theorem BG_GammaR_equiv' (N : ℕ) [NeZero N] :
    ∃ φ : BG (GammaR N) ≃* SL(2, ZMod N),
      ∀ (γ : SL(2, ℤ)) (x : BG (GammaR N)), x.IsClassOf (ofZ γ) → φ x = redSL N γ := by
  have hle : NormG (GammaR N) ≤ (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range := by
    rw [normG_GammaR', SL2ZR_eq_range]
  have hmem : ∀ γ : SL(2, ℤ), ofZ γ ∈ NormG (GammaR N) := fun γ => by
    rw [normG_GammaR']; exact ofZ_mem_toR (Subgroup.mem_top γ)
  set ψ := redOn hle N
  have hsurj : Function.Surjective ψ := by
    intro A
    obtain ⟨γ, rfl⟩ := redSL_surjective N A
    exact ⟨⟨ofZ γ, hmem γ⟩, redOn_ofZ hle N γ _⟩
  have hker : (GammaR N).subgroupOf (NormG (GammaR N)) = ψ.ker := by
    ext ⟨g, hg⟩
    obtain ⟨γ, rfl⟩ := hle hg
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change ofZ γ ∈ toR _ ↔ redOn hle N ⟨ofZ γ, hg⟩ = 1
    rw [redOn_ofZ, ofZ_mem_toR_iff]
    rfl
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), ?_⟩
  rintro γ x ⟨hγ, rfl⟩
  exact redOn_ofZ hle N γ hγ

theorem BG_pmGammaR_equiv' (N : ℕ) [NeZero N] :
    ∃ φ : BG (pmGammaR N) ≃* SL(2, ZMod N) ⧸ pmOneSL N,
      ∀ (γ : SL(2, ℤ)) (x : BG (pmGammaR N)), x.IsClassOf (ofZ γ) →
        φ x = QuotientGroup.mk (redSL N γ) := by
  have hle : NormG (pmGammaR N) ≤ (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range := by
    rw [normG_pmGammaR', SL2ZR_eq_range]
  have hmem : ∀ γ : SL(2, ℤ), ofZ γ ∈ NormG (pmGammaR N) := fun γ => by
    rw [normG_pmGammaR']; exact ofZ_mem_toR (Subgroup.mem_top γ)
  set ψ := (QuotientGroup.mk' (pmOneSL N)).comp (redOn hle N)
  have hψ : ∀ γ hγ, ψ ⟨ofZ γ, hγ⟩ = QuotientGroup.mk (redSL N γ) := fun γ hγ => by
    simp only [ψ, MonoidHom.comp_apply, redOn_ofZ, QuotientGroup.mk'_apply]
  have hsurj : Function.Surjective ψ := by
    intro A
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (pmOneSL N) A
    obtain ⟨γ, rfl⟩ := redSL_surjective N B
    exact ⟨⟨ofZ γ, hmem γ⟩, hψ γ _⟩
  have hker : (pmGammaR N).subgroupOf (NormG (pmGammaR N)) = ψ.ker := by
    ext ⟨g, hg⟩
    obtain ⟨γ, rfl⟩ := hle hg
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψ, QuotientGroup.eq_one_iff, mem_pmOneSL]
    change ofZ γ ∈ pmGammaR N ↔ _
    rw [pmGammaR_eq, ofZ_mem_toR_iff, mem_sup_pm_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have : redSL N (-γ) = 1 := h
        rw [redSL_neg, neg_eq_iff_eq_neg] at this
        exact this
    · rintro (h | h)
      · exact Or.inl h
      · right
        change redSL N (-γ) = 1
        rw [redSL_neg, h, neg_neg]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), ?_⟩
  rintro γ x ⟨hγ, rfl⟩
  exact hψ γ hγ

end

end NormalizerLean
