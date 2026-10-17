module

public import NormalizerDelta.GenLocal

@[expose] public section

/-!
# General modular curves: §G, §Q, §S

* §G: under the local hypothesis every normalizer element projSL m (m primitive, det m ∣ N) has det m = 1:
  a prime p ∣ det m would make H mod p fix a line (Prop. 4.5(1), k = 1), or contradict Prop. 4.5(4) with
  k = v_p(N).  So Nor(Γ_H) ≤ SL₂(ℤ), and Nor(Γ_H) ∩ SL₂(ℤ) = Γ_{N(H)} (§R); the isomorphism is reduction mod N.
* §Q: as for Γ(N) (`XNGLQ.lean`), with surjectivity from `normG_level_form'`.
* §S: Γ_{±1} = ±Γ(N) and the order formula of the X(N) stage.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### §G -/

theorem det_eq_one_of_hloc {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det) (hDN : m.det ∣ N)
    (hprim : ∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H))) : m.det = 1 := by
  by_contra hD1
  have hD1' : m.det.natAbs ≠ 1 := by omega
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD1'
  have hpD' : (p : ℤ) ∣ m.det := Int.natCast_dvd.2 hpD
  have hpN : p ∣ N := Int.natCast_dvd_natCast.1 (hpD'.trans hDN)
  rcases hloc p hp hpN with hnb | hsp
  · apply hnb
    have := isBorelMod_of_dvd_det' hD hg hp (hprim p hp) (k := 1) (by rwa [pow_one])
    rwa [pow_one] at this
  · have := le_of_isSplitMod' hD hg hp (hprim p hp) (Nat.ordProj_dvd N p) hsp (e := 1) (by rwa [pow_one])
    omega

theorem ofZ_eq_projSL {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det) (hD1 : m.det = 1) :
    ofZ (⟨m, hD1⟩ : SL(2, ℤ)) = projSL (m.map (Int.cast : ℤ → ℝ)) := by
  apply Subtype.ext
  rw [coe_ofZ_eq_map (⟨m, hD1⟩ : SL(2, ℤ)), coe_projSL_int hD, hD1, Int.cast_one, Real.sqrt_one, inv_one,
    one_smul]

theorem normG_GammaH' {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    NormG (toR (GammaH N H)) = toR (GammaH N (NormH H)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨m, hD, hDN, hprim, rfl⟩ := normG_level_form' (Gamma_le_GammaH N H) hg
    have hD1 := det_eq_one_of_hloc hloc hD hDN hprim hg
    rw [← normG_GammaH_inf_SL2ZR']
    exact ⟨hg, (⟨m, hD1⟩ : SL(2, ℤ)), Subgroup.mem_top _, ofZ_eq_projSL hD hD1⟩
  · exact GammaH_normH_le_normG N H

theorem BG_GammaH_equiv' {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    ∃ φ : BG (toR (GammaH N H)) ≃* QH H,
      ∀ (γ : SL(2, ℤ)) (hγ : redSL N γ ∈ NormH H) (x : BG (toR (GammaH N H))),
        x.IsClassOf (ofZ γ) → φ x = QuotientGroup.mk ⟨redSL N γ, hγ⟩ := by
  have hN := normG_GammaH' hloc
  have hle : NormG (toR (GammaH N H)) ≤ (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)).range := by
    rw [hN, ← SL2ZR_eq_range]
    exact Subgroup.map_mono le_top
  have hred : ∀ g : NormG (toR (GammaH N H)), redOn hle N g ∈ NormH H := by
    rintro ⟨g, hg⟩
    have hg' := hg
    rw [hN] at hg'
    obtain ⟨γ, hγ, rfl⟩ := mem_toR.1 hg'
    rw [redOn_ofZ]; exact hγ
  set ψ := (QuotientGroup.mk' (H.subgroupOf (NormH H))).comp ((redOn hle N).codRestrict (NormH H) hred)
    with hψdef
  have hψ : ∀ γ hγ hγ', ψ ⟨ofZ γ, hγ⟩ = QuotientGroup.mk ⟨redSL N γ, hγ'⟩ := by
    intro γ hγ hγ'
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    congr 1
    apply Subtype.ext
    simp [MonoidHom.codRestrict_apply, redOn_ofZ]
  have hsurj : Function.Surjective ψ := by
    intro A
    obtain ⟨⟨B, hB⟩, rfl⟩ := QuotientGroup.mk'_surjective _ A
    obtain ⟨γ, rfl⟩ := redSL_surjective N B
    have hγ : ofZ γ ∈ NormG (toR (GammaH N H)) := (ofZ_mem_normG_GammaH_iff' N H γ).2 hB
    exact ⟨⟨ofZ γ, hγ⟩, hψ γ hγ hB⟩
  have hker : (toR (GammaH N H)).subgroupOf (NormG (toR (GammaH N H))) = ψ.ker := by
    ext ⟨g, hg⟩
    obtain ⟨γ, rfl⟩ := hle hg
    have hγ' : redSL N γ ∈ NormH H := (ofZ_mem_normG_GammaH_iff' N H γ).1 hg
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψ γ hg hγ', QuotientGroup.eq_one_iff]
    change ofZ γ ∈ toR _ ↔ _
    rw [ofZ_mem_toR_iff, Subgroup.mem_subgroupOf]
    rfl
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj), ?_⟩
  rintro γ hγ x ⟨hγ', rfl⟩
  exact hψ γ hγ' hγ

theorem card_BG_GammaH' {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    Nat.card (BG (toR (GammaH N H))) = H.relIndex (NormH H) := by
  show (toR (GammaH N H)).relIndex (NormG (toR (GammaH N H))) = _
  rw [normG_GammaH' hloc, relIndex_toR, relIndex_GammaH_GammaH_normH]

/-! ### §Q -/

/-- g ↦ normSL g, Nor_{GL₂⁺(ℚ)}(Γ) → Nor_{SL₂(ℝ)}(Γ). -/
def psiG (Γ : Subgroup SL(2, ℤ)) : NormGQ (Γ.map toGLPosQ) →* NormG (toR Γ) where
  toFun g := ⟨normSL g, mem_NormGQ_map_iff.1 g.2⟩
  map_one' := Subtype.ext normSL_one
  map_mul' x y := Subtype.ext (normSL_mul x y)

/-- Nor_{GL₂⁺(ℚ)}(Γ) → Nor(Γ)/Γ. -/
def phiG (Γ : Subgroup SL(2, ℤ)) : NormGQ (Γ.map toGLPosQ) →* BG (toR Γ) :=
  (QuotientGroup.mk' ((toR Γ).subgroupOf (NormG (toR Γ)))).comp (psiG Γ)

theorem phiG_surjective {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    Function.Surjective (phiG Γ) := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hD, -, -, rfl⟩ := normG_level_form' hΓ hg
  set W : Matrix (Fin 2) (Fin 2) ℚ := m.map (Int.cast : ℤ → ℚ) with hWdef
  have hWdet : W.det = (m.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) m
    simpa using this.symm
  have hWpos : 0 < W.det := by rw [hWdet]; exact_mod_cast hD
  let G : GLPos (Fin 2) ℚ := ⟨GeneralLinearGroup.mkOfDetNeZero W hWpos.ne', by
    rw [mem_glpos, GeneralLinearGroup.val_det_apply]; exact hWpos⟩
  have hGg : normSL G = projSL (m.map (Int.cast : ℤ → ℝ)) := by
    unfold normSL
    congr 1
  have hG : G ∈ NormGQ (Γ.map toGLPosQ) := mem_NormGQ_map_iff.2 (hGg ▸ hg)
  refine ⟨⟨G, hG⟩, ?_⟩
  show (QuotientGroup.mk (psiG Γ ⟨G, hG⟩) : BG (toR Γ)) = QuotientGroup.mk ⟨_, hg⟩
  congr 1

theorem BQ_equiv_BG' {N : ℕ} (hN0 : NeZero N) {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    ∃ φ : NormGQ (Γ.map toGLPosQ) →* BG (toR Γ), Function.Surjective φ ∧
      φ.ker = (Γ.map toGLPosQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (Γ.map toGLPosQ)) ∧
      ∀ g : NormGQ (Γ.map toGLPosQ), (φ g).IsClassOf (normSL g) := by
  refine ⟨phiG Γ, phiG_surjective hΓ, ?_, fun g => ⟨mem_NormGQ_map_iff.1 g.2, rfl⟩⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← normSL_mem_toR_iff hneg]
  show (QuotientGroup.mk (psiG Γ g) : BG (toR Γ)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

/-! ### §S -/

theorem GammaH_pmOneSL (N : ℕ) :
    GammaH N (pmOneSL N) = CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1) := by
  ext γ
  rw [mem_GammaH, mem_pmOneSL, mem_sup_pm_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      change redSL N (-γ) = 1
      rw [redSL_neg, h, neg_neg]
  · rintro (h | h)
    · exact Or.inl h
    · right
      have : redSL N (-γ) = 1 := h
      rw [redSL_neg, neg_eq_iff_eq_neg] at this
      exact this

theorem toR_GammaH_pmOneSL (N : ℕ) : toR (GammaH N (pmOneSL N)) = pmGammaR N := by
  rw [GammaH_pmOneSL, pmGammaR_eq]

theorem card_BG_GammaH_pmOne' :
    Nat.card (BG (toR (GammaH 37 (pmOneSL 37)))) = 25308 ∧
      Nat.card (BG (toR (GammaH 38 (pmOneSL 38)))) = 20520 ∧
      Nat.card (BG (toR (GammaH 39 (pmOneSL 39)))) = 26208 := by
  simp only [toR_GammaH_pmOneSL]
  have h37 := card_BG_pmGammaR' 37 (by norm_num)
  have h38 := card_BG_pmGammaR' 38 (by norm_num)
  have h39 := card_BG_pmGammaR' 39 (by norm_num)
  rw [Nat.Prime.primeFactors (by norm_num)] at h37
  rw [show (38 : ℕ) = 2 * 19 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)] at h38
  rw [show (39 : ℕ) = 3 * 13 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)] at h39
  norm_num at h37 h38 h39
  exact ⟨by exact_mod_cast h37, by exact_mod_cast h38, by exact_mod_cast h39⟩

end

end NormalizerLean
