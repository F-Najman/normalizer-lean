module

public import NormalizerDelta.MixedLe
public import NormalizerDelta.GenPrime

@[expose] public section

/-!
# Part 8: the order (§B, general H₂ and prime level)

|Nor(Γ)/Γ| = [Nor(Γ) : Nor(Γ) ∩ Γ_{H₂}] · [Nor(Γ) ∩ Γ_{H₂} : Γ].  The second factor is [N(H₁) : H₁]
(`relIndex_inf_normG'`).  The first is the number of classes of Nor(Γ_{H₂})/Γ_{H₂} that meet Nor(Γ), as
Nor(Γ) ≤ Nor(Γ_{H₂}) (`normG_inf_le'`), and by `exists_mul_mem_normG_inf_iff'` these are the classes with
`HasNormDet` (`card_subtype_eq_relIndex`, with the embedding `Subgroup.quotientSubgroupOfEmbeddingOfLE`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- The classes of t/H that meet s ≤ t are as many as the classes of s/H. -/
theorem card_subtype_eq_relIndex {α : Type*} [Group α] {H s t : Subgroup α} (h : s ≤ t)
    (P : t ⧸ H.subgroupOf t → Prop)
    (hP : ∀ x, P x ↔ ∃ g : s, x = QuotientGroup.mk (Subgroup.inclusion h g)) :
    Nat.card {x // P x} = H.relIndex s := by
  set f := Subgroup.quotientSubgroupOfEmbeddingOfLE H h
  have e : {x // P x} ≃ Set.range f := Equiv.subtypeEquivRight fun x => by
    rw [hP, Set.mem_range]
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨QuotientGroup.mk g, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨g, rfl⟩
  rw [Nat.card_congr e, Nat.card_range_of_injective f.injective]
  rfl

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

omit [NeZero N₁] [NeZero N₂] in
theorem isUnit_det_of_dvd (hcop : N₁.Coprime N₂) {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hd : m.det ∣ N₂) : IsUnit ((m.det : ℤ) : ZMod N₁) := by
  rw [isUnit_intCast_iff_coprime hdet.le]
  have : m.det.toNat ∣ N₂ := by
    have h := Int.natAbs_dvd_natAbs.2 hd
    rwa [Int.natAbs_natCast, show m.det.natAbs = m.det.toNat by omega] at h
  exact Nat.Coprime.coprime_dvd_left this hcop.symm

theorem isNormDet_one {N : ℕ} (H : Subgroup SL(2, ZMod N)) : IsNormDet H 1 :=
  ⟨1, Matrix.det_one, fun h hh => ⟨h, hh, by rw [Matrix.one_mul, Matrix.mul_one]⟩⟩

/-- For g = (det m)^{-1/2}·m ∈ Nor(Γ_{H₂}) with det m prime to N₁, `HasNormDet H₁ g` means det m mod N₁ ∈ Det(H₁). -/
theorem hasNormDet_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂))) :
    HasNormDet H₁ (projSL (m.map (Int.cast : ℤ → ℝ))) ↔ IsNormDet H₁ ((m.det : ℤ) : ZMod N₁) := by
  constructor
  · rintro ⟨m', hdet', he, hunit', hnd'⟩
    have hg' : projSL (m'.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂)) := he ▸ hg
    have h1 := (exists_mul_mem_normG_inf_iff' hcop H₁ H₂ hdet' hunit' hg').2 hnd'
    rw [← he] at h1
    exact (exists_mul_mem_normG_inf_iff' hcop H₁ H₂ hdet hunit hg).1 h1
  · intro h; exact ⟨m, hdet, rfl, hunit, h⟩

/-- The classes of Nor(Γ_{H₂})/Γ_{H₂} that meet Nor(Γ) are those with `HasNormDet`. -/
theorem hasNormDet_class_iff (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    (x : BG (toR (GammaH N₂ H₂))) :
    (∃ g, x.IsClassOf g ∧ HasNormDet H₁ g) ↔
      ∃ g : NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)),
        x = QuotientGroup.mk (Subgroup.inclusion (normG_inf_le' hcop H₂ hloc) g) := by
  have : NeZero (N₁ * N₂) := ⟨Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  constructor
  · rintro ⟨g, ⟨hg, rfl⟩, m, hdet, rfl, hunit, hnd⟩
    obtain ⟨γ, hγ, hmem⟩ := (exists_mul_mem_normG_inf_iff' hcop H₁ H₂ hdet hunit hg).2 hnd
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    show (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * (projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ) ∈ _
    rw [inv_mul_cancel_left]
    exact ofZ_mem_toR hγ
  · rintro ⟨g, rfl⟩
    refine ⟨g, ⟨normG_inf_le' hcop H₂ hloc g.2, rfl⟩, ?_⟩
    obtain ⟨m, hdet, -, hprim, he⟩ := normG_level_form' (Gamma_le_inf H₁ H₂) g.2
    have hg := g.2
    rw [he] at hg ⊢
    have hunit := isUnit_det_inf hcop H₂ hloc hdet (fun p hp _ => hprim p hp) hg
    refine ⟨m, hdet, rfl, hunit, (m.map (Int.cast : ℤ → ZMod N₁)), det_map_intCast_zmod m,
      normalizesMat_of_mem_normG_inf hcop H₁ H₂ hdet hg⟩

theorem card_BG_inf' (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) =
      H₁.relIndex (NormH H₁) *
        Nat.card {x : BG (toR (GammaH N₂ H₂)) // ∃ g, x.IsClassOf g ∧ HasNormDet H₁ g} := by
  set G := toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)
  set G₂ := toR (GammaH N₂ H₂)
  have hle := normG_inf_le' hcop H₂ hloc
  have hGle : G ≤ NormG G ⊓ G₂ := le_inf Subgroup.le_normalizer (Subgroup.map_mono inf_le_right)
  show G.relIndex (NormG G) = _
  rw [← Subgroup.relIndex_mul_relIndex G (NormG G ⊓ G₂) (NormG G) hGle inf_le_left,
    relIndex_inf_normG' hcop H₁ H₂, inf_comm, Subgroup.inf_relIndex_right,
    card_subtype_eq_relIndex hle _ (hasNormDet_class_iff hcop H₂ hloc)]

theorem card_BG_inf_of_isNormDet' (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)}
    (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    (hall : ∀ u : (ZMod N₁)ˣ, IsNormDet H₁ u) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) =
      H₁.relIndex (NormH H₁) * Nat.card (BG (toR (GammaH N₂ H₂))) := by
  rw [card_BG_inf' hcop H₂ hloc]
  congr 1
  apply Nat.card_congr
  refine Equiv.subtypeUnivEquiv fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hdet, hd, -, he⟩ := normG_level_form' (Gamma_le_GammaH N₂ H₂) g.2
  have hunit := isUnit_det_of_dvd hcop hdet hd
  exact ⟨g, ⟨g.2, rfl⟩, m, hdet, he, hunit, by simpa using hall hunit.unit⟩

theorem card_BG_inf_prime_unique' {p : ℕ} (hp : p.Prime) (hcop : N₁.Coprime p)
    {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ q : ℕ, q.Prime → q ∣ N₁ → ¬ IsBorelMod H₁ q ∨ IsSplitMod H₁ (q ^ N₁.factorization q))
    {H₂ : Subgroup SL(2, ZMod p)} (h : FixesUniqueLine H₂) (hd : IsNormDet H₁ (p : ZMod N₁)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH p H₂))) =
      2 * (H₁.relIndex (NormH H₁) * H₂.relIndex (NormH H₂)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [card_BG_inf' hcop H₂ hloc]
  have e : Nat.card {x : BG (toR (GammaH p H₂)) // ∃ g, x.IsClassOf g ∧ HasNormDet H₁ g} =
      Nat.card (BG (toR (GammaH p H₂))) := by
    apply Nat.card_congr
    refine Equiv.subtypeUnivEquiv fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hdet, hdp, -, he⟩ := normG_level_form' (Gamma_le_GammaH p H₂) g.2
    have hunit := isUnit_det_of_dvd hcop hdet hdp
    refine ⟨g, ⟨g.2, rfl⟩, m, hdet, he, hunit, ?_⟩
    have hdp' : m.det.toNat ∣ p := by
      have h := Int.natAbs_dvd_natAbs.2 hdp
      rwa [Int.natAbs_natCast, show m.det.natAbs = m.det.toNat by omega] at h
    rcases (Nat.dvd_prime hp).1 hdp' with h1 | h1
    · rw [show m.det = 1 by omega, Int.cast_one]; exact isNormDet_one H₁
    · rw [show m.det = p by omega, Int.cast_natCast]; exact hd
  rw [e, card_BG_GammaH_prime_unique' hp h]
  ring

theorem card_BG_inf_prime_unique_of_not' {p : ℕ} (hp : p.Prime) (hcop : N₁.Coprime p)
    {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ q : ℕ, q.Prime → q ∣ N₁ → ¬ IsBorelMod H₁ q ∨ IsSplitMod H₁ (q ^ N₁.factorization q))
    {H₂ : Subgroup SL(2, ZMod p)} (_h : FixesUniqueLine H₂) (hd : ¬ IsNormDet H₁ (p : ZMod N₁)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH p H₂))) = H₁.relIndex (NormH H₁) * H₂.relIndex (NormH H₂) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [card_BG_inf' hcop H₂ hloc]
  congr 1
  rw [← relIndex_normG_inf_SL2ZR' p H₂]
  apply card_subtype_eq_relIndex (inf_le_left : NormG (toR (GammaH p H₂)) ⊓ SL2ZR ≤ _)
  intro x
  constructor
  · rintro ⟨g, ⟨hg, rfl⟩, m', hdet', he', hunit', hnd'⟩
    obtain ⟨m, hdet, hdp, -, he⟩ := normG_level_form' (Gamma_le_GammaH p H₂) hg
    have hunit := isUnit_det_of_dvd hcop hdet hdp
    have hnd : IsNormDet H₁ ((m.det : ℤ) : ZMod N₁) := by
      rw [he] at hg
      exact (hasNormDet_iff hcop H₁ H₂ hdet hunit hg).1 (he ▸ ⟨m', hdet', he', hunit', hnd'⟩)
    have hdp' : m.det.toNat ∣ p := by
      have h := Int.natAbs_dvd_natAbs.2 hdp
      rwa [Int.natAbs_natCast, show m.det.natAbs = m.det.toNat by omega] at h
    have hm1 : m.det = 1 := by
      rcases (Nat.dvd_prime hp).1 hdp' with h1 | h1
      · omega
      · exfalso; apply hd
        rwa [show m.det = p by omega, Int.cast_natCast] at hnd
    have hS : g ∈ SL2ZR := by
      rw [he, ← ofZ_eq_projSL hdet hm1]
      exact ofZ_mem_toR (Subgroup.mem_top _)
    exact ⟨⟨g, ⟨hg, hS⟩⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨hg, hS⟩ := Subgroup.mem_inf.1 g.2
    obtain ⟨γ, -, hγ⟩ := mem_toR.1 hS
    have hd1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
    refine ⟨g, ⟨hg, rfl⟩, γ, by rw [hd1]; exact one_pos, ?_, by rw [hd1, Int.cast_one]; exact isUnit_one,
      by rw [hd1, Int.cast_one]; exact isNormDet_one H₁⟩
    rw [← hγ]
    exact ofZ_eq_projSL (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by rw [hd1]; exact one_pos) hd1

end

end NormalizerLean
