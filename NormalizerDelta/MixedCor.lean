module

public import NormalizerDelta.MixedDelta
public import NormalizerDelta.CartanNonsplit
public import NormalizerDelta.CartanSplit

@[expose] public section

/-!
# Part 8: corollaries (§C)

`card_BG_inf_of_isNormDet'` for H₁ = {1} (Γ(N₁)), for the image of Γ_ns⁺(p) (p ≥ 5) and for the image of
Γ_sp⁺(p) (p ≥ 7) mod p.  These are of type I, self-normalizing for Γ_ns⁺ and Γ_sp⁺ (Part 5), and Det(H₁) is
everything: {1} is normalized by all of GL₂, Γ_ns⁺(p) by the non-split Cartan subgroup (whose determinant is the
norm, onto F_p^×), and Γ_sp⁺(p) by diag(u, 1).
-/

open Matrix MatrixGroups Polynomial

namespace NormalizerLean

noncomputable section

-- As in `CartanNonsplit.lean`: in Mathlib v4.35.0-rc3 this instance breaks `ring` on negations in `ZMod p`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-! ### Generalities -/

theorem map_zmodCast_self {p : ℕ} (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M.map (ZMod.cast : ZMod p → ZMod p) = M := by
  ext i j; simp

/-- If Γ mod p fixes no line (in the form of Part 5), then ¬ `IsBorelMod` for its image mod p. -/
theorem not_isBorelMod_of_hirr {p : ℕ} [Fact p.Prime] {Γ : Subgroup SL(2, ℤ)}
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 →
      ∃ γ ∈ Γ, ∀ c : ZMod p, (redSL p γ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v ≠ c • v) :
    ¬ IsBorelMod (Γ.map (redSL p)) p := by
  rintro ⟨v, ⟨a, b, hab⟩, hfix⟩
  have hv : v ≠ 0 := by rintro rfl; simp at hab
  obtain ⟨γ, hγ, hne⟩ := hirr v hv
  obtain ⟨c, hc⟩ := hfix (redSL p γ) (Subgroup.mem_map_of_mem _ hγ)
  rw [map_zmodCast_self] at hc
  exact hne c hc

theorem relIndex_normH_map_eq_one {p : ℕ} [NeZero p] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma p ≤ Γ) (hn : NormG (toR Γ) = toR Γ) :
    (Γ.map (redSL p)).relIndex (NormH (Γ.map (redSL p))) = 1 := by
  rw [← relIndex_normG_inf_SL2ZR' p, GammaH_map' hΓ, hn]
  exact Subgroup.relIndex_eq_one.2 inf_le_left

theorem mem_map_redSL_iff {p : ℕ} [NeZero p] {Γ : Subgroup SL(2, ℤ)} {P : Matrix (Fin 2) (Fin 2) (ZMod p) → Prop}
    (hΓ : ∀ γ : SL(2, ℤ), γ ∈ Γ ↔ P ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)))
    (h : SL(2, ZMod p)) : h ∈ Γ.map (redSL p) ↔ P (h : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [coe_redSL_eq_map]; exact (hΓ γ).1 hγ
  · intro hP
    obtain ⟨γ, rfl⟩ := redSL_surjective p h
    exact ⟨γ, (hΓ γ).2 (by rwa [coe_redSL_eq_map] at hP), rfl⟩

/-! ### Γ(N₁) -/

theorem GammaH_bot (N : ℕ) : GammaH N ⊥ = CongruenceSubgroup.Gamma N := by
  ext γ
  rw [mem_GammaH, Subgroup.mem_bot, CongruenceSubgroup.Gamma_mem']

theorem hloc_bot (N : ℕ) [NeZero N] :
    ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod (⊥ : Subgroup SL(2, ZMod N)) p ∨
      IsSplitMod (⊥ : Subgroup SL(2, ZMod N)) (p ^ N.factorization p) := by
  intro p hp hpN
  right
  have hq : p ^ N.factorization p ∣ N := Nat.ordProj_dvd N p
  have hfix : ∀ v : Fin 2 → ZMod (p ^ N.factorization p), FixesLine (⊥ : Subgroup SL(2, ZMod N)) _ v := by
    intro v h hh
    rw [Subgroup.mem_bot] at hh
    subst hh
    refine ⟨1, ?_⟩
    have : ((1 : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map
        (ZMod.cast : ZMod N → ZMod (p ^ N.factorization p)) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.cast_one hq]
    rw [this, Matrix.one_mulVec, one_smul]
  exact ⟨![1, 0], ![0, 1], hfix _, hfix _, by simp⟩

theorem isNormDet_bot {N : ℕ} (u : ZMod N) : IsNormDet (⊥ : Subgroup SL(2, ZMod N)) u := by
  refine ⟨!![u, 0; 0, 1], by simp [det_fin_two_of], fun h hh => ⟨h, hh, ?_⟩⟩
  rw [Subgroup.mem_bot] at hh
  subst hh
  simp

theorem card_BG_Gamma_inf' {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (CongruenceSubgroup.Gamma N₁ ⊓ GammaH N₂ H₂))) =
      Nat.card SL(2, ZMod N₁) * Nat.card (BG (toR (GammaH N₂ H₂))) := by
  rw [← GammaH_bot, card_BG_inf_of_isNormDet' hcop H₂ (hloc_bot N₁) (fun u => isNormDet_bot _)]
  congr 1
  rw [show NormH (⊥ : Subgroup SL(2, ZMod N₁)) = ⊤ from Subgroup.normalizer_eq_top_iff.2 inferInstance,
    Subgroup.relIndex_top_right, Subgroup.index_bot]

/-! ### Γ_ns⁺(p) -/

theorem exists_sq_sub_mul_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ε : ZMod p} (hε : ε ≠ 0) (u : ZMod p) :
    ∃ a c : ZMod p, a ^ 2 - ε * c ^ 2 = u := by
  have hp_odd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := C (-ε) * X ^ 2 - C u
  have hg : degree g = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 (neg_ne_zero.2 hε)]; norm_num),
      degree_C_mul_X_pow 2 (neg_ne_zero.2 hε)]
    rfl
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    FiniteField.exists_root_sum_quadratic (degree_X_pow 2) hg (by rw [ZMod.card, hp_odd])
  refine ⟨a, b, ?_⟩
  simp only [f, g, eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hab
  linear_combination hab


/-! ### Matrices normalizing H through conjugation -/

theorem det_conj_adjugate {N : ℕ} {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det)
    (h : SL(2, ZMod N)) :
    (Ring.inverse g.det • (g * (h : Matrix (Fin 2) (Fin 2) (ZMod N)) * adjugate g)).det = 1 := by
  have e : (Ring.inverse g.det • (g * (h : Matrix (Fin 2) (Fin 2) (ZMod N)) * adjugate g)).det =
      (Ring.inverse g.det * g.det) ^ 2 := by
    rw [Matrix.det_smul, det_mul, det_mul, h.2, mul_one, det_adjugate]
    simp only [Fintype.card_fin]
    ring
  rw [e, Ring.inverse_mul_cancel _ hu, one_pow]

/-- (det g)⁻¹·g h adj g ∈ SL₂(ℤ/N). -/
def conjAdj {N : ℕ} {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det) (h : SL(2, ZMod N)) :
    SL(2, ZMod N) :=
  ⟨_, det_conj_adjugate hu h⟩

theorem coe_conjAdj {N : ℕ} {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det) (h : SL(2, ZMod N)) :
    (conjAdj hu h : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      Ring.inverse g.det • (g * (h : Matrix (Fin 2) (Fin 2) (ZMod N)) * adjugate g) := rfl

theorem mul_eq_conj_adjugate_mul {N : ℕ} {g : Matrix (Fin 2) (Fin 2) (ZMod N)} (hu : IsUnit g.det)
    (h : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    g * h = (Ring.inverse g.det • (g * h * adjugate g)) * g := by
  rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    Ring.inverse_mul_cancel _ hu, one_smul]

/-- g (of unit determinant) normalizes H if (det g)⁻¹·g h adj g ∈ H for every h ∈ H. -/
theorem normalizesMat_of_conj {N : ℕ} {H : Subgroup SL(2, ZMod N)} {g : Matrix (Fin 2) (Fin 2) (ZMod N)}
    (hu : IsUnit g.det) (hconj : ∀ h ∈ H, conjAdj hu h ∈ H) : NormalizesMat H g :=
  fun h hh => ⟨_, hconj h hh, mul_eq_conj_adjugate_mul hu _⟩

theorem entry_eta {N : ℕ} (M : Matrix (Fin 2) (Fin 2) (ZMod N)) : M = !![M 0 0, M 0 1; M 1 0, M 1 1] :=
  Matrix.eta_fin_two M

/-! ### Γ_ns⁺(p) -/

theorem mem_map_GammaNsPlus_iff {p : ℕ} [NeZero p] {ε : ZMod p} (h : SL(2, ZMod p)) :
    h ∈ (GammaNsPlus p ε).map (redSL p) ↔
      ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ∧
        (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = ε * (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0) ∨
      ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = -(h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ∧
        (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = -(ε * (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0)) :=
  mem_map_redSL_iff (P := fun M => (M 1 1 = M 0 0 ∧ M 0 1 = ε * M 1 0) ∨ (M 1 1 = -M 0 0 ∧ M 0 1 = -(ε * M 1 0)))
    (fun γ => by simp [GammaNsPlus]) h

theorem isNormDet_nsPlus {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) {u : ZMod p}
    (hu : u ≠ 0) : IsNormDet ((GammaNsPlus p ε).map (redSL p)) u := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hε0 : ε ≠ 0 := by rintro rfl; exact hε ⟨0, by ring⟩
  obtain ⟨a, c, hac⟩ := exists_sq_sub_mul_sq hp hε0 u
  set g : Matrix (Fin 2) (Fin 2) (ZMod p) := !![a, ε * c; c, a]
  have hg : g.det = u := by rw [det_fin_two_of, ← hac]; ring
  have hgu : IsUnit g.det := by rw [hg]; exact hu.isUnit
  refine ⟨g, hg, normalizesMat_of_conj hgu fun h hh => ?_⟩
  rw [mem_map_GammaNsPlus_iff] at hh ⊢
  rw [coe_conjAdj]
  simp only [g, adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  rw [entry_eta (h : Matrix (Fin 2) (Fin 2) (ZMod p))]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring
  · right
    constructor
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring

theorem hloc_nsPlus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    ∀ q : ℕ, q.Prime → q ∣ p → ¬ IsBorelMod ((GammaNsPlus p ε).map (redSL p)) q ∨
      IsSplitMod ((GammaNsPlus p ε).map (redSL p)) (q ^ p.factorization q) := by
  have : Fact p.Prime := ⟨hp⟩
  intro q hq hqp
  obtain rfl := ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqp)
  left
  apply not_isBorelMod_of_hirr
  intro v hv
  exact hirr_ns hp2 hε (GammaNs_le_GammaNsPlus ε) q hq dvd_rfl v hv

theorem card_BG_GammaNsPlus_inf' {p N₂ : ℕ} [NeZero N₂] (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p}
    (hε : ¬ IsSquare ε) (hcop : p.Coprime N₂) (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (GammaNsPlus p ε ⊓ GammaH N₂ H₂))) = Nat.card (BG (toR (GammaH N₂ H₂))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hΓ : CongruenceSubgroup.Gamma p ≤ GammaNsPlus p ε := (Gamma_le_GammaNs ε).trans (GammaNs_le_GammaNsPlus ε)
  rw [← GammaH_map' hΓ, card_BG_inf_of_isNormDet' hcop H₂ (hloc_nsPlus hp hp2 hε)
    (fun u => isNormDet_nsPlus hp2 hε u.ne_zero),
    relIndex_normH_map_eq_one hΓ (normG_GammaNsPlus' hp hp5 hε), one_mul]

/-! ### Γ_sp⁺(p) -/

theorem mem_map_GammaSpPlus_iff {p : ℕ} [NeZero p] (h : SL(2, ZMod p)) :
    h ∈ (GammaSpPlus p).map (redSL p) ↔
      ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0) ∨
      ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 0) :=
  mem_map_redSL_iff (P := fun M => (M 0 1 = 0 ∧ M 1 0 = 0) ∨ (M 0 0 = 0 ∧ M 1 1 = 0))
    (fun γ => by simp [GammaSpPlus]) h

theorem isNormDet_spPlus {p : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0) :
    IsNormDet ((GammaSpPlus p).map (redSL p)) u := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set g : Matrix (Fin 2) (Fin 2) (ZMod p) := !![u, 0; 0, 1]
  have hg : g.det = u := by rw [det_fin_two_of]; ring
  have hgu : IsUnit g.det := by rw [hg]; exact hu.isUnit
  refine ⟨g, hg, normalizesMat_of_conj hgu fun h hh => ?_⟩
  rw [mem_map_GammaSpPlus_iff] at hh ⊢
  rw [coe_conjAdj]
  simp only [g, adjugate_fin_two_of, Matrix.smul_apply, smul_eq_mul]
  rw [entry_eta (h : Matrix (Fin 2) (Fin 2) (ZMod p))]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring
  · right; constructor
    · rw [h1, h2]; ring
    · rw [h1, h2]; ring

/-- For primes p ≥ 5, Γ_sp⁺(p) mod p fixes no line (as in the proof of `normG_GammaSpPlus'`). -/
theorem hirr_spPlus {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) : ∀ v : Fin 2 → ZMod p, v ≠ 0 →
    ∃ γ ∈ GammaSpPlus p, ∀ c : ZMod p, (redSL p γ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v ≠ c • v := by
  have h2 := zmod_two_ne_zero (p := p) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast zmod_ne_zero_of_lt (n := 3) (by norm_num) (by omega)
  obtain ⟨δ, d00, d01, d10, d11⟩ := exists_lift_diag (p := p) (by omega)
  have hδ : δ ∈ GammaSpPlus p := Or.inl ⟨d01, d10⟩
  have hS : matS ∈ GammaSpPlus p := Or.inr ⟨by simp [matS, mkSL], by simp [matS, mkSL]⟩
  intro v hv
  by_cases hv0 : v 0 = 0
  · refine ⟨matS, hS, fun c hc => ?_⟩
    have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [hv0, h1])
    have := congrFun hc 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, redSL_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp [matS, mkSL, hv0, -neg_eq_zero] at this
    exact h1 (neg_eq_zero.1 this)
  by_cases hv1 : v 1 = 0
  · refine ⟨matS, hS, fun c hc => ?_⟩
    have := congrFun hc 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, redSL_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp [matS, mkSL, hv1] at this
    exact hv0 this
  · refine ⟨δ, hδ, fun c hc => ?_⟩
    have c0 := congrFun hc 0
    have c1 := congrFun hc 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, redSL_apply, d00, d01, d10, d11,
      Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, zero_add] at c0 c1
    have e0 : c = 2 := by
      have : (c - 2) * v 0 = 0 := by linear_combination -c0
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv0)
    have e1 : c = 2⁻¹ := by
      have : (c - 2⁻¹) * v 1 = 0 := by linear_combination -c1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv1)
    apply h3
    have : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
    rw [← e1, e0] at this
    linear_combination this

theorem card_BG_GammaSpPlus_inf' {p N₂ : ℕ} [NeZero N₂] (hp : p.Prime) (hp7 : 7 ≤ p) (hcop : p.Coprime N₂)
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (GammaSpPlus p ⊓ GammaH N₂ H₂))) = Nat.card (BG (toR (GammaH N₂ H₂))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hΓ : CongruenceSubgroup.Gamma p ≤ GammaSpPlus p := Gamma_le_GammaSpPlus p
  have hloc : ∀ q : ℕ, q.Prime → q ∣ p → ¬ IsBorelMod ((GammaSpPlus p).map (redSL p)) q ∨
      IsSplitMod ((GammaSpPlus p).map (redSL p)) (q ^ p.factorization q) := by
    intro q hq hqp
    obtain rfl := ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqp)
    exact Or.inl (not_isBorelMod_of_hirr (hirr_spPlus (by omega)))
  rw [← GammaH_map' hΓ, card_BG_inf_of_isNormDet' hcop H₂ hloc (fun u => isNormDet_spPlus u.ne_zero),
    relIndex_normH_map_eq_one hΓ (normG_GammaSpPlus' hp hp7), one_mul]

end

end NormalizerLean
