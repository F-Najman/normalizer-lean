module

public import NormalizerDelta.MixedCor
public import NormalizerLean.Local

@[expose] public section

/-!
# Part 8: sanity checks (§S), Q₈ ≤ SL₂(F₇)

* Q₈ = ⟨i, j⟩ is the explicit list `Q8list` of 8 matrices (`Q8mod7_eq`).
* Det(Q₈) is the set of non-zero squares (`isNormDet_Q8mod7_iff'`): no matrix of determinant 3, 5 or 6 conjugates i
  and j into Q₈ (`decide +kernel` over the 7⁴ matrices).
* Q₈ fixes no line of F₇², and |N(Q₈)| = 48 (`decide +kernel` over 4-tuples), so |Nor(Γ_{Q₈}(7))/Γ_{Q₈}(7)| = 6
  (Part 6, `card_BG_GammaH'`).
* With Γ₀(p) = Γ_{B(p)}, B(p) fixing exactly one line, `card_BG_inf_prime_unique'` and its negation give 12 for p = 2
  (2 = 3² mod 7) and 6 for p = 3.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- The eight elements of Q₈ ≤ SL₂(F₇): ±1, ±i, ±j, ±k with i = [[0, −1], [1, 0]], j = [[2, 3], [3, −2]], k = ij. -/
def Q8list : List (Matrix (Fin 2) (Fin 2) (ZMod 7)) :=
  [!![1, 0; 0, 1], !![6, 0; 0, 6], !![0, 6; 1, 0], !![0, 1; 6, 0], !![2, 3; 3, 5], !![5, 4; 4, 2],
    !![4, 2; 2, 3], !![3, 5; 5, 4]]

set_option maxRecDepth 100000 in
theorem Q8list_mul : ∀ A ∈ Q8list, ∀ B ∈ Q8list, A * B ∈ Q8list := by decide +kernel

set_option maxRecDepth 100000 in
theorem Q8list_adj : ∀ A ∈ Q8list, !![A 1 1, -A 0 1; -A 1 0, A 0 0] ∈ Q8list := by decide +kernel

theorem Q8list_det : ∀ A ∈ Q8list, A.det = 1 := by
  intro A hA
  simp only [Q8list, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [det_fin_two_of] <;> decide

/-- Q₈ as an explicit subgroup. -/
def Q8sub : Subgroup SL(2, ZMod 7) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list}
  one_mem' := by show (1 : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list; decide +kernel
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : SL(2, ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list
    rw [Matrix.SpecialLinearGroup.coe_mul]; exact Q8list_mul _ ha _ hb
  inv_mem' := fun {g} hg => by
    show ((g⁻¹ : SL(2, ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    exact Q8list_adj _ hg

theorem mem_Q8sub {g : SL(2, ZMod 7)} : g ∈ Q8sub ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list := Iff.rfl

def gi7 : SL(2, ZMod 7) := ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

def gj7 : SL(2, ZMod 7) := ⟨!![2, 3; 3, -2], by rw [Matrix.det_fin_two_of]; decide⟩

theorem Q8mod7_def : Q8mod7 = Subgroup.closure {gi7, gj7} := rfl

theorem Q8mod7_eq : Q8mod7 = Q8sub := by
  rw [Q8mod7_def]
  apply le_antisymm
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨by rw [SetLike.mem_coe, mem_Q8sub]; decide +kernel, by rw [SetLike.mem_coe, mem_Q8sub]; decide +kernel⟩
  · intro g hg
    rw [mem_Q8sub] at hg
    have hi : gi7 ∈ Subgroup.closure ({gi7, gj7} : Set SL(2, ZMod 7)) := Subgroup.subset_closure (by simp)
    have hj : gj7 ∈ Subgroup.closure ({gi7, gj7} : Set SL(2, ZMod 7)) := Subgroup.subset_closure (by simp)
    simp only [Q8list, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h
    · rw [show g = 1 from Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two])]
      exact one_mem _
    · rw [show g = gi7 * gi7 from Subtype.ext (by rw [h]; decide +kernel)]; exact mul_mem hi hi
    · rw [show g = gi7 from Subtype.ext (by rw [h]; decide +kernel)]; exact hi
    · rw [show g = gi7 * gi7 * gi7 from Subtype.ext (by rw [h]; decide +kernel)]
      exact mul_mem (mul_mem hi hi) hi
    · rw [show g = gj7 from Subtype.ext (by rw [h]; decide +kernel)]; exact hj
    · rw [show g = gi7 * gi7 * gj7 from Subtype.ext (by rw [h]; decide +kernel)]
      exact mul_mem (mul_mem hi hi) hj
    · rw [show g = gi7 * gj7 from Subtype.ext (by rw [h]; decide +kernel)]; exact mul_mem hi hj
    · rw [show g = gi7 * gi7 * gi7 * gj7 from Subtype.ext (by rw [h]; decide +kernel)]
      exact mul_mem (mul_mem (mul_mem hi hi) hi) hj

theorem mem_Q8mod7 {g : SL(2, ZMod 7)} : g ∈ Q8mod7 ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list := by
  rw [Q8mod7_eq, mem_Q8sub]

/-- `NormalizesMat Q₈ M` on the explicit list. -/
theorem normalizesMat_Q8mod7_iff (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) :
    NormalizesMat Q8mod7 M ↔ ∀ A ∈ Q8list, ∃ B ∈ Q8list, M * A = B * M := by
  constructor
  · intro hM A hA
    obtain ⟨h', hh', e⟩ := hM ⟨A, Q8list_det A hA⟩ (mem_Q8mod7.2 hA)
    exact ⟨h', mem_Q8mod7.1 hh', e⟩
  · intro hM h hh
    obtain ⟨B, hB, e⟩ := hM h (mem_Q8mod7.1 hh)
    exact ⟨⟨B, Q8list_det B hB⟩, mem_Q8mod7.2 hB, e⟩

/-! ### Det(Q₈) -/

theorem Q8_nonsq_aux : ∀ a b c d : ZMod 7, (a * d - b * c = 3 ∨ a * d - b * c = 5 ∨ a * d - b * c = 6) →
    ¬ ((∃ B ∈ Q8list, !![a, b; c, d] * !![0, 6; 1, 0] = B * !![a, b; c, d]) ∧
      (∃ B ∈ Q8list, !![a, b; c, d] * !![2, 3; 3, 5] = B * !![a, b; c, d])) := by
  decide +kernel

theorem nonsq_mod7_aux : ∀ u : ZMod 7, u ≠ 0 → (∀ r : ZMod 7, u ≠ r * r) → u = 3 ∨ u = 5 ∨ u = 6 := by
  decide

theorem isNormDet_Q8mod7_iff' {u : ZMod 7} (hu : u ≠ 0) : IsNormDet Q8mod7 u ↔ IsSquare u := by
  constructor
  · rintro ⟨g, hg, hn⟩
    by_contra hsq
    have hsq' : ∀ r : ZMod 7, u ≠ r * r := fun r h => hsq ⟨r, h⟩
    have h356 := nonsq_mod7_aux u hu hsq'
    rw [normalizesMat_Q8mod7_iff] at hn
    obtain ⟨B₁, hB₁, e₁⟩ := hn !![0, 6; 1, 0] (by decide +kernel)
    obtain ⟨B₂, hB₂, e₂⟩ := hn !![2, 3; 3, 5] (by decide +kernel)
    rw [Matrix.eta_fin_two g] at e₁ e₂
    rw [← hg, det_fin_two] at h356
    exact Q8_nonsq_aux _ _ _ _ h356 ⟨⟨B₁, hB₁, e₁⟩, ⟨B₂, hB₂, e₂⟩⟩
  · rintro ⟨r, rfl⟩
    rw [← sq]; exact isNormDet_sq _ r

/-! ### |Nor(Γ_{Q₈}(7))/Γ_{Q₈}(7)| = 6 -/

theorem Q8_noline_aux : ∀ v0 v1 c c' : ZMod 7, ¬ (v0 = 0 ∧ v1 = 0) →
    ¬ ((gi7 : Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ ![v0, v1] = c • ![v0, v1] ∧
      (gj7 : Matrix (Fin 2) (Fin 2) (ZMod 7)) *ᵥ ![v0, v1] = c' • ![v0, v1]) := by
  decide +kernel

theorem not_isBorelMod_Q8mod7 : ¬ IsBorelMod Q8mod7 7 := by
  rintro ⟨v, ⟨a, b, hab⟩, hfix⟩
  obtain ⟨c, hc⟩ := hfix gi7 (by rw [Q8mod7_def]; exact Subgroup.subset_closure (by simp))
  obtain ⟨c', hc'⟩ := hfix gj7 (by rw [Q8mod7_def]; exact Subgroup.subset_closure (by simp))
  rw [map_zmodCast_self] at hc hc'
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv] at hc hc' hab
  apply Q8_noline_aux (v 0) (v 1) c c'
  · rintro ⟨h0, h1⟩; simp [h0, h1] at hab; exact absurd hab (by decide)
  · exact ⟨hc, hc'⟩

/-- SL₂(F₇) as 4-tuples. -/
def sl7Equiv : SL(2, ZMod 7) ≃ {x : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 // x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1} where
  toFun g := ⟨(g 0 0, g 0 1, g 1 0, g 1 1), by rw [← det_fin_two]; exact g.2⟩
  invFun x := ⟨!![x.1.1, x.1.2.1; x.1.2.2.1, x.1.2.2.2], by rw [det_fin_two_of]; exact x.2⟩
  left_inv g := Subtype.ext (Matrix.eta_fin_two _).symm
  right_inv x := rfl

theorem card_normH_aux :
    ((Finset.univ : Finset (ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7)).filter (fun x =>
      x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1 ∧
      ∀ A ∈ Q8list, ∃ B ∈ Q8list, !![x.1, x.2.1; x.2.2.1, x.2.2.2] * A = B * !![x.1, x.2.1; x.2.2.1, x.2.2.2])).card
      = 48 := by
  decide +kernel

theorem card_Q8_aux :
    ((Finset.univ : Finset (ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7)).filter (fun x =>
      x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1 ∧ !![x.1, x.2.1; x.2.2.1, x.2.2.2] ∈ Q8list)).card = 8 := by
  decide +kernel

theorem card_subgroup_eq_filter {H : Subgroup SL(2, ZMod 7)} (P : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 → Prop)
    [DecidablePred P]
    (hP : ∀ g : SL(2, ZMod 7), g ∈ H ↔ P ((sl7Equiv g).1)) :
    Nat.card H = ((Finset.univ : Finset (ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7)).filter (fun x =>
      x.1 * x.2.2.2 - x.2.1 * x.2.2.1 = 1 ∧ P x)).card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine ((Equiv.subtypeEquiv (p := fun g => g ∈ H) (q := fun y => P y.1) sl7Equiv (fun g => hP g)).trans ?_)
  exact {
    toFun := fun y => ⟨y.1.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, y.1.2, y.2⟩⟩
    invFun := fun z => ⟨⟨z.1, (Finset.mem_filter.1 z.2).2.1⟩, (Finset.mem_filter.1 z.2).2.2⟩
    left_inv := fun y => rfl
    right_inv := fun z => rfl }

theorem card_Q8mod7 : Nat.card Q8mod7 = 8 := by
  rw [card_subgroup_eq_filter (fun x => !![x.1, x.2.1; x.2.2.1, x.2.2.2] ∈ Q8list), card_Q8_aux]
  intro g
  rw [mem_Q8mod7]
  show _ ↔ (sl7Equiv.symm (sl7Equiv g) : Matrix (Fin 2) (Fin 2) (ZMod 7)) ∈ Q8list
  rw [Equiv.symm_apply_apply]

theorem card_normH_Q8mod7 : Nat.card (NormH Q8mod7) = 48 := by
  rw [card_subgroup_eq_filter (fun x => ∀ A ∈ Q8list, ∃ B ∈ Q8list,
      !![x.1, x.2.1; x.2.2.1, x.2.2.2] * A = B * !![x.1, x.2.1; x.2.2.1, x.2.2.2]), card_normH_aux]
  intro g
  rw [← normalizesMat_iff_mem_normH, normalizesMat_Q8mod7_iff]
  show _ ↔ ∀ A ∈ Q8list, ∃ B ∈ Q8list, (sl7Equiv.symm (sl7Equiv g) : Matrix (Fin 2) (Fin 2) (ZMod 7)) * A =
    B * (sl7Equiv.symm (sl7Equiv g) : Matrix (Fin 2) (Fin 2) (ZMod 7))
  rw [Equiv.symm_apply_apply]

theorem relIndex_normH_Q8mod7 : Q8mod7.relIndex (NormH Q8mod7) = 6 := by
  have h := Subgroup.card_mul_index (Q8mod7.subgroupOf (NormH Q8mod7))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv, card_Q8mod7,
    card_normH_Q8mod7] at h
  rw [Subgroup.relIndex]
  omega

theorem hloc_Q8mod7 : ∀ p : ℕ, p.Prime → p ∣ 7 → ¬ IsBorelMod Q8mod7 p ∨
    IsSplitMod Q8mod7 (p ^ (7 : ℕ).factorization p) := by
  intro p hp hp7
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hp7
  exact Or.inl not_isBorelMod_Q8mod7

theorem card_BG_Q8mod7' : Nat.card (BG (toR (GammaH 7 Q8mod7))) = 6 := by
  rw [card_BG_GammaH' hloc_Q8mod7, relIndex_normH_Q8mod7]

/-! ### With Γ₀(2) and Γ₀(3) -/

theorem Gamma_le_Gamma0 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N := fun γ hγ => by
  obtain ⟨-, -, h10, -⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  exact CongruenceSubgroup.Gamma0_mem.2 h10

theorem fixesUniqueLine_Gamma0 {p : ℕ} (hp : p.Prime) :
    FixesUniqueLine ((CongruenceSubgroup.Gamma0 p).map (redSL p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hB : FixesLine ((CongruenceSubgroup.Gamma0 p).map (redSL p)) p ![1, 0] := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨((γ 0 0 : ℤ) : ZMod p), ?_⟩
    rw [map_zmodCast_self, coe_redSL_eq_map]
    have h10 := CongruenceSubgroup.Gamma0_mem.1 hγ
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10]
  refine ⟨![1, 0], by simp, hB, (fixesUniqueLine_iff' hp hB).2 ?_⟩
  rw [GammaH_map' (Gamma_le_Gamma0 p)]
  exact CongruenceSubgroup.Gamma1_in_Gamma0 p

theorem relIndex_normH_Gamma0_of_card {p : ℕ} (hp : p.Prime)
    (h2 : Nat.card (BG (toR (CongruenceSubgroup.Gamma0 p))) = 2) :
    ((CongruenceSubgroup.Gamma0 p).map (redSL p)).relIndex (NormH ((CongruenceSubgroup.Gamma0 p).map (redSL p))) = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 := card_BG_GammaH_prime_unique' hp (fixesUniqueLine_Gamma0 hp)
  rw [GammaH_map' (Gamma_le_Gamma0 p), h2] at h1
  omega

theorem card_BG_Gamma0_two : Nat.card (BG (toR (CongruenceSubgroup.Gamma0 2))) = 2 := by
  have := card_B_prime_pow Nat.prime_two one_pos
  simp [f₂] at this
  exact this

theorem card_BG_Gamma0_three : Nat.card (BG (toR (CongruenceSubgroup.Gamma0 3))) = 2 := by
  have := card_B_prime_pow Nat.prime_three one_pos
  simp [f₃] at this
  exact this

theorem card_BG_Q8mod7_inf_two' :
    Nat.card (BG (toR (GammaH 7 Q8mod7 ⊓ CongruenceSubgroup.Gamma0 2))) = 12 := by
  rw [← GammaH_map' (Gamma_le_Gamma0 2),
    card_BG_inf_prime_unique' Nat.prime_two (by norm_num) hloc_Q8mod7 (fixesUniqueLine_Gamma0 Nat.prime_two)
      ((isNormDet_Q8mod7_iff' (by decide)).2 ⟨3, by decide⟩),
    relIndex_normH_Q8mod7, relIndex_normH_Gamma0_of_card Nat.prime_two card_BG_Gamma0_two]

theorem card_BG_Q8mod7_inf_three' :
    Nat.card (BG (toR (GammaH 7 Q8mod7 ⊓ CongruenceSubgroup.Gamma0 3))) = 6 := by
  rw [← GammaH_map' (Gamma_le_Gamma0 3),
    card_BG_inf_prime_unique_of_not' Nat.prime_three (by norm_num) hloc_Q8mod7
      (fixesUniqueLine_Gamma0 Nat.prime_three)
      (fun h => by
        obtain ⟨r, hr⟩ := (isNormDet_Q8mod7_iff' (by decide)).1 h
        revert r; decide),
    relIndex_normH_Q8mod7, relIndex_normH_Gamma0_of_card Nat.prime_three card_BG_Gamma0_three]

end

end NormalizerLean
