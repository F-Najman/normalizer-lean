module

public import NormalizerDelta.CartanLevel

@[expose] public section

/-!
# §S: split Cartan curves

* Γ_sp(N) ⊇ Γ(N), and γ ↦ γ₀₀ mod N is a homomorphism Γ_sp(N) → (ℤ/N)ˣ, onto (lift diag(u, u⁻¹)), with kernel Γ(N);
  so [Γ_sp(N) : Γ(N)] = φ(N) and [SL₂(ℤ) : Γ_sp(N)] = N³∏(1 − 1/p²)/φ(N) = N²∏(1 + 1/p).
* D⁻¹ Γ_sp(N) D = Γ₀(N²) ([[a, b], [c, d]] ↦ [[a, b/N], [Nc, d]]), so |BG(Γ_sp(N))| = |B(N²)|.
* p ≥ 5: Γ_sp⁺(p) ≤ Nor(Γ_sp(p)), [Γ_sp⁺(p) : Γ_sp(p)] = 2 = |B(p²)|, hence equality.
* p ≥ 7: Γ_sp⁺(p) mod p fixes no line (diag(2, 1/2) and [[0, −1], [1, 0]]), so its normalizer lies in SL₂(ℤ)
  (`normG_level_le_SL2ZR'`); σ diag(2, 1/2) σ⁻¹ ∈ Γ_sp⁺(p) has trace 5/2 ≠ 0, so it is diag(α, 1/α) with α = 2 or 1/2,
  and σ is diagonal or antidiagonal mod p.
* p = 5: [[1, 1], [2, 3]] normalizes Γ_sp⁺(5) (`decide` on the residues).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Helpers -/

theorem mem_normG_of_SL {Γ : Subgroup SL(2, ℤ)} {σ : SL(2, ℤ)} (h1 : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ)
    (h2 : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) : ofZ σ ∈ NormG (toR Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨σ * γ * σ⁻¹, h1 γ hγ, by simp [map_mul, map_inv]⟩
  · rintro ⟨γ', hγ', hY⟩
    refine ⟨σ⁻¹ * γ' * σ, h2 γ' hγ', ?_⟩
    simp only [map_mul, map_inv] at hY ⊢
    rw [hY]
    group

theorem conj_mem_of_normG {Γ : Subgroup SL(2, ℤ)} {σ γ : SL(2, ℤ)} (hσ : ofZ σ ∈ NormG (toR Γ))
    (hγ : γ ∈ Γ) : σ * γ * σ⁻¹ ∈ Γ := by
  have h := (Subgroup.mem_normalizer_iff.1 hσ (ofZ γ)).1 (ofZ_mem_toR hγ)
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact ofZ_mem_toR_iff.1 h

theorem conj_trace (σ x : SL(2, ℤ)) :
    (σ * x * σ⁻¹) 0 0 + (σ * x * σ⁻¹) 1 1 = x 0 0 + x 1 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply σ
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rwa [det_fin_two] at this
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11]
  linear_combination (x 0 0 + x 1 1) * hdet

theorem card_BG_eq_one_of {Γ : Subgroup SL(2, ℝ)} (h : NormG Γ = Γ) : Nat.card (BG Γ) = 1 := by
  show Γ.relIndex (NormG Γ) = 1
  rw [Subgroup.relIndex_eq_one, h]

theorem relIndex_toR {H K : Subgroup SL(2, ℤ)} : (toR H).relIndex (toR K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective _ _ ofZ_injective

/-! ### The index of Γ_sp(N) -/

theorem Gamma_le_GammaSp (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaSp N := fun γ h => by
  obtain ⟨-, hb, hc, -⟩ := CongruenceSubgroup.Gamma_mem.1 h
  exact ⟨hb, hc⟩

theorem Gamma_le_GammaSpPlus (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaSpPlus N :=
  fun γ h => Or.inl (Gamma_le_GammaSp N h)

theorem GammaSp_le_GammaSpPlus (N : ℕ) : GammaSp N ≤ GammaSpPlus N := fun _ h => Or.inl h

theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have := congrArg (fun z : ℤ => (z : ZMod N)) γ.2
  simp only [det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at this
  exact this

/-- γ ↦ γ₀₀ mod N on Γ_sp(N). -/
def spMap (N : ℕ) : GammaSp N →* (ZMod N)ˣ where
  toFun γ := Units.mkOfMulEqOne (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)
    (by have h := det_mod (N := N) (γ : SL(2, ℤ)); rw [γ.2.1, zero_mul, sub_zero] at h; exact h)
  map_one' := by ext; simp
  map_mul' γ γ' := by
    ext
    simp only [Units.val_mkOfMulEqOne, Units.val_mul, Subgroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul,
      γ.2.1, zero_mul, add_zero]

theorem spMap_surjective (N : ℕ) [NeZero N] : Function.Surjective (spMap N) := by
  intro u
  let x : SL(2, ZMod N) := ⟨!![(u : ZMod N), 0; 0, ((u⁻¹ : (ZMod N)ˣ) : ZMod N)], by
    rw [det_fin_two_of]; simp⟩
  obtain ⟨γ, hγ⟩ := redSL_surjective N x
  have hent : ∀ i j, ((γ i j : ℤ) : ZMod N) = (x : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := by
    intro i j
    rw [← hγ]; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨⟨γ, by
    show ((γ 0 1 : ℤ) : ZMod N) = 0 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0
    rw [hent, hent]; simp [x]⟩, ?_⟩
  ext
  show ((γ 0 0 : ℤ) : ZMod N) = u
  rw [hent]; simp [x]

theorem spMap_ker (N : ℕ) : (spMap N).ker = (CongruenceSubgroup.Gamma N).subgroupOf (GammaSp N) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, CongruenceSubgroup.Gamma_mem]
  have hb := γ.2.1
  have hc := γ.2.2
  have h := det_mod (N := N) (γ : SL(2, ℤ))
  rw [hb, zero_mul, sub_zero] at h
  constructor
  · intro h1
    have ha : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = 1 := by
      have := congrArg Units.val h1; simpa [spMap] using this
    rw [ha, one_mul] at h
    exact ⟨ha, hb, hc, h⟩
  · rintro ⟨ha, -, -, -⟩
    ext; simpa [spMap] using ha

theorem relIndex_Gamma_GammaSp (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma N).relIndex (GammaSp N) = N.totient := by
  rw [Subgroup.relIndex, ← spMap_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (spMap_surjective N), Subgroup.card_top, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

theorem index_GammaSp' (N : ℕ) [NeZero N] :
    ((GammaSp N).index : ℚ) = N ^ 2 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  have h := Subgroup.relIndex_mul_index (Gamma_le_GammaSp N)
  rw [relIndex_Gamma_GammaSp] at h
  have h' : ((N.totient : ℕ) : ℚ) * ((GammaSp N).index : ℚ) =
      N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
    rw [← index_Gamma', ← h]; push_cast; ring
  rw [Nat.totient_eq_mul_prod_factors, prod_one_sub_inv_sq] at h'
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hP : ∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have h2 : (2 : ℚ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  apply mul_left_cancel₀ (mul_ne_zero hN hP)
  linear_combination h'

/-! ### X_sp(N) ≅ X₀(N²) -/

theorem conj_GammaSp' (N : ℕ) (hN : 0 < N) :
    (toR (GammaSp N)).map (MulAut.conj (projSL !![(N : ℝ), 0; 0, 1])⁻¹).toMonoidHom =
      Gamma0R (N ^ 2) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  ext Y
  constructor
  · rintro ⟨_, ⟨γ, ⟨hb, hc⟩, rfl⟩, rfl⟩
    obtain ⟨b', hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hb
    obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
    have hY := coe_conj_Dm_inv (M := N) hN (coe_ofZ γ)
    refine mem_Gamma0R_of_entries (γ 0 0) b' (N ^ 2 * c') (γ 1 1) ?_ (dvd_mul_right _ _)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [hY, hb', hc']
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · intro hY
    obtain ⟨a, b, c, d, hdet, ⟨c', rfl⟩, hYm⟩ := exists_entries_of_mem_Gamma0R hY
    have h : a * d - (N * b) * (N * c') = 1 := by push_cast at hdet; linear_combination hdet
    refine ⟨ofZ (mkSL a (N * b) (N * c') d h), ⟨mkSL a (N * b) (N * c') d h, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · show (((N * b : ℤ)) : ZMod N) = 0
      simp
    · show (((N * c' : ℤ)) : ZMod N) = 0
      simp
    · apply Subtype.ext
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [coe_conj_Dm_inv hN (coe_ofZ_mkSL h), hYm]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem card_BG_GammaSp' (N : ℕ) [NeZero N] :
    Nat.card (BG (toR (GammaSp N))) = Nat.card (B (N ^ 2)) := by
  rw [← card_BG_map_conj (toR (GammaSp N)) (projSL !![(N : ℝ), 0; 0, 1])⁻¹,
    conj_GammaSp' N (Nat.pos_of_ne_zero (NeZero.ne N))]

theorem card_B_sq_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.card (B (p ^ 2)) = 2 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [card_B_explicit', hp.factorization_pow, Finsupp.single_apply, Finsupp.single_apply,
    Nat.primeFactors_prime_pow two_ne_zero hp]
  have h2 : p ≠ 2 := by omega
  have h3 : p ≠ 3 := by omega
  rw [if_neg h2, if_neg h3]
  have : ({p} : Finset ℕ) \ {2, 3} = {p} := by
    ext q; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by tauto⟩
  rw [this]
  rfl

theorem card_BG_GammaSp_two_three' :
    Nat.card (BG (toR (GammaSp 2))) = 6 ∧ Nat.card (BG (toR (GammaSp 3))) = 12 := by
  constructor
  · rw [card_BG_GammaSp', card_B_explicit', Nat.prime_two.factorization_pow,
      Nat.primeFactors_prime_pow two_ne_zero Nat.prime_two]
    simp
    rfl
  · rw [card_BG_GammaSp', card_B_explicit', Nat.prime_three.factorization_pow,
      Nat.primeFactors_prime_pow two_ne_zero Nat.prime_three]
    simp
    rfl

theorem card_BG_GammaSp_prime' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.card (BG (toR (GammaSp p))) = 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [card_BG_GammaSp', card_B_sq_prime hp hp5]

/-! ### Nor(Γ_sp(p)) = Γ_sp⁺(p) -/

theorem GammaSpPlus_le_normG_GammaSp (N : ℕ) : toR (GammaSpPlus N) ≤ NormG (toR (GammaSp N)) := by
  apply toR_le_normG
  intro g hg γ hγ
  obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply g
  obtain ⟨hγb, hγc⟩ := hγ
  show (((g * γ * g⁻¹) 0 1 : ℤ) : ZMod N) = 0 ∧ (((g * γ * g⁻¹) 1 0 : ℤ) : ZMod N) = 0
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10,
    e11]
  push_cast
  rcases hg with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · simp [hb, hc, hγb, hγc]
  · simp [ha, hd, hγb, hγc]

/-- S = [[0, −1], [1, 0]]. -/
def matS : SL(2, ℤ) := mkSL 0 (-1) 1 0 (by ring)

theorem relIndex_GammaSp_GammaSpPlus {N : ℕ} (hN : 2 ≤ N) :
    (GammaSp N).relIndex (GammaSpPlus N) = 2 := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨matS, Or.inr ⟨by simp [matS, mkSL], by simp [matS, mkSL]⟩⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hdet := det_mod (N := N) (b : SL(2, ℤ))
  have eS : ∀ i j, ((b : SL(2, ℤ)) * matS) i j = (b : SL(2, ℤ)) i 1 * matS 1 j +
      (b : SL(2, ℤ)) i 0 * matS 0 j := by
    intro i j; simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hmem : ∀ x : SL(2, ℤ), x ∈ GammaSp N ↔ ((x 0 1 : ℤ) : ZMod N) = 0 ∧ ((x 1 0 : ℤ) : ZMod N) = 0 :=
    fun x => Iff.rfl
  rw [hmem, hmem, eS, eS]
  simp only [matS, mkSL]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, head_cons,
    mul_zero, mul_one, mul_neg, zero_add, add_zero, Int.cast_neg, neg_eq_zero]
  rcases b.2 with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · rw [hb, hc, mul_zero, sub_zero] at hdet
    have ha0 : (((b : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
    right; exact ⟨⟨hb, hc⟩, fun h => ha0 h.1⟩
  · rw [ha, hd, zero_mul, zero_sub] at hdet
    have hb0 : (((b : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) ≠ 0 := by
      intro h0; rw [h0, zero_mul, neg_zero] at hdet; exact zero_ne_one hdet
    left; exact ⟨⟨ha, hd⟩, fun h => hb0 h.1⟩

theorem normG_GammaSp' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormG (toR (GammaSp p)) = toR (GammaSpPlus p) := by
  have hle := GammaSpPlus_le_normG_GammaSp p
  have h1 : (toR (GammaSp p)).relIndex (NormG (toR (GammaSp p))) = 2 := card_BG_GammaSp_prime' hp hp5
  have h2 : (toR (GammaSp p)).relIndex (toR (GammaSpPlus p)) = 2 := by
    rw [relIndex_toR]; exact relIndex_GammaSp_GammaSpPlus hp.two_le
  have h3 := Subgroup.relIndex_mul_relIndex (toR (GammaSp p)) (toR (GammaSpPlus p))
    (NormG (toR (GammaSp p))) (Subgroup.map_mono (GammaSp_le_GammaSpPlus p)) hle
  rw [h1, h2] at h3
  have h4 : (toR (GammaSpPlus p)).relIndex (NormG (toR (GammaSp p))) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h4) hle

/-! ### Γ_sp⁺(p) is self-normalizing for p ≥ 7 -/

theorem zmod_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have := (ZMod.natCast_eq_zero_iff 2 p).1 this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem zmod_ne_zero_of_lt {p n : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  omega

/-- A lift of diag(2, 1/2) to SL₂(ℤ). -/
theorem exists_lift_diag {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    ∃ δ : SL(2, ℤ), ((δ 0 0 : ℤ) : ZMod p) = 2 ∧ ((δ 0 1 : ℤ) : ZMod p) = 0 ∧
      ((δ 1 0 : ℤ) : ZMod p) = 0 ∧ ((δ 1 1 : ℤ) : ZMod p) = 2⁻¹ := by
  have h2 := zmod_two_ne_zero hp
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let x : SL(2, ZMod p) := ⟨!![2, 0; 0, 2⁻¹], by rw [det_fin_two_of]; field_simp; ring⟩
  obtain ⟨δ, hδ⟩ := redSL_surjective p x
  have hent : ∀ i j, ((δ i j : ℤ) : ZMod p) = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) i j := by
    intro i j; rw [← hδ]; simp [Matrix.SpecialLinearGroup.map_apply_coe]
  exact ⟨δ, by rw [hent]; simp [x], by rw [hent]; simp [x], by rw [hent]; simp [x], by rw [hent]; simp [x]⟩

theorem redSL_apply {p : ℕ} (γ : SL(2, ℤ)) (i j : Fin 2) :
    ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) i j = ((γ i j : ℤ) : ZMod p) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem normG_GammaSpPlus' {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    NormG (toR (GammaSpPlus p)) = toR (GammaSpPlus p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 := zmod_two_ne_zero (p := p) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast zmod_ne_zero_of_lt (n := 3) (by norm_num) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := by exact_mod_cast zmod_ne_zero_of_lt (n := 5) (by norm_num) (by omega)
  obtain ⟨δ, d00, d01, d10, d11⟩ := exists_lift_diag (p := p) (by omega)
  have hδ : δ ∈ GammaSpPlus p := Or.inl ⟨d01, d10⟩
  have hS : matS ∈ GammaSpPlus p := Or.inr ⟨by simp [matS, mkSL], by simp [matS, mkSL]⟩
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  -- the normalizer lies in SL₂(ℤ)
  have hirr : ∀ q : ℕ, q.Prime → q ∣ p → ∀ v : Fin 2 → ZMod q, v ≠ 0 →
      ∃ γ ∈ GammaSpPlus p, ∀ c : ZMod q, (redSL q γ : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v ≠ c • v := by
    intro q hq hqp v hv
    obtain rfl := ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqp).symm
    by_cases hv0 : v 0 = 0
    · refine ⟨matS, hS, fun c hc => ?_⟩
      have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [hv0, h1])
      have := congrFun hc 0
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, redSL_apply, Pi.smul_apply,
        smul_eq_mul] at this
      simp [matS, mkSL, hv0] at this
      exact h1 this
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
  have hgSL := normG_level_le_SL2ZR' (N := p) inferInstance (Gamma_le_GammaSpPlus p) hirr hg
  obtain ⟨σ, -, rfl⟩ := hgSL
  refine ofZ_mem_toR ?_
  -- t = σ δ σ⁻¹ ∈ Γ_sp⁺(p)
  have ht := conj_mem_of_normG hg hδ
  set t := σ * δ * σ⁻¹ with htdef
  have htσ : t * σ = σ * δ := by rw [htdef]; group
  have htr := congrArg (fun z : ℤ => (z : ZMod p)) (conj_trace σ δ)
  simp only [Int.cast_add, d00, d11] at htr
  rw [← htdef] at htr
  have hdt := det_mod (N := p) t
  -- entries of t σ = σ δ mod p
  have E : ∀ i j, (((t * σ) i j : ℤ) : ZMod p) = (((σ * δ) i j : ℤ) : ZMod p) := by
    intro i j; rw [htσ]
  have E00 := E 0 0
  have E01 := E 0 1
  have E10 := E 1 0
  have E11 := E 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
    Int.cast_mul, d00, d01, d10, d11, mul_zero, zero_mul, add_zero, zero_add] at E00 E01 E10 E11
  have hinv : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  rcases ht with ⟨tb, tc⟩ | ⟨ta, td⟩
  · -- t diagonal: t₀₀ ∈ {2, 1/2}
    simp only [tb, tc, zero_mul, mul_zero, sub_zero, add_zero, zero_add] at hdt E00 E01 E10 E11
    have hα : ((t 0 0 : ℤ) : ZMod p) = 2 ∨ ((t 0 0 : ℤ) : ZMod p) = 2⁻¹ := by
      have : (((t 0 0 : ℤ) : ZMod p) - 2) * (((t 0 0 : ℤ) : ZMod p) - 2⁻¹) = 0 := by
        linear_combination (((t 0 0 : ℤ) : ZMod p)) * htr - hdt + hinv
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
    have h4 : (2 : ZMod p) - 2⁻¹ ≠ 0 := by
      intro h
      apply h3
      linear_combination (2 : ZMod p) * h + hinv
    rcases hα with hα | hα
    · -- σ diagonal
      have hβ : ((t 1 1 : ℤ) : ZMod p) = 2⁻¹ := by linear_combination htr - hα
      left
      constructor
      · have : (((σ 0 1 : ℤ) : ZMod p)) * (2 - 2⁻¹) = 0 := by
          rw [hα] at E01; linear_combination E01
        exact (mul_eq_zero.1 this).resolve_right h4
      · have : (((σ 1 0 : ℤ) : ZMod p)) * (2 - 2⁻¹) = 0 := by
          rw [hβ] at E10; linear_combination -E10
        exact (mul_eq_zero.1 this).resolve_right h4
    · -- σ antidiagonal
      have hβ : ((t 1 1 : ℤ) : ZMod p) = 2 := by linear_combination htr - hα
      right
      constructor
      · have : (((σ 0 0 : ℤ) : ZMod p)) * (2 - 2⁻¹) = 0 := by
          rw [hα] at E00; linear_combination -E00
        exact (mul_eq_zero.1 this).resolve_right h4
      · have : (((σ 1 1 : ℤ) : ZMod p)) * (2 - 2⁻¹) = 0 := by
          rw [hβ] at E11; linear_combination E11
        exact (mul_eq_zero.1 this).resolve_right h4
  · -- t antidiagonal: trace 0 = 2 + 1/2, impossible
    exfalso
    rw [ta, td] at htr
    apply h5
    linear_combination (-2 : ZMod p) * htr - hinv

theorem card_BG_GammaSpPlus' {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    Nat.card (BG (toR (GammaSpPlus p))) = 1 :=
  card_BG_eq_one_of (normG_GammaSpPlus' hp hp7)

/-! ### p = 5 -/

/-- [[1, 1], [2, 3]]. -/
def sigma5 : SL(2, ℤ) := mkSL 1 1 2 3 (by ring)

theorem sp5_conj_aux : ∀ a b c d : ZMod 5, ((b = 0 ∧ c = 0) ∨ (a = 0 ∧ d = 0)) → a * d - b * c = 1 →
    ((-a - c + b + d = 0 ∧ 6 * a + 9 * c - 4 * b - 6 * d = 0) ∨
      (3 * a + 3 * c - 2 * b - 2 * d = 0 ∧ -2 * a - 3 * c + 2 * b + 3 * d = 0)) := by
  decide

theorem sp5_conj_aux' : ∀ a b c d : ZMod 5, ((b = 0 ∧ c = 0) ∨ (a = 0 ∧ d = 0)) → a * d - b * c = 1 →
    ((3 * a - c + 9 * b - 3 * d = 0 ∧ -2 * a + c - 4 * b + 2 * d = 0) ∨
      (3 * a - c + 6 * b - 2 * d = 0 ∧ -2 * a + c - 6 * b + 3 * d = 0)) := by
  decide

theorem GammaSpPlus_five_lt' : toR (GammaSpPlus 5) < NormG (toR (GammaSpPlus 5)) := by
  refine lt_of_le_of_ne Subgroup.le_normalizer (fun h => ?_)
  have hmem : ofZ sigma5 ∈ NormG (toR (GammaSpPlus 5)) := by
    apply mem_normG_of_SL
    · intro γ hγ
      obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply sigma5
      have hd := det_mod (N := 5) γ
      have key := sp5_conj_aux _ _ _ _ hγ hd
      show (((((sigma5 * γ * sigma5⁻¹) 0 1 : ℤ)) : ZMod 5) = 0 ∧ _) ∨ _
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10,
        e11]
      simp only [sigma5, mkSL, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, head_cons]
      push_cast
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left; constructor
        · linear_combination k1
        · linear_combination k2
      · right; constructor
        · linear_combination k1
        · linear_combination k2
    · intro γ hγ
      obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply sigma5
      have hd := det_mod (N := 5) γ
      have key := sp5_conj_aux' _ _ _ _ hγ hd
      show (((((sigma5⁻¹ * γ * sigma5) 0 1 : ℤ)) : ZMod 5) = 0 ∧ _) ∨ _
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10,
        e11]
      simp only [sigma5, mkSL, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
        cons_val_fin_one, head_cons]
      push_cast
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left; constructor
        · linear_combination k1
        · linear_combination k2
      · right; constructor
        · linear_combination k1
        · linear_combination k2
  have hnot : ofZ sigma5 ∉ toR (GammaSpPlus 5) := by
    rw [ofZ_mem_toR_iff]
    rintro (⟨hb, -⟩ | ⟨ha, -⟩)
    · exact absurd hb (by simp [sigma5, mkSL]; decide)
    · exact absurd ha (by simp [sigma5, mkSL]; decide)
  exact hnot (h ▸ hmem)

end

end NormalizerLean
