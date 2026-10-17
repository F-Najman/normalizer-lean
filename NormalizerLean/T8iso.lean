module

public import NormalizerLean.Local
public import NormalizerLean.T8cd

@[expose] public section

/-!
# T8(c, d), isomorphisms: the completed λ = 5, 6 presentations present B(32), B(64), and Bars's
λ = 8 presentation presents B(256)

Same scheme as T5: w ↦ [w_m], s ↦ [S_{h(m)}] is well defined (the relators are evaluated as
explicit matrices, computed in sympy), onto by T4, and the orders agree (T8(c, d) and T3).
For m = 32 the Fricke element is irrational; (ws)⁴ = (wsw)s(wsw)s and w s⁻¹ w = r are rational.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open Words

/-- w s w ↦ [[−1, 0], [m/k, −1]] for w the Fricke element. -/
theorem coe_fricke_S_fricke (m k : ℕ) (hm : m ≠ 0) (hk : k ≠ 0) :
    ((fricke m hm * S k * fricke m hm : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1, 0; (m : ℝ) / k, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_fricke, coe_S]
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  apply smul_mul_mul_smul_eq hs hmr
  rw [mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem hPart_32 : hPart 32 = 4 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num, hPart_two_pow]; norm_num

theorem hPart_64 : hPart 64 = 8 := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, hPart_two_pow]; norm_num

theorem hPart_256 : hPart 256 = 8 := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, hPart_two_pow]; norm_num

theorem mul_pow_four_eq {G : Type*} [Group G] (a b : G) :
    (a * b) ^ 4 = (a * b * a) * b * (a * b * a) * b := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-! ### The relators hold -/

theorem rels_c5 : ∀ ρ ∈ barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2},
    FreeGroup.lift (locF (fricke 32 (NeZero.ne 32)) (hPart 32)) ρ ∈ Gamma0R 32 := by
  have hm : (32 : ℕ) ≠ 0 := by norm_num
  rw [hPart_32]
  intro ρ hρ
  simp only [barsRels, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with ((rfl | rfl | rfl) | rfl)
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact fricke_sq_mem _ _
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact S_pow_self_mem _ _ (by norm_num)
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of, locF]
    rw [mul_pow_four_eq]
    have hX := coe_fricke_S_fricke 32 4 hm (by norm_num)
    set X := fricke 32 (NeZero.ne 32) * S 4 * fricke 32 (NeZero.ne 32)
    refine mem_Gamma0R_of_entries (-1) 0 0 (-1) ?_ (by norm_num)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hX, coe_S]
    norm_num [mul_fin_two]
  · have hR := coe_lift_rr 32 4 hm (by norm_num)
    rw [show (w * s⁻¹ * w : FreeGroup LGen) = rr by rw [rr_def]]
    rel_compute 3 1 32 11 hR

theorem rels_c6 : ∀ ρ ∈ barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3},
    FreeGroup.lift (locF (fricke 64 (NeZero.ne 64)) (hPart 64)) ρ ∈ Gamma0R 64 := by
  have hm : (64 : ℕ) ≠ 0 := by norm_num
  have hW := coe_fricke_of_sq 64 8 hm (by norm_num)
  rw [hPart_64]
  intro ρ hρ
  simp only [barsRels, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with ((rfl | rfl | rfl) | rfl)
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact fricke_sq_mem _ _
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact S_pow_self_mem _ _ (by norm_num)
  · rel_compute (-1) 0 0 (-1) hW
  · rel_compute (-5) (-1) (-64) (-13) hW

theorem rels_d8 : ∀ ρ ∈ ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
      Set (FreeGroup LGen)),
    FreeGroup.lift (locF (fricke 256 (NeZero.ne 256)) (hPart 256)) ρ ∈ Gamma0R 256 := by
  have hm : (256 : ℕ) ≠ 0 := by norm_num
  have hW := coe_fricke_of_sq 256 16 hm (by norm_num)
  rw [hPart_256]
  intro ρ hρ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact fricke_sq_mem _ _
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact S_pow_self_mem _ _ (by norm_num)
  · rel_compute (-11) (-4) 256 93 hW

/-! ### The isomorphisms -/

/-- **T8(c)**, λ = 5. -/
theorem completed_lambda5' :
    ∃ φ : PresentedGroup (barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2}) ≃* B 32,
      (φ (.of .w)).IsALClass 32 ∧ (φ (.of .s)).IsClassOf (S 4) := by
  have := finite_B' 32
  have hcard : Nat.card (PresentedGroup (barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2})) =
      Nat.card (B 32) := by
    rw [completed_lambda5_card', show (32 : ℕ) = 2 ^ 5 by norm_num,
      card_B_prime_pow Nat.prime_two (by norm_num)]
    rfl
  have : Finite (PresentedGroup (barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2})) :=
    Nat.finite_of_card_ne_zero (by rw [completed_lambda5_card']; norm_num)
  have hbij := (presHom_surjective rels_c5 Nat.prime_two (by norm_num : 0 < 5)
    (by norm_num)).bijective_of_nat_card_le hcard.le
  refine ⟨MulEquiv.ofBijective _ hbij, presHom_w_isALClass rels_c5, ?_⟩
  have := presHom_s_isClassOf rels_c5
  rwa [hPart_32] at this

/-- **T8(c)**, λ = 6. -/
theorem completed_lambda6' :
    ∃ φ : PresentedGroup (barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3}) ≃* B 64,
      (φ (.of .w)).IsALClass 64 ∧ (φ (.of .s)).IsClassOf (S 8) := by
  have := finite_B' 64
  have hcard : Nat.card (PresentedGroup (barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3})) =
      Nat.card (B 64) := by
    rw [completed_lambda6_card', show (64 : ℕ) = 2 ^ 6 by norm_num,
      card_B_prime_pow Nat.prime_two (by norm_num)]
    rfl
  have : Finite (PresentedGroup (barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3})) :=
    Nat.finite_of_card_ne_zero (by rw [completed_lambda6_card']; norm_num)
  have hbij := (presHom_surjective rels_c6 Nat.prime_two (by norm_num : 0 < 6)
    (by norm_num)).bijective_of_nat_card_le hcard.le
  refine ⟨MulEquiv.ofBijective _ hbij, presHom_w_isALClass rels_c6, ?_⟩
  have := presHom_s_isClassOf rels_c6
  rwa [hPart_64] at this

/-- **T8(d)**: Bars's λ = 8 presentation presents B(256). -/
theorem bars_lambda8' :
    ∃ φ : PresentedGroup ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
        Set (FreeGroup LGen)) ≃* B 256,
      (φ (.of .w)).IsALClass 256 ∧ (φ (.of .s)).IsClassOf (S 8) := by
  have := finite_B' 256
  have hcard : Nat.card (PresentedGroup ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
      Set (FreeGroup LGen))) = Nat.card (B 256) := by
    rw [bars_lambda8_card', show (256 : ℕ) = 2 ^ 8 by norm_num,
      card_B_prime_pow Nat.prime_two (by norm_num)]
    rfl
  have : Finite (PresentedGroup ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
      Set (FreeGroup LGen))) :=
    Nat.finite_of_card_ne_zero (by rw [bars_lambda8_card']; norm_num)
  have hbij := (presHom_surjective rels_d8 Nat.prime_two (by norm_num : 0 < 8)
    (by norm_num)).bijective_of_nat_card_le hcard.le
  refine ⟨MulEquiv.ofBijective _ hbij, presHom_w_isALClass rels_d8, ?_⟩
  have := presHom_s_isClassOf rels_d8
  rwa [hPart_256] at this

end

end NormalizerLean
