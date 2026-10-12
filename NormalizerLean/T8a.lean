import NormalizerLean.GlobalRels

/-!
# T8(a): the relations at N = 256

With w = w₂₅₆ = [[0, −1/16], [16, 0]] and s = S₈:
* (w s² w s)(s² w s w)⁻¹ = [[5, −9/8], [−288, 65]] ∉ Γ₀(256), so Akbaş–Singerman's relation fails;
* w s w s w s³ w s³ = −[[11, 4], [−256, −93]] ∈ Γ₀(256), so Bars's relation holds.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem coe_w256 : ((w256 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1 / 16; 16, 0] := rfl

theorem AS_quotient_matrix' :
    ((w256 * S 8 ^ 2 * w256 * S 8 * (S 8 ^ 2 * w256 * S 8 * w256)⁻¹ : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![5, -9 / 8; -288, 65] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_pow, coe_w256, coe_S]
  norm_num [adjugate_fin_two_of, mul_fin_two, pow_succ]

theorem bars_word_matrix' :
    ((w256 * S 8 * w256 * S 8 * w256 * S 8 ^ 3 * w256 * S 8 ^ 3 : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = -!![11, 4; -256, -93] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_w256,
    coe_S]
  norm_num [mul_fin_two, pow_succ]

theorem w256_isAtkinLehner : IsAtkinLehner 256 256 w256 := by
  refine ⟨0, -1, 1, 0, by norm_num, ?_⟩
  rw [coe_w256, show Real.sqrt ((256 : ℕ) : ℝ) = 16 by
    rw [show ((256 : ℕ) : ℝ) = 16 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem w256_mem : w256 ∈ Norm0 256 := by
  have : NeZero (256 : ℕ) := ⟨by norm_num⟩
  exact isAtkinLehner_mem_normalizer' dvd_rfl w256_isAtkinLehner

theorem S8_mem : S 8 ∈ Norm0 256 := by
  have : NeZero (256 : ℕ) := ⟨by norm_num⟩
  refine S_mem_normalizer' ?_
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, hPart_two_pow]
  norm_num

theorem AS_relation_fails' :
    ∃ x y : B 256, x.IsClassOf w256 ∧ y.IsClassOf (S 8) ∧
      x * y ^ 2 * x * y ≠ y ^ 2 * x * y * x := by
  refine ⟨QuotientGroup.mk ⟨w256, w256_mem⟩, QuotientGroup.mk ⟨S 8, S8_mem⟩,
    B.isClassOf_mk _, B.isClassOf_mk _, ?_⟩
  intro h
  set W : Norm0 256 := ⟨w256, w256_mem⟩
  set T : Norm0 256 := ⟨S 8, S8_mem⟩
  have h' : (QuotientGroup.mk (W * T ^ 2 * W * T) : B 256) =
      QuotientGroup.mk (T ^ 2 * W * T * W) := h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
  have hmem := (mul_inv_mem_iff_inv_mul_mem (W * T ^ 2 * W * T).2).2 h'
  have hmem' : w256 * S 8 ^ 2 * w256 * S 8 * (S 8 ^ 2 * w256 * S 8 * w256)⁻¹ ∈ Gamma0R 256 := hmem
  obtain ⟨a, b, c, d, -, -, hm⟩ := exists_entries_of_mem_Gamma0R hmem'
  rw [AS_quotient_matrix'] at hm
  have hb : (b : ℝ) = -9 / 8 := by
    have := congrFun (congrFun hm 0) 1
    simpa using this.symm
  have : (8 * b : ℤ) = -9 := by
    have : ((8 * b : ℤ) : ℝ) = -9 := by push_cast; rw [hb]; norm_num
    exact_mod_cast this
  omega

theorem bars_relation_holds' :
    ∃ x y : B 256, x.IsClassOf w256 ∧ y.IsClassOf (S 8) ∧
      x * y * x * y * x * y ^ 3 * x * y ^ 3 = 1 := by
  refine ⟨QuotientGroup.mk ⟨w256, w256_mem⟩, QuotientGroup.mk ⟨S 8, S8_mem⟩,
    B.isClassOf_mk _, B.isClassOf_mk _, ?_⟩
  set W : Norm0 256 := ⟨w256, w256_mem⟩
  set T : Norm0 256 := ⟨S 8, S8_mem⟩
  show (QuotientGroup.mk (W * T * W * T * W * T ^ 3 * W * T ^ 3) : B 256) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show w256 * S 8 * w256 * S 8 * w256 * S 8 ^ 3 * w256 * S 8 ^ 3 ∈ Gamma0R 256
  refine mem_Gamma0R_of_entries (-11) (-4) 256 93 ?_ (by norm_num)
  rw [bars_word_matrix']
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

end

end NormalizerLean
