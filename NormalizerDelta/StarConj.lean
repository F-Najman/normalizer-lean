module

public import NormalizerDelta.StarBasic

@[expose] public section

/-!
# Part 7: the conjugation formula

For an Atkin–Lehner element w = (1/√Q)[[QA, B], [QmC, QD']] of level n = Qm (QAD' − mBC = 1), h ≥ 1, and
γ = [[a, b], [Nc, d]] with N = Qmh² and d − a = ht, the element g = D_h⁻¹ w D_h satisfies
g γ g⁻¹ = [[x₁₁, x₁₂], [N x₂₁, x₂₂]] with the integers

* x₁₁ = QAD'a + hQmBD'c − hQmACb − mBCd,
* x₁₂ = ABt + QA²b − mB²c,
* x₂₁ = −CD't + QD'²c − mC²b,
* x₂₂ = d + h(mBCt + Qm(ACb − BD'c)).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem coe_conj_al_mul_conj {h Q m : ℕ} (hh : 0 < h) (hQ : 0 < Q) {A B C D' : ℤ}
    (hdet : (Q : ℤ) * A * D' - m * B * C = 1) {w : SL(2, ℝ)}
    (hw : (w : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * A, B; (Q : ℝ) * m * C, (Q : ℝ) * D'])
    {γ : SL(2, ℝ)} {a b c d t : ℤ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (Q : ℝ) * m * h ^ 2 * c, d])
    (ht : d - a = h * t) :
    ((MulAut.conj (Dm h)⁻¹ w * γ * (MulAut.conj (Dm h)⁻¹ w)⁻¹ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![((Q * A * D' * a + h * Q * m * B * D' * c - h * Q * m * A * C * b - m * B * C * d : ℤ) : ℝ),
        ((A * B * t + Q * A ^ 2 * b - m * B ^ 2 * c : ℤ) : ℝ);
        (Q : ℝ) * m * h ^ 2 * ((-(C * D' * t) + Q * D' ^ 2 * c - m * C ^ 2 * b : ℤ) : ℝ),
        ((d + h * (m * B * C * t + Q * m * (A * C * b - B * D' * c)) : ℤ) : ℝ)] := by
  set s : ℝ := (Real.sqrt Q)⁻¹ with hsdef
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hs : s ^ 2 * Q = 1 := by
    rw [hsdef, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; field_simp
  have hw' : (w : Matrix (Fin 2) (Fin 2) ℝ) =
      !![s * (Q * A), s * B; s * (Q * m * C), s * (Q * D')] := by
    rw [hw]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hg := coe_conj_Dm_inv hh hw'
  set g := MulAut.conj (Dm h)⁻¹ w
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  set β : ℝ := (B : ℝ) / h with hβdef
  have hBβ : (B : ℝ) = β * h := by rw [hβdef]; field_simp
  have hg' : (g : Matrix (Fin 2) (Fin 2) ℝ) =
      !![s * Q * A, s * β; s * h * Q * m * C, s * Q * D'] := by
    rw [hg]; ext i j; fin_cases i <;> fin_cases j <;> simp [hβdef] <;> ring
  have hdetR : (Q : ℝ) * A * D' - m * (β * h) * C = 1 := by rw [← hBβ]; exact_mod_cast hdet
  have htR : (d : ℝ) - a = h * t := by exact_mod_cast ht
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hg', hγ, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;>
    (try rw [hBβ])
  · linear_combination
      ((Q : ℝ) * A * D' * a + h * Q * m * (β * h) * D' * c - h * Q * m * A * C * b - m * (β * h) * C * d) * hs
  · linear_combination (s ^ 2 * (A * Q * β)) * htR +
      ((A : ℝ) * (β * h) * t + Q * A ^ 2 * b - m * (β * h) ^ 2 * c) * hs
  · linear_combination (s ^ 2 * (-(C : ℝ) * D' * Q ^ 2 * h * m)) * htR +
      ((Q : ℝ) * m * h ^ 2 * (-(C * D' * t) + Q * D' ^ 2 * c - m * C ^ 2 * b)) * hs
  · linear_combination (s ^ 2 * (Q * d)) * hdetR + (s ^ 2 * (C * Q * β * h * m)) * htR +
      ((d : ℝ) + h * (m * (β * h) * C * t + Q * m * (A * C * b - (β * h) * D' * c))) * hs

end

end NormalizerLean
