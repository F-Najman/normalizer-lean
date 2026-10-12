import NormalizerLean.GenC

/-!
# T4, part 2: the invariant e of w_{m_p}, and the relation R = w_N S_h⁻¹ w_N⁻¹

For an Atkin–Lehner element g = (1/√Q)[[Qx, y], [Nz, Qw]] with Q = m_p = h_p² e (h_p = p^{v_p(h)},
e = p^{v_p(n)}), writing h = h_p h', the (8′)-data are (h_p x, h' y, h' z, h_p w, e, 1).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem hPart_split {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime) :
    ∃ h' : ℕ, hPart N = p ^ (hPart N).factorization p * h' ∧ Nat.Coprime p h' ∧
      h' ^ 2 ∣ N / mPart N p := by
  have hh0 := (hPart_pos N).ne'
  set k := (hPart N).factorization p
  refine ⟨hPart N / p ^ k, (Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)).symm,
    Nat.coprime_ordCompl hp hh0, ?_⟩
  set h' := hPart N / p ^ k
  have hh' : h' ∣ hPart N := Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _)
  have h1 : h' ^ 2 ∣ N := dvd_trans (pow_dvd_pow_of_dvd hh' 2) (hPart_sq_dvd hN)
  have hcop : Nat.Coprime (h' ^ 2) (mPart N p) :=
    (Nat.Coprime.pow (N.factorization p) 2 (Nat.coprime_ordCompl hp hh0)).symm
  have h2 : mPart N p ∣ N := Nat.ordProj_dvd N p
  rw [Nat.dvd_div_iff_mul_dvd h2, mul_comm]
  exact hcop.mul_dvd_of_dvd_of_dvd h1 h2

theorem mPart_eq {N p : ℕ} (hN : N ≠ 0) :
    mPart N p = (p ^ (hPart N).factorization p) ^ 2 * p ^ (nPart N).factorization p := by
  unfold mPart
  rw [← pow_mul, ← pow_add, ← factorization_nPart (p := p) hN]
  ring_nf

/-- Newman data of an Atkin–Lehner element of m_p: e = p^{v_p(n)}. -/
theorem NData_of_isAtkinLehner {N p : ℕ} [NeZero N] (hp : p.Prime) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N (mPart N p) g) :
    ∃ a b c d : ℤ, NData N g a b c d (p ^ (nPart N).factorization p) 1 := by
  have hN := NeZero.ne N
  obtain ⟨h', hsplit, hcop, hdvd⟩ := hPart_split hN hp
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  set k := (hPart N).factorization p
  set ν' := (nPart N).factorization p
  set hp' := p ^ k
  set e := p ^ ν'
  have hQ : mPart N p = hp' ^ 2 * e := mPart_eq hN
  have he0 : 0 < e := pow_pos hp.pos _
  have hhp0 : 0 < hp' := pow_pos hp.pos _
  have hh'0 : 0 < h' := by
    rcases Nat.eq_zero_or_pos h' with h0 | h0
    · rw [h0, mul_zero] at hsplit; exact absurd hsplit (hPart_pos N).ne'
    · exact h0
  -- N = n h², n = e · (N/m_p)/h'²
  have hNnh := hPart_sq_mul_nPart N hN
  obtain ⟨t, ht⟩ := hdvd
  have hNm : N = mPart N p * (N / mPart N p) := (Nat.mul_div_cancel' (Nat.ordProj_dvd N p)).symm
  have hn : nPart N = e * t := by
    have : nPart N * (hp' ^ 2 * h' ^ 2) = e * t * (hp' ^ 2 * h' ^ 2) :=
      calc nPart N * (hp' ^ 2 * h' ^ 2) = N := by rw [← mul_pow, ← hsplit, hNnh]
        _ = mPart N p * (N / mPart N p) := hNm
        _ = e * t * (hp' ^ 2 * h' ^ 2) := by rw [ht, hQ]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  refine ⟨hp' * x, h' * y, h' * z, hp' * w, he0, ⟨t, hn⟩, ?_, Or.inl rfl, ?_⟩
  · -- determinant
    have hdetz : ((hp' ^ 2 * e : ℕ) : ℤ) ^ 2 * x * w - N * y * z = (hp' ^ 2 * e : ℕ) := by
      rw [← hQ]; exact hdet
    have hNz : (N : ℤ) = (e * t : ℕ) * ((hp' * h' : ℕ) : ℤ) ^ 2 := by
      rw [← hn, ← hsplit]; exact_mod_cast hNnh.symm
    rw [hNz] at hdetz
    push_cast at hdetz ⊢
    rw [hn]
    push_cast
    have hhpz : ((hp' : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hhp0.ne'
    apply mul_left_cancel₀ (pow_ne_zero 2 hhpz)
    linear_combination hdetz
  · -- the matrix
    rw [hgm]
    have hs : Real.sqrt (mPart N p : ℝ) = hp' * Real.sqrt e := by
      rw [hQ]; push_cast
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hse : Real.sqrt (e : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast he0)).ne'
    have hsq : Real.sqrt (e : ℝ) * Real.sqrt e = e := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hhr : (hp' : ℝ) ≠ 0 := by exact_mod_cast hhp0.ne'
    have hh'r : (h' : ℝ) ≠ 0 := by exact_mod_cast hh'0.ne'
    have hH : (hPart N : ℝ) = hp' * h' := by exact_mod_cast hsplit
    have hQr : (mPart N p : ℝ) = hp' ^ 2 * e := by exact_mod_cast hQ
    rw [hs, hH, hQr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- e(w_{m_p}) = p^{v_p(n)}. -/
theorem eOf_isAtkinLehner {N p : ℕ} [NeZero N] (hp : p.Prime) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N (mPart N p) g) : eOf N g = p ^ (nPart N).factorization p := by
  obtain ⟨a, b, c, d, h⟩ := NData_of_isAtkinLehner hp hg
  exact eOf_eq h

end

end NormalizerLean
