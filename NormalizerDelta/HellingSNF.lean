module

public import NormalizerDelta.HellingVal

@[expose] public section

/-!
# Part 9: the Smith normal form of an integral 2×2 matrix

`exists_snf`: every X ∈ M₂(ℤ) is U·diag(x, y)·V with det U = det V = 1 and x ∣ y.  The proof minimizes |(UXV)₀₀|
over U, V ∈ SL₂(ℤ) (one Bézout step reduces it unless (UXV)₀₀ divides its row and column), clears the row and the
column, and then replaces diag(x, y) by diag(gcd(x, y), xy/gcd(x, y)).
-/

open Matrix

namespace NormalizerLean.Helling

/-- One Bézout step on the first column: some W of determinant 1 makes the first column of W·X equal to
(gcd(X₀₀, X₁₀), 0). -/
theorem exists_col_gcd (X : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W.det = 1 ∧ (W * X) 0 0 = Int.gcd (X 0 0) (X 1 0) ∧ (W * X) 1 0 = 0 := by
  set a := X 0 0
  set b := X 1 0
  set g := Int.gcd a b
  by_cases hg : g = 0
  · rw [Int.gcd_eq_zero_iff] at hg
    refine ⟨1, det_one, ?_, ?_⟩
    · simp [g, a, b, hg.1, hg.2]
    · simpa [b] using hg.2
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg
  have ha : (g : ℤ) ∣ a := Int.gcd_dvd_left a b
  have hb : (g : ℤ) ∣ b := Int.gcd_dvd_right a b
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  have hbez : (g : ℤ) = a * a.gcdA b + b * a.gcdB b := Int.gcd_eq_gcd_ab a b
  refine ⟨!![a.gcdA b, a.gcdB b; -b', a'], ?_, ?_, ?_⟩
  · rw [det_fin_two_of]
    apply mul_left_cancel₀ hgz
    linear_combination -hbez - a.gcdA b * ha' - a.gcdB b * hb'
  · simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    rw [hbez]
    simp only [a, b]
    ring
  · simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    change -b' * a + a' * b = 0
    rw [ha', hb']
    ring

/-- One Bézout step on the first row. -/
theorem exists_row_gcd (X : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ W : Matrix (Fin 2) (Fin 2) ℤ, W.det = 1 ∧ (X * W) 0 0 = Int.gcd (X 0 0) (X 0 1) ∧ (X * W) 0 1 = 0 := by
  obtain ⟨W, hW, h1, h2⟩ := exists_col_gcd Xᵀ
  refine ⟨Wᵀ, by rw [det_transpose, hW], ?_, ?_⟩
  · have := congrFun (congrFun (transpose_mul W Xᵀ) 0) 0
    rw [transpose_transpose] at this
    rw [← this, transpose_apply, h1]
    simp
  · have := congrFun (congrFun (transpose_mul W Xᵀ) 0) 1
    rw [transpose_transpose] at this
    rw [← this, transpose_apply, h2]

theorem natAbs_gcd_lt {a b : ℤ} (ha : a ≠ 0) (h : ¬ a ∣ b) : Int.gcd a b < a.natAbs := by
  have h1 : Int.gcd a b ∣ a.natAbs := Int.gcd_dvd_natAbs_left a b
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 ha) h1
  rcases h2.lt_or_eq with h2 | h2
  · exact h2
  · exfalso
    apply h
    have : (a.natAbs : ℤ) ∣ b := by
      rw [← h2]
      exact Int.gcd_dvd_right a b
    exact (Int.natAbs_dvd.1 this)

theorem adjugate_mul_mul_adjugate {A X B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det = 1) (hB : B.det = 1) :
    A.adjugate * (A * X * B) * B.adjugate = X := by
  rw [Matrix.mul_assoc A, ← Matrix.mul_assoc A.adjugate, adjugate_mul, hA, one_smul, Matrix.one_mul,
    Matrix.mul_assoc, mul_adjugate, hB, one_smul, Matrix.mul_one]

/-- Every X ∈ M₂(ℤ) is U·diag(x, y)·V with U, V of determinant 1. -/
theorem exists_diag (X : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧ ∃ x y : ℤ, X = U * !![x, 0; 0, y] * V := by
  classical
  by_cases hX : X = 0
  · exact ⟨1, 1, det_one, det_one, 0, 0, by rw [hX]; ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  -- some U X V has a nonzero (0,0) entry
  have hex : ∃ n : ℕ, ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧ (U * X * V) 0 0 ≠ 0 ∧
      ((U * X * V) 0 0).natAbs = n := by
    obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hX (Matrix.ext h)
    have key : ∀ i j : Fin 2, ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧
        (U * X * V) 0 0 = X i j := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨1, 1, det_one, det_one, by simp⟩
      · exact ⟨1, !![0, -1; 1, 0], det_one, by simp [det_fin_two_of], by
          simp [mul_apply, Fin.sum_univ_two]⟩
      · exact ⟨!![0, 1; -1, 0], 1, by simp [det_fin_two_of], det_one, by
          simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct]⟩
      · exact ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [det_fin_two_of], by simp [det_fin_two_of], by
          simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct]⟩
    obtain ⟨U, V, hU, hV, he⟩ := key i j
    exact ⟨_, U, V, hU, hV, by rw [he]; exact hij, rfl⟩
  obtain ⟨U₀, V₀, hU₀, hV₀, hne, hn⟩ := Nat.find_spec hex
  have hmin : ∀ {m : ℕ}, (∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧ (U * X * V) 0 0 ≠ 0 ∧
      ((U * X * V) 0 0).natAbs = m) → Nat.find hex ≤ m := fun h => Nat.find_min' hex h
  set X' := U₀ * X * V₀ with hX'
  -- minimality gives the divisibilities
  have hdiv1 : X' 0 0 ∣ X' 1 0 := by
    by_contra h
    obtain ⟨W, hW, h1, -⟩ := exists_col_gcd X'
    have hlt := natAbs_gcd_lt hne h
    have hgne : Int.gcd (X' 0 0) (X' 1 0) ≠ 0 := by
      rw [Ne, Int.gcd_eq_zero_iff]
      exact fun h' => hne h'.1
    have e : W * U₀ * X * V₀ = W * X' := by rw [hX']; simp only [Matrix.mul_assoc]
    have := hmin ⟨W * U₀, V₀, by rw [det_mul, hW, hU₀, one_mul], hV₀, by
      rw [e, h1]
      exact_mod_cast hgne, by
      rw [e, h1, Int.natAbs_natCast]⟩
    omega
  have hdiv2 : X' 0 0 ∣ X' 0 1 := by
    by_contra h
    obtain ⟨W, hW, h1, -⟩ := exists_row_gcd X'
    have hlt := natAbs_gcd_lt hne h
    have hgne : Int.gcd (X' 0 0) (X' 0 1) ≠ 0 := by
      rw [Ne, Int.gcd_eq_zero_iff]
      exact fun h' => hne h'.1
    have e : U₀ * X * (V₀ * W) = X' * W := by rw [hX']; simp only [Matrix.mul_assoc]
    have := hmin ⟨U₀, V₀ * W, hU₀, by rw [det_mul, hW, hV₀, one_mul], by
      rw [e, h1]
      exact_mod_cast hgne, by
      rw [e, h1, Int.natAbs_natCast]⟩
    omega
  obtain ⟨c, hc⟩ := hdiv1
  obtain ⟨d, hd⟩ := hdiv2
  set E1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -c, 1]
  set E2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, -d; 0, 1]
  have hE1 : E1.det = 1 := by simp [E1, det_fin_two_of]
  have hE2 : E2.det = 1 := by simp [E2, det_fin_two_of]
  have hD : (E1 * U₀) * X * (V₀ * E2) = !![X' 0 0, 0; 0, X' 1 1 - c * X' 0 1] := by
    have : (E1 * U₀) * X * (V₀ * E2) = E1 * X' * E2 := by
      simp only [hX', Matrix.mul_assoc]
    rw [this]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E1, E2, mul_apply, Fin.sum_univ_two, vecMul, dotProduct, hc, hd] <;> ring
  refine ⟨(E1 * U₀).adjugate, (V₀ * E2).adjugate, by rw [det_adjugate', det_mul, hE1, hU₀, one_mul],
    by rw [det_adjugate', det_mul, hE2, hV₀, one_mul], X' 0 0, X' 1 1 - c * X' 0 1, ?_⟩
  rw [← hD, adjugate_mul_mul_adjugate (by rw [det_mul, hE1, hU₀, one_mul])
    (by rw [det_mul, hE2, hV₀, one_mul])]

/-- diag(x, y) = U·diag(g, l)·V with det U = det V = 1, g = gcd(x, y) and g ∣ l. -/
theorem exists_diag_dvd (x y : ℤ) :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧ ∃ g l : ℤ, g ∣ l ∧
      !![x, 0; 0, y] = U * !![g, 0; 0, l] * V := by
  set g := Int.gcd x y
  by_cases hg : g = 0
  · rw [Int.gcd_eq_zero_iff] at hg
    exact ⟨1, 1, det_one, det_one, 0, 0, dvd_rfl, by rw [hg.1, hg.2]; simp⟩
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg
  obtain ⟨x', hx'⟩ : (g : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : (g : ℤ) ∣ y := Int.gcd_dvd_right x y
  have hbez : (g : ℤ) = x * x.gcdA y + y * x.gcdB y := Int.gcd_eq_gcd_ab x y
  set s := x.gcdA y
  set t := x.gcdB y
  set R1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
  set W : Matrix (Fin 2) (Fin 2) ℤ := !![s, -y'; t, x']
  set R2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -(t * y'), 1]
  have hR1 : R1.det = 1 := by simp [R1, det_fin_two_of]
  have hR2 : R2.det = 1 := by simp [R2, det_fin_two_of]
  have hW : W.det = 1 := by
    simp only [W, det_fin_two_of]
    apply mul_left_cancel₀ hgz
    rw [hx', hy'] at hbez
    linear_combination -hbez
  have hD : (R2 * R1) * !![x, 0; 0, y] * W = !![(g : ℤ), 0; 0, x * y'] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R1, R2, W, mul_apply, Fin.sum_univ_two]
    · linear_combination -hbez
    · linear_combination (-y') * hx' + x' * hy'
    · linear_combination t * hy' + (t * y') * hbez
    · linear_combination (t * y' ^ 2 - y') * hx' + (x' - t * y' * x') * hy'
  refine ⟨(R2 * R1).adjugate, W.adjugate, by rw [det_adjugate', det_mul, hR1, hR2, one_mul],
    by rw [det_adjugate', hW], g, x * y', ?_, ?_⟩
  · rw [hx']
    exact (dvd_mul_right _ _).mul_right _
  · rw [← hD, adjugate_mul_mul_adjugate (by rw [det_mul, hR1, hR2, one_mul]) hW]

/-- **Smith normal form**: every X ∈ M₂(ℤ) is U·diag(x, y)·V with det U = det V = 1 and x ∣ y. -/
theorem exists_snf (X : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ U V : Matrix (Fin 2) (Fin 2) ℤ, U.det = 1 ∧ V.det = 1 ∧ ∃ x y : ℤ, x ∣ y ∧
      X = U * !![x, 0; 0, y] * V := by
  obtain ⟨U, V, hU, hV, x, y, hX⟩ := exists_diag X
  obtain ⟨U', V', hU', hV', g, l, hgl, hD⟩ := exists_diag_dvd x y
  refine ⟨U * U', V' * V, by rw [det_mul, hU, hU', one_mul], by rw [det_mul, hV, hV', one_mul], g, l, hgl, ?_⟩
  rw [hX, hD]
  simp only [Matrix.mul_assoc]

end NormalizerLean.Helling
