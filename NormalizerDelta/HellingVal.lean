module

public import NormalizerLean.Defs

@[expose] public section

/-!
# Part 9: p-adic distances of integral 2×2 matrices

For an integral 2×2 matrix X with det X ≠ 0 and a prime p, `dist p X` = v_p(det X) − 2·v_p(c(X)), where c(X) is the
gcd of the entries (`cont`).  This is the p-part of Conway's hyperdistance between the lattice classes [ℤ²] and
[Xℤ²], i.e. the distance of the vertices [ℤ_(p)²] and [Xℤ_(p)²] of the p-adic tree; `dd p X Y` = `dist p (adj X·Y)`
is the distance of [Xℤ_(p)²] and [Yℤ_(p)²].  This file proves the calculus: the triangle inequality, invariance under
scalars and under matrices of determinant prime to p, parity, and the "V shape" of k ↦ dd(diag(p^k, 1)·Y)
(`dist_diagP_mul`), which is what makes the p-adic tree a tree.
-/

open Matrix

namespace NormalizerLean.Helling

/-- The gcd of the four entries of an integral 2×2 matrix. -/
def cont (X : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Int.gcd (Int.gcd (X 0 0) (X 0 1)) (Int.gcd (X 1 0) (X 1 1))

theorem dvd_cont_iff {k : ℤ} {X : Matrix (Fin 2) (Fin 2) ℤ} :
    k ∣ (cont X : ℤ) ↔ ∀ i j, k ∣ X i j := by
  simp only [cont, Int.dvd_coe_gcd_iff, Fin.forall_fin_two]

theorem eq_zero_of_cont_eq_zero {X : Matrix (Fin 2) (Fin 2) ℤ} (h : cont X = 0) : X = 0 := by
  ext i j
  have := dvd_cont_iff.1 (show (0 : ℤ) ∣ (cont X : ℤ) by rw [h]; simp) i j
  simpa using this

theorem cont_ne_zero {X : Matrix (Fin 2) (Fin 2) ℤ} (h : X.det ≠ 0) : cont X ≠ 0 := by
  intro h0
  apply h
  rw [eq_zero_of_cont_eq_zero h0]
  simp

theorem det_adjugate' (X : Matrix (Fin 2) (Fin 2) ℤ) : X.adjugate.det = X.det := by
  rw [det_adjugate]
  simp

theorem adjugate_adjugate' (X : Matrix (Fin 2) (Fin 2) ℤ) : X.adjugate.adjugate = X := by
  rw [adjugate_adjugate _ (by simp)]
  simp

theorem det_mul_ne_zero {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    (X * Y).det ≠ 0 := by
  rw [det_mul]
  exact mul_ne_zero hX hY

theorem det_adjugate_ne_zero {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : X.adjugate.det ≠ 0 := by
  rwa [det_adjugate']

theorem det_smul_ne_zero {n : ℤ} (hn : n ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) :
    (n • X).det ≠ 0 := by
  rw [det_smul]
  exact mul_ne_zero (pow_ne_zero _ hn) hX

variable (p : ℕ)

/-- v_p of the gcd of the entries. -/
def vc (X : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := padicValNat p (cont X)

/-- v_p of the determinant. -/
def vd (X : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := padicValInt p X.det

/-- The p-adic distance d_p(X) = v_p(det X) − 2·v_p(c(X)). -/
def dist (X : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := vd p X - 2 * vc p X

/-- The distance of the vertices [Xℤ_(p)²] and [Yℤ_(p)²]: d_p(adj X · Y). -/
def dd (X Y : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := dist p (X.adjugate * Y)

/-- diag(p^k, 1). -/
def diagP (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ) ^ k, 0; 0, 1]

/-- v_p of the gcd of the first row. -/
def va (Y : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := padicValNat p (Int.gcd (Y 0 0) (Y 0 1))

/-- v_p of the gcd of the second row. -/
def vb (Y : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := padicValNat p (Int.gcd (Y 1 0) (Y 1 1))

variable {p} [hp : Fact p.Prime]

theorem pow_dvd_iff_le_vc {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) {k : ℕ} :
    (∀ i j, (p : ℤ) ^ k ∣ X i j) ↔ k ≤ vc p X := by
  rw [← dvd_cont_iff, vc, ← padicValNat_dvd_iff_le (cont_ne_zero hX)]
  norm_cast

theorem pow_dvd_det_iff {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) {k : ℕ} :
    (p : ℤ) ^ k ∣ X.det ↔ k ≤ vd p X := by
  rw [padicValInt_dvd_iff, vd]
  simp [hX]

theorem pow_vc_dvd {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (i j : Fin 2) :
    (p : ℤ) ^ vc p X ∣ X i j :=
  (pow_dvd_iff_le_vc hX).2 le_rfl i j

theorem vc_eq_of_iff {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) {m : ℕ}
    (h : ∀ k : ℕ, (∀ i j, (p : ℤ) ^ k ∣ X i j) ↔ k ≤ m) : vc p X = m := by
  apply le_antisymm
  · exact (h _).1 ((pow_dvd_iff_le_vc hX).2 le_rfl)
  · exact (pow_dvd_iff_le_vc hX).1 ((h _).2 le_rfl)

theorem two_vc_le_vd {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : 2 * vc p X ≤ vd p X := by
  rw [← pow_dvd_det_iff hX, det_fin_two, two_mul, pow_add]
  exact dvd_sub (mul_dvd_mul (pow_vc_dvd hX 0 0) (pow_vc_dvd hX 1 1))
    (mul_dvd_mul (pow_vc_dvd hX 0 1) (pow_vc_dvd hX 1 0))

theorem vd_mul {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    vd p (X * Y) = vd p X + vd p Y := by
  simp only [vd, det_mul]
  exact padicValInt.mul hX hY

theorem vc_mul {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    vc p X + vc p Y ≤ vc p (X * Y) := by
  rw [← pow_dvd_iff_le_vc (det_mul_ne_zero hX hY)]
  intro i j
  rw [mul_apply, Fin.sum_univ_two, pow_add]
  exact dvd_add (mul_dvd_mul (pow_vc_dvd hX _ _) (pow_vc_dvd hY _ _))
    (mul_dvd_mul (pow_vc_dvd hX _ _) (pow_vc_dvd hY _ _))

theorem dist_mul_le {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    dist p (X * Y) ≤ dist p X + dist p Y := by
  have h1 := vd_mul (p := p) hX hY
  have h2 := vc_mul (p := p) hX hY
  have h3 := two_vc_le_vd (p := p) hX
  have h4 := two_vc_le_vd (p := p) hY
  simp only [dist]
  omega

theorem dist_mod_two (X : Matrix (Fin 2) (Fin 2) ℤ) (hX : X.det ≠ 0) : dist p X % 2 = vd p X % 2 := by
  have := two_vc_le_vd (p := p) hX
  simp only [dist]
  omega

/-! ### Adjugates and scalars -/

theorem vc_adjugate {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : vc p X.adjugate = vc p X := by
  apply vc_eq_of_iff (det_adjugate_ne_zero hX)
  intro k
  rw [← pow_dvd_iff_le_vc hX]
  simp only [adjugate_fin_two, Fin.forall_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, dvd_neg]
  tauto

omit hp in
theorem vd_adjugate (X : Matrix (Fin 2) (Fin 2) ℤ) : vd p X.adjugate = vd p X := by
  simp [vd, det_adjugate']

theorem dist_adjugate {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : dist p X.adjugate = dist p X := by
  simp only [dist, vd_adjugate, vc_adjugate hX]

theorem cont_smul (n : ℤ) (X : Matrix (Fin 2) (Fin 2) ℤ) : cont (n • X) = n.natAbs * cont X := by
  simp only [cont, Matrix.smul_apply, smul_eq_mul, Int.gcd_mul_left]
  push_cast
  rw [Int.gcd_mul_left, Int.natAbs_abs]

theorem vc_smul {n : ℤ} (hn : n ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) :
    vc p (n • X) = padicValInt p n + vc p X := by
  simp only [vc, cont_smul, padicValInt]
  exact padicValNat.mul (Int.natAbs_ne_zero.2 hn) (cont_ne_zero hX)

theorem vd_smul {n : ℤ} (hn : n ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) :
    vd p (n • X) = 2 * padicValInt p n + vd p X := by
  simp only [vd, det_smul, Fintype.card_fin, pow_two]
  rw [padicValInt.mul (mul_ne_zero hn hn) hX, padicValInt.mul hn hn]
  ring

theorem dist_smul {n : ℤ} (hn : n ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) :
    dist p (n • X) = dist p X := by
  simp only [dist, vc_smul hn hX, vd_smul hn hX]
  omega

omit hp in
theorem dist_one : dist p (1 : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
  simp [dist, vd]

/-! ### Matrices of determinant prime to p -/

omit hp in
theorem det_ne_zero_of_not_dvd {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : ¬ (p : ℤ) ∣ U.det) : U.det ≠ 0 :=
  fun h => hU (h ▸ dvd_zero _)

omit hp in
theorem dist_eq_zero_of_not_dvd {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : ¬ (p : ℤ) ∣ U.det) : dist p U = 0 := by
  simp [dist, vd, padicValInt.eq_zero_of_not_dvd hU]

theorem dist_unit_mul {U X : Matrix (Fin 2) (Fin 2) ℤ} (hU : ¬ (p : ℤ) ∣ U.det) (hX : X.det ≠ 0) :
    dist p (U * X) = dist p X := by
  have hU0 := det_ne_zero_of_not_dvd hU
  apply le_antisymm
  · have := dist_mul_le (p := p) hU0 hX
    rw [dist_eq_zero_of_not_dvd hU] at this
    omega
  · have e : U.adjugate * (U * X) = U.det • X := by
      rw [← Matrix.mul_assoc, adjugate_mul, smul_mul, Matrix.one_mul]
    have h1 := dist_mul_le (p := p) (det_adjugate_ne_zero hU0) (det_mul_ne_zero hU0 hX)
    rw [e, dist_smul hU0 hX, dist_adjugate hU0, dist_eq_zero_of_not_dvd hU] at h1
    omega

theorem dist_mul_unit {U X : Matrix (Fin 2) (Fin 2) ℤ} (hU : ¬ (p : ℤ) ∣ U.det) (hX : X.det ≠ 0) :
    dist p (X * U) = dist p X := by
  have hU0 := det_ne_zero_of_not_dvd hU
  rw [← dist_adjugate (det_mul_ne_zero hX hU0), adjugate_mul_distrib,
    dist_unit_mul (by rwa [det_adjugate']) (det_adjugate_ne_zero hX), dist_adjugate hX]

theorem not_dvd_det_of_det_eq_one {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : U.det = 1) : ¬ (p : ℤ) ∣ U.det := by
  rw [hU]
  norm_cast
  exact hp.out.not_dvd_one

/-! ### The distance between two vertices -/

theorem dd_comm {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) : dd p X Y = dd p Y X := by
  rw [dd, dd, ← dist_adjugate (det_mul_ne_zero (det_adjugate_ne_zero hX) hY), adjugate_mul_distrib,
    adjugate_adjugate']

theorem dd_self {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : dd p X X = 0 := by
  rw [dd, adjugate_mul, dist_smul hX (by simp), dist_one]

theorem dd_triangle {X Y Z : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) (hZ : Z.det ≠ 0) :
    dd p X Z ≤ dd p X Y + dd p Y Z := by
  have e : X.adjugate * Y * (Y.adjugate * Z) = Y.det • (X.adjugate * Z) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, mul_adjugate, smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have h := dist_mul_le (p := p) (det_mul_ne_zero (det_adjugate_ne_zero hX) hY)
    (det_mul_ne_zero (det_adjugate_ne_zero hY) hZ)
  rw [e, dist_smul hY (det_mul_ne_zero (det_adjugate_ne_zero hX) hZ)] at h
  exact h

theorem dd_mul_left {R X Y : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.det ≠ 0) (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    dd p (R * X) (R * Y) = dd p X Y := by
  have e : (R * X).adjugate * (R * Y) = R.det • (X.adjugate * Y) := by
    rw [adjugate_mul_distrib, Matrix.mul_assoc, ← Matrix.mul_assoc R.adjugate, adjugate_mul, smul_mul,
      Matrix.one_mul, Matrix.mul_smul]
  rw [dd, e, dist_smul hR (det_mul_ne_zero (det_adjugate_ne_zero hX) hY), dd]

theorem dd_mul_unit_right {X Y U : Matrix (Fin 2) (Fin 2) ℤ} (hU : ¬ (p : ℤ) ∣ U.det) (hX : X.det ≠ 0)
    (hY : Y.det ≠ 0) : dd p X (Y * U) = dd p X Y := by
  rw [dd, ← Matrix.mul_assoc, dist_mul_unit hU (det_mul_ne_zero (det_adjugate_ne_zero hX) hY), dd]

theorem dd_smul_right {X Y : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hn : n ≠ 0) (hX : X.det ≠ 0)
    (hY : Y.det ≠ 0) : dd p X (n • Y) = dd p X Y := by
  rw [dd, Matrix.mul_smul, dist_smul hn (det_mul_ne_zero (det_adjugate_ne_zero hX) hY), dd]

omit hp in
theorem dd_one_left {X : Matrix (Fin 2) (Fin 2) ℤ} : dd p 1 X = dist p X := by
  simp [dd]

theorem dd_mod_two {X Y : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    dd p X Y % 2 = (vd p X + vd p Y) % 2 := by
  rw [dd, dist_mod_two _ (det_mul_ne_zero (det_adjugate_ne_zero hX) hY),
    vd_mul (det_adjugate_ne_zero hX) hY, vd_adjugate]

/-- dd(X, Z) = 0 means X and Z are the same vertex; then they have the same distance to every Y. -/
theorem dd_eq_of_dd_eq_zero {X Y Z : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hY : Y.det ≠ 0)
    (hZ : Z.det ≠ 0) (h : dd p X Z = 0) : dd p X Y = dd p Z Y := by
  have h1 := dd_triangle (p := p) hX hZ hY
  have h2 := dd_triangle (p := p) hZ hX hY
  rw [dd_comm hZ hX] at h2
  omega


/-! ### Valuations of integers and diagonal matrices -/

theorem exists_eq_pow_mul_not_dvd {x : ℤ} (hx : x ≠ 0) :
    ∃ x' : ℤ, ¬ (p : ℤ) ∣ x' ∧ x = (p : ℤ) ^ padicValInt p x * x' := by
  obtain ⟨x', hx'⟩ : (p : ℤ) ^ padicValInt p x ∣ x := (padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)
  refine ⟨x', fun h => ?_, hx'⟩
  obtain ⟨t, ht⟩ := h
  have h1 : (p : ℤ) ^ (padicValInt p x + 1) ∣ x := ⟨t, by nth_rewrite 1 [hx']; rw [ht, pow_succ]; ring⟩
  have := ((padicValInt_dvd_iff _ _).1 h1).resolve_left hx
  omega

theorem padicValInt_le_of_dvd {x y : ℤ} (hy : y ≠ 0) (h : x ∣ y) : padicValInt p x ≤ padicValInt p y := by
  have : (p : ℤ) ^ padicValInt p x ∣ y := ((padicValInt_dvd_iff _ _).2 (Or.inr le_rfl)).trans h
  exact ((padicValInt_dvd_iff _ _).1 this).resolve_left hy

theorem dist_diag {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    dist p !![x, 0; 0, y] = padicValInt p x + padicValInt p y - 2 * min (padicValInt p x) (padicValInt p y) := by
  have hD : (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [det_fin_two_of]; simpa using mul_ne_zero hx hy
  have hvc : vc p !![x, 0; 0, y] = min (padicValInt p x) (padicValInt p y) := by
    apply vc_eq_of_iff hD
    intro k
    simp only [Fin.forall_fin_two, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, dvd_zero, and_true, true_and, le_min_iff]
    rw [padicValInt_dvd_iff, padicValInt_dvd_iff]
    simp [hx, hy]
  have hvd : vd p !![x, 0; 0, y] = padicValInt p x + padicValInt p y := by
    rw [vd, det_fin_two_of, mul_zero, sub_zero, padicValInt.mul hx hy]
  rw [dist, hvc, hvd]

/-! ### The V shape -/

theorem row0_ne_zero {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) : Int.gcd (Y 0 0) (Y 0 1) ≠ 0 := by
  intro h
  rw [Int.gcd_eq_zero_iff] at h
  apply hY
  rw [det_fin_two, h.1, h.2]
  ring

theorem row1_ne_zero {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) : Int.gcd (Y 1 0) (Y 1 1) ≠ 0 := by
  intro h
  rw [Int.gcd_eq_zero_iff] at h
  apply hY
  rw [det_fin_two, h.1, h.2]
  ring

theorem pow_dvd_row0_iff {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) {k : ℕ} :
    ((p : ℤ) ^ k ∣ Y 0 0 ∧ (p : ℤ) ^ k ∣ Y 0 1) ↔ k ≤ va p Y := by
  rw [← Int.dvd_coe_gcd_iff, va, ← padicValNat_dvd_iff_le (row0_ne_zero hY)]
  norm_cast

theorem pow_dvd_row1_iff {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) {k : ℕ} :
    ((p : ℤ) ^ k ∣ Y 1 0 ∧ (p : ℤ) ^ k ∣ Y 1 1) ↔ k ≤ vb p Y := by
  rw [← Int.dvd_coe_gcd_iff, vb, ← padicValNat_dvd_iff_le (row1_ne_zero hY)]
  norm_cast

theorem va_add_vb_le {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) : va p Y + vb p Y ≤ vd p Y := by
  obtain ⟨h00, h01⟩ := (pow_dvd_row0_iff (p := p) hY).2 le_rfl
  obtain ⟨h10, h11⟩ := (pow_dvd_row1_iff (p := p) hY).2 le_rfl
  rw [← pow_dvd_det_iff hY, det_fin_two, pow_add]
  exact dvd_sub (mul_dvd_mul h00 h11) (mul_dvd_mul h01 h10)

theorem pow_dvd_pow_mul_iff {k j : ℕ} {y : ℤ} :
    (p : ℤ) ^ j ∣ (p : ℤ) ^ k * y ↔ j ≤ k ∨ (p : ℤ) ^ (j - k) ∣ y := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hjk : j ≤ k
  · simp only [hjk, true_or, iff_true]
    exact (pow_dvd_pow _ hjk).mul_right _
  · simp only [hjk, false_or]
    rw [show j = k + (j - k) by omega, pow_add, mul_dvd_mul_iff_left (pow_ne_zero _ hp0),
      show k + (j - k) - k = j - k by omega]

omit hp in
theorem det_diagP_mul (k : ℕ) (Y : Matrix (Fin 2) (Fin 2) ℤ) :
    (diagP p k * Y).det = (p : ℤ) ^ k * Y.det := by
  rw [det_mul, diagP, det_fin_two_of]
  ring

theorem det_diagP_mul_ne_zero (k : ℕ) {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) :
    (diagP p k * Y).det ≠ 0 := by
  rw [det_diagP_mul]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hY

theorem vc_diagP_mul (k : ℕ) {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) :
    vc p (diagP p k * Y) = min (k + va p Y) (vb p Y) := by
  apply vc_eq_of_iff (det_diagP_mul_ne_zero k hY)
  intro j
  have e : ∀ i, (diagP p k * Y) 0 i = (p : ℤ) ^ k * Y 0 i := fun i => by
    simp [diagP, mul_apply, Fin.sum_univ_two]
  have e' : ∀ i, (diagP p k * Y) 1 i = Y 1 i := fun i => by
    simp [diagP, mul_apply, Fin.sum_univ_two]
  simp only [Fin.forall_fin_two, e, e', pow_dvd_pow_mul_iff]
  have h0 := pow_dvd_row0_iff (p := p) hY (k := j - k)
  have h1 := pow_dvd_row1_iff (p := p) hY (k := j)
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    have := h1.1 ⟨hc, hd⟩
    rcases ha with ha | ha
    · omega
    rcases hb with hb | hb
    · omega
    have := h0.1 ⟨ha, hb⟩
    omega
  · intro hj
    have hb := h1.2 (by omega)
    by_cases hjk : j ≤ k
    · exact ⟨⟨Or.inl hjk, Or.inl hjk⟩, hb⟩
    · have ha := h0.2 (by omega)
      exact ⟨⟨Or.inr ha.1, Or.inr ha.2⟩, hb⟩

theorem vd_diagP_mul (k : ℕ) {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) :
    vd p (diagP p k * Y) = k + vd p Y := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [vd, det_diagP_mul, padicValInt.mul (pow_ne_zero _ hp0) hY, vd]
  congr 1
  rw [padicValInt, Int.natAbs_pow, Int.natAbs_natCast, padicValNat.prime_pow]

/-- **The V shape**: d_p(diag(p^k, 1)·Y) = k + v_p(det Y) − 2 min(k + a, b), where a, b are the valuations of the
rows of Y; as a function of k it is |k − (b − a)| + const. -/
theorem dist_diagP_mul (k : ℕ) {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) :
    dist p (diagP p k * Y) = k + vd p Y - 2 * min (k + va p Y) (vb p Y) := by
  rw [dist, vc_diagP_mul k hY, vd_diagP_mul k hY]

omit hp in
theorem diagP_zero : diagP p 0 = 1 := by
  rw [diagP, pow_zero]
  exact (one_fin_two).symm

/-- The midpoint inequality: for n ≥ 2, f(1) ≤ max(f(0), f(n)) − 1, where f(k) = d_p(diag(p^k, 1)·Y). -/
theorem dist_diagP_one_lt {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    dist p (diagP p 1 * Y) + 1 ≤ max (dist p Y) (dist p (diagP p n * Y)) := by
  have h0 := dist_diagP_mul (p := p) 0 hY
  rw [diagP_zero, Matrix.one_mul] at h0
  rw [h0, dist_diagP_mul 1 hY, dist_diagP_mul n hY]
  have := va_add_vb_le (p := p) hY
  omega

end NormalizerLean.Helling
