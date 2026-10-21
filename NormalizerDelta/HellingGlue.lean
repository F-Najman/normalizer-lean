module

public import NormalizerDelta.HellingCenter

@[expose] public section

/-!
# Part 9: gluing the primes, and the Atkin–Lehner shape

* `exists_glue_one`, `exists_glue`: a vertex can be moved at finitely many primes p (to a prescribed vertex) without
  moving it at the other primes.  With the Smith form adj(Z)·W = U·diag(e₁, e₂)·V one takes Z·U·diag(p^{a₁}, p^{a₂}).
* `al_shape`: a primitive integral Y of positive determinant that fixes the vertex 1 at every p ∤ N and preserves
  the edge {1, diag(1, N)} at every p ∣ N (N squarefree) is [[ex, y], [Nz, ew]] with e ∣ N and det Y = e.
* `fix_bound`, `dd_eq_zero_of_fix`: the vertices fixed by [[1, k], [0, 1]] and [[1, 0], [m, 1]].
-/

open Matrix

namespace NormalizerLean.Helling

/-- diag(1, N). -/
def diagN (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (N : ℤ)]

/-- [[1, k], [0, 1]]. -/
def upM (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, k; 0, 1]

/-- [[1, 0], [m, 1]]. -/
def loM (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; m, 1]

theorem det_diagN (N : ℕ) : (diagN N).det = N := by
  simp [diagN, det_fin_two_of]

theorem det_upT (k : ℤ) : (upM k).det = 1 := by
  simp [upM, det_fin_two_of]

theorem det_loT (m : ℤ) : (loM m).det = 1 := by
  simp [loM, det_fin_two_of]

/-- If every prime factor of the squarefree n divides x, then n ∣ x. -/
theorem dvd_of_squarefree {n : ℕ} (hn : Squarefree n) {x : ℤ} (h : ∀ p, p.Prime → p ∣ n → (p : ℤ) ∣ x) :
    (n : ℤ) ∣ x := by
  rw [← Nat.prod_primeFactors_of_squarefree hn, Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact Nat.Coprime.isCoprime ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq)
  · intro p hp
    exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

theorem padicValNat_eq_one_of_squarefree {N p : ℕ} (hN : Squarefree N) (hp : p.Prime) (hpN : p ∣ N) :
    padicValNat p N = 1 := by
  have hN0 : N ≠ 0 := hN.ne_zero
  have h1 := hN.natFactorization_le_one p
  have h2 := hp.factorization_pos_of_dvd hN0 hpN
  rw [Nat.factorization_def N hp] at h1 h2
  omega

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Gluing -/

/-- Move Z to W at p, without moving it at the other primes. -/
theorem exists_glue_one {Z W : Matrix (Fin 2) (Fin 2) ℤ} (hZ : Z.det ≠ 0) (hW : W.det ≠ 0) :
    ∃ Z' : Matrix (Fin 2) (Fin 2) ℤ, Z'.det ≠ 0 ∧ dd p Z' W = 0 ∧
      ∀ q, (hq : q.Prime) → q ≠ p → @dd q Z Z' = 0 := by
  obtain ⟨U, V, hU, hV, e₁, e₂, -, hX⟩ := exists_snf (Z.adjugate * W)
  have hXdet : (Z.adjugate * W).det ≠ 0 := det_mul_ne_zero (det_adjugate_ne_zero hZ) hW
  have hD : (!![e₁, 0; 0, e₂] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    intro h0; apply hXdet; rw [hX, det_mul, det_mul, h0]; ring
  have he₁ : e₁ ≠ 0 := by intro h0; apply hD; simp [det_fin_two_of, h0]
  have he₂ : e₂ ≠ 0 := by intro h0; apply hD; simp [det_fin_two_of, h0]
  obtain ⟨f₁, hf₁p, hf₁⟩ := exists_eq_pow_mul_not_dvd (p := p) he₁
  obtain ⟨f₂, hf₂p, hf₂⟩ := exists_eq_pow_mul_not_dvd (p := p) he₂
  set a₁ := padicValInt p e₁
  set a₂ := padicValInt p e₂
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set P : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ) ^ a₁, 0; 0, (p : ℤ) ^ a₂] with hPdef
  have hPdet : P.det = (p : ℤ) ^ (a₁ + a₂) := by
    rw [hPdef, det_fin_two_of, pow_add]; ring
  have hPdet0 : P.det ≠ 0 := by rw [hPdet]; exact pow_ne_zero _ hp0
  have hU0 : U.det ≠ 0 := by rw [hU]; exact one_ne_zero
  refine ⟨Z * U * P, ?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact mul_ne_zero (mul_ne_zero hZ hU0) hPdet0
  · -- adj(Z U P) W = p^{a₁+a₂} • diag(f₁, f₂) V
    have e : (Z * U * P).adjugate * W = (p : ℤ) ^ (a₁ + a₂) • (!![f₁, 0; 0, f₂] * V) := by
      rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc, hX,
        ← Matrix.mul_assoc U.adjugate, ← Matrix.mul_assoc U.adjugate, adjugate_mul, hU, one_smul,
        Matrix.one_mul, ← Matrix.mul_assoc, hPdef, adjugate_fin_two_of]
      rw [← smul_mul]
      congr 1
      rw [hf₁, hf₂]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, pow_add] <;> ring
    have hf : ¬ (p : ℤ) ∣ (!![f₁, 0; 0, f₂] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [det_fin_two_of, mul_zero, sub_zero]
      exact fun h => (Int.Prime.dvd_mul' hp.out h).elim hf₁p hf₂p
    have hVp := not_dvd_det_of_det_eq_one (p := p) hV
    rw [dd, e, dist_smul (pow_ne_zero _ hp0) (det_mul_ne_zero (det_ne_zero_of_not_dvd hf)
      (det_ne_zero_of_not_dvd hVp)), dist_mul_unit hVp (det_ne_zero_of_not_dvd hf),
      dist_eq_zero_of_not_dvd hf]
  · intro q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    have e : Z.adjugate * (Z * U * P) = Z.det • (U * P) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Z.adjugate, adjugate_mul, smul_mul, Matrix.one_mul]
    have hPq : ¬ (q : ℤ) ∣ P.det := by
      rw [hPdet]
      intro h
      have := Int.Prime.dvd_pow' hq h
      norm_cast at this
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 this)
    rw [dd, e, dist_smul hZ (det_mul_ne_zero hU0 hPdet0),
      dist_unit_mul (not_dvd_det_of_det_eq_one hU) hPdet0, dist_eq_zero_of_not_dvd hPq]

omit hp in
/-- Move Z₀ to W p at every p ∈ P, without moving it at the primes outside P. -/
theorem exists_glue (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (W : ℕ → Matrix (Fin 2) (Fin 2) ℤ)
    (hW : ∀ p ∈ P, (W p).det ≠ 0) {Z₀ : Matrix (Fin 2) (Fin 2) ℤ} (hZ₀ : Z₀.det ≠ 0) :
    ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, Z.det ≠ 0 ∧ (∀ p ∈ P, dd p Z (W p) = 0) ∧
      ∀ q, q.Prime → q ∉ P → dd q Z₀ Z = 0 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    exact ⟨Z₀, hZ₀, by simp, fun q hq _ => by have : Fact q.Prime := ⟨hq⟩; exact dd_self hZ₀⟩
  | insert p P hpP ih =>
    obtain ⟨Z, hZ, h1, h2⟩ := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
      (fun q hq => hW q (Finset.mem_insert_of_mem hq))
    have hpp := hP p (Finset.mem_insert_self p P)
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨Z', hZ', h3, h4⟩ := exists_glue_one (p := p) hZ (hW p (Finset.mem_insert_self p P))
    refine ⟨Z', hZ', ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact h3
      · have hqp : q ≠ p := fun h => hpP (h ▸ hq)
        have hqq := hP q (Finset.mem_insert_of_mem hq)
        have : Fact q.Prime := ⟨hqq⟩
        have := dd_triangle (p := q) hZ' hZ (hW q (Finset.mem_insert_of_mem hq))
        rw [dd_comm hZ' hZ, h4 q hqq hqp, h1 q hq] at this
        omega
    · intro q hq hqP
      have : Fact q.Prime := ⟨hq⟩
      have hqp : q ≠ p := fun h => hqP (h ▸ Finset.mem_insert_self p P)
      have := dd_triangle (p := q) hZ₀ hZ hZ'
      rw [h2 q hq (fun h => hqP (Finset.mem_insert_of_mem h)), h4 q hq hqp] at this
      omega

/-! ### The Atkin–Lehner shape -/

omit hp in
theorem vc_eq_zero_of_cont_eq_one {Y : Matrix (Fin 2) (Fin 2) ℤ} (h : cont Y = 1) : vc p Y = 0 := by
  simp [vc, h]

theorem dvd_entries_of_dist_eq_zero {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) (h : dist p M = 0)
    (hd : (p : ℤ) ∣ M.det) : ∀ i j, (p : ℤ) ∣ M i j := by
  have h1 : 1 ≤ vd p M := (pow_dvd_det_iff hM).1 (by simpa using hd)
  have h2 : 1 ≤ vc p M := by
    simp only [dist] at h
    omega
  have := (pow_dvd_iff_le_vc hM (k := 1)).2 h2
  simpa using this

theorem not_dvd_det_of_dist_eq_zero {Y : Matrix (Fin 2) (Fin 2) ℤ} (hY : Y.det ≠ 0) (hprim : cont Y = 1)
    (h : dist p Y = 0) : ¬ (p : ℤ) ∣ Y.det := by
  intro hd
  have h1 : 1 ≤ vd p Y := (pow_dvd_det_iff hY).1 (by simpa using hd)
  simp only [dist, vc_eq_zero_of_cont_eq_one hprim] at h
  omega

theorem not_dvd_all_of_cont_eq_one {Y : Matrix (Fin 2) (Fin 2) ℤ} (hprim : cont Y = 1)
    (h : ∀ i j, (p : ℤ) ∣ Y i j) : False := by
  have := dvd_cont_iff.2 h
  rw [hprim] at this
  norm_cast at this
  exact hp.out.not_dvd_one this

/-- The facts at one prime p ∣ N. -/
theorem local_shape {N : ℕ} (hN : Squarefree N) (hpN : p ∣ N) {Y : Matrix (Fin 2) (Fin 2) ℤ}
    (hY : Y.det ≠ 0) (hprim : cont Y = 1) (h : PresE p 1 (diagN N) Y) :
    (p : ℤ) ∣ Y 1 0 ∧ (¬ (p : ℤ) ∣ Y.det ∨
      ((p : ℤ) ∣ Y 0 0 ∧ (p : ℤ) ∣ Y 1 1 ∧ vd p Y = 1)) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne_zero
  have hvN : padicValInt p N = 1 := by
    rw [padicValInt, Int.natAbs_natCast]
    exact padicValNat_eq_one_of_squarefree hN hp.out hpN
  have hpN' : (p : ℤ) ∣ N := by exact_mod_cast hpN
  have hD : (diagN N).adjugate = !![(N : ℤ), 0; 0, 1] := by
    rw [diagN, adjugate_fin_two_of]; simp
  unfold PresE at h
  simp only [Matrix.mul_one, dd_one_left] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- fix
    refine ⟨?_, Or.inl (not_dvd_det_of_dist_eq_zero hY hprim h1)⟩
    set M := (diagN N).adjugate * (Y * diagN N) with hM
    have hMdet : M.det = (N : ℤ) ^ 2 * Y.det := by
      rw [hM, det_mul, det_mul, det_adjugate', det_diagN]; ring
    have hM0 : M.det ≠ 0 := by rw [hMdet]; exact mul_ne_zero (pow_ne_zero _ hN0) hY
    have := dvd_entries_of_dist_eq_zero hM0 h2 (by rw [hMdet]; exact (dvd_pow hpN' two_ne_zero).mul_right _) 1 0
    have e : M 1 0 = Y 1 0 := by simp [hM, hD, diagN, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    rwa [e] at this
  · -- swap
    set M₁ := (diagN N).adjugate * Y with hM₁
    set M₂ := Y * diagN N with hM₂
    have hM₁det : M₁.det = N * Y.det := by rw [hM₁, det_mul, det_adjugate', det_diagN]
    have hM₂det : M₂.det = Y.det * N := by rw [hM₂, det_mul, det_diagN]
    have hM₁0 : M₁.det ≠ 0 := by rw [hM₁det]; exact mul_ne_zero hN0 hY
    have hM₂0 : M₂.det ≠ 0 := by rw [hM₂det]; exact mul_ne_zero hY hN0
    have d₁ := dvd_entries_of_dist_eq_zero hM₁0 h1 (by rw [hM₁det]; exact hpN'.mul_right _)
    have d₂ := dvd_entries_of_dist_eq_zero hM₂0 h2 (by rw [hM₂det]; exact hpN'.mul_left _)
    have e10 : M₁ 1 0 = Y 1 0 := by simp [hM₁, hD, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    have e11 : M₁ 1 1 = Y 1 1 := by simp [hM₁, hD, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    have e01 : M₁ 0 1 = N * Y 0 1 := by simp [hM₁, hD, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    have f00 : M₂ 0 0 = Y 0 0 := by simp [hM₂, diagN, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
    have h10 := d₁ 1 0
    have h11 := d₁ 1 1
    have h00 := d₂ 0 0
    rw [e10] at h10
    rw [e11] at h11
    rw [f00] at h00
    refine ⟨h10, Or.inr ⟨h00, h11, ?_⟩⟩
    -- v_p(det Y) = 1
    have hvd₁ : vd p M₁ = 1 + vd p Y := by
      rw [vd, hM₁det, padicValInt.mul hN0 hY, hvN, vd]
    have hdist : dist p M₁ = 0 := h1
    simp only [dist, hvd₁] at hdist
    have hc := two_vc_le_vd (p := p) hM₁0
    rw [hvd₁] at hc
    -- p ∤ Y 0 1, since Y is primitive
    have h01 : ¬ (p : ℤ) ∣ Y 0 1 := by
      intro h01
      apply not_dvd_all_of_cont_eq_one (p := p) hprim
      intro i j
      fin_cases i <;> fin_cases j
      · exact h00
      · exact h01
      · exact h10
      · exact h11
    by_contra hne
    have hge : 2 ≤ vc p M₁ := by omega
    have := (pow_dvd_iff_le_vc hM₁0 (k := 2)).2 hge 0 1
    rw [e01] at this
    apply h01
    have hY01 : Y 0 1 ≠ 0 := fun h0 => h01 (h0 ▸ dvd_zero _)
    have hv := ((padicValInt_dvd_iff 2 _).1 this).resolve_left (mul_ne_zero hN0 hY01)
    rw [padicValInt.mul hN0 hY01, hvN] at hv
    have := (padicValInt_dvd_iff (p := p) 1 (Y 0 1)).2 (Or.inr (by omega))
    simpa using this

omit hp in
/-- **The Atkin–Lehner shape.** -/
theorem al_shape {N : ℕ} (hN : Squarefree N) {Y : Matrix (Fin 2) (Fin 2) ℤ} (hpos : 0 < Y.det)
    (hprim : cont Y = 1) (hfix : ∀ p, (hp : p.Prime) → ¬ p ∣ N → @dist p Y = 0)
    (hedge : ∀ p, p.Prime → p ∣ N → PresE p 1 (diagN N) Y) :
    ∃ e : ℕ, e ∣ N ∧ ∃ x y z w : ℤ, (e : ℤ) ^ 2 * x * w - N * y * z = e ∧
      Y = !![(e : ℤ) * x, y; N * z, e * w] := by
  have hY : Y.det ≠ 0 := hpos.ne'
  set e := Y.det.natAbs with he
  have hee : (e : ℤ) = Y.det := Int.natAbs_of_nonneg hpos.le
  have he0 : e ≠ 0 := by rw [he]; exact Int.natAbs_ne_zero.2 hY
  -- the primes of e
  have F1 : ∀ q, q.Prime → q ∣ e → q ∣ N ∧ (q : ℤ) ∣ Y 0 0 ∧ (q : ℤ) ∣ Y 1 1 ∧ padicValNat q e = 1 := by
    intro q hq hqe
    have : Fact q.Prime := ⟨hq⟩
    have hqd : (q : ℤ) ∣ Y.det := by rw [← hee]; exact_mod_cast hqe
    have hqN : q ∣ N := by
      by_contra hqN
      exact not_dvd_det_of_dist_eq_zero hY hprim (hfix q hq hqN) hqd
    obtain ⟨-, h | ⟨h1, h2, h3⟩⟩ := local_shape (p := q) hN hqN hY hprim (hedge q hq hqN)
    · exact absurd hqd h
    · exact ⟨hqN, h1, h2, by rw [vd, padicValInt, ← he] at h3; exact h3⟩
  have F2 : ∀ q, q.Prime → q ∣ N → (q : ℤ) ∣ Y 1 0 := fun q hq hqN => by
    have : Fact q.Prime := ⟨hq⟩
    exact (local_shape (p := q) hN hqN hY hprim (hedge q hq hqN)).1
  have hesq : Squarefree e := by
    rw [Nat.squarefree_iff_factorization_le_one he0]
    intro q
    by_cases hq : q.Prime
    · rw [Nat.factorization_def e hq]
      by_cases hqe : q ∣ e
      · rw [(F1 q hq hqe).2.2.2]
      · rw [padicValNat.eq_zero_of_not_dvd hqe]; omega
    · simp [Nat.factorization_eq_zero_of_not_prime e hq]
  have heN : e ∣ N := by
    have := dvd_of_squarefree hesq (x := N) fun q hq hqe => by exact_mod_cast (F1 q hq hqe).1
    exact_mod_cast this
  have h00 : (e : ℤ) ∣ Y 0 0 := dvd_of_squarefree hesq fun q hq hqe => (F1 q hq hqe).2.1
  have h11 : (e : ℤ) ∣ Y 1 1 := dvd_of_squarefree hesq fun q hq hqe => (F1 q hq hqe).2.2.1
  have h10 : (N : ℤ) ∣ Y 1 0 := dvd_of_squarefree hN F2
  obtain ⟨x, hx⟩ := h00
  obtain ⟨w, hw⟩ := h11
  obtain ⟨z, hz⟩ := h10
  refine ⟨e, heN, x, Y 0 1, z, w, ?_, ?_⟩
  · have hdet : Y.det = (e : ℤ) * x * ((e : ℤ) * w) - Y 0 1 * ((N : ℤ) * z) := by
      rw [det_fin_two, hx, hw, hz]
    linear_combination -hee - hdet
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hx, hw, hz]

/-! ### Fixed points of unipotent matrices -/

theorem pow_dvd_of_dd_eq_zero {X R : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) (hR : R.det = 1)
    (h : dd p X (R * X) = 0) : ∀ i j, (p : ℤ) ^ vd p X ∣ (X.adjugate * (R * X)) i j := by
  have hR0 : R.det ≠ 0 := by rw [hR]; exact one_ne_zero
  have hM : (X.adjugate * (R * X)).det ≠ 0 :=
    det_mul_ne_zero (det_adjugate_ne_zero hX) (det_mul_ne_zero hR0 hX)
  have hvd : vd p (X.adjugate * (R * X)) = 2 * vd p X := by
    rw [vd_mul (det_adjugate_ne_zero hX) (det_mul_ne_zero hR0 hX), vd_mul hR0 hX, vd_adjugate]
    simp [vd, hR]
    ring
  have hc := two_vc_le_vd (p := p) hM
  rw [dd, dist, hvd] at h
  rw [hvd] at hc
  exact (pow_dvd_iff_le_vc hM).2 (by omega)

theorem pow_dvd_of_pow_dvd_mul_sq {k a : ℤ} (hk : k ≠ 0) {j t : ℕ} (h : (p : ℤ) ^ j ∣ k * a ^ 2)
    (hj : padicValInt p k + 2 * t ≤ j + 1) : (p : ℤ) ^ t ∣ a := by
  by_cases ha : a = 0
  · rw [ha]; exact dvd_zero _
  have hka : k * a ^ 2 ≠ 0 := mul_ne_zero hk (pow_ne_zero _ ha)
  have h1 := ((padicValInt_dvd_iff j _).1 h).resolve_left hka
  rw [padicValInt.mul hk (pow_ne_zero _ ha), pow_two, padicValInt.mul ha ha] at h1
  exact (padicValInt_dvd_iff t a).2 (Or.inr (by omega))

/-- If [[1, k], [0, 1]] and [[1, 0], [m, 1]] fix the vertex X, then v_p(det X) ≤ v_p(k) + 2b and
v_p(det X) ≤ v_p(m) + 2a, where a, b are the valuations of the rows of X. -/
theorem fix_bound {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) {k m : ℤ} (hk : k ≠ 0) (hm : m ≠ 0)
    (h₁ : dd p X (upM k * X) = 0) (h₂ : dd p X (loM m * X) = 0) :
    vd p X ≤ padicValInt p k + 2 * vb p X ∧ vd p X ≤ padicValInt p m + 2 * va p X := by
  have d₁ := pow_dvd_of_dd_eq_zero hX (det_upT k) h₁
  have d₂ := pow_dvd_of_dd_eq_zero hX (det_loT m) h₂
  have e01 : (X.adjugate * (upM k * X)) 0 1 = k * X 1 1 ^ 2 := by
    simp [upM, adjugate_fin_two, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; ring
  have e10 : (X.adjugate * (upM k * X)) 1 0 = -(k * X 1 0 ^ 2) := by
    simp [upM, adjugate_fin_two, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; ring
  have f01 : (X.adjugate * (loM m * X)) 0 1 = -(m * X 0 1 ^ 2) := by
    simp [loM, adjugate_fin_two, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; ring
  have f10 : (X.adjugate * (loM m * X)) 1 0 = m * X 0 0 ^ 2 := by
    simp [loM, adjugate_fin_two, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; ring
  have a1 := d₁ 0 1
  have a2 := d₁ 1 0
  have b1 := d₂ 0 1
  have b2 := d₂ 1 0
  rw [e01] at a1
  rw [e10, dvd_neg] at a2
  rw [f01, dvd_neg] at b1
  rw [f10] at b2
  constructor
  · by_contra hlt
    push Not at hlt
    have := (pow_dvd_row1_iff (p := p) hX (k := vb p X + 1)).1
      ⟨pow_dvd_of_pow_dvd_mul_sq hk a2 (by omega), pow_dvd_of_pow_dvd_mul_sq hk a1 (by omega)⟩
    omega
  · by_contra hlt
    push Not at hlt
    have := (pow_dvd_row0_iff (p := p) hX (k := va p X + 1)).1
      ⟨pow_dvd_of_pow_dvd_mul_sq hm b2 (by omega), pow_dvd_of_pow_dvd_mul_sq hm b1 (by omega)⟩
    omega

theorem vc_eq_min {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) : vc p X = min (va p X) (vb p X) := by
  have := vc_diagP_mul (p := p) 0 hX
  rwa [diagP_zero, Matrix.one_mul, zero_add] at this

/-- A vertex fixed by [[1, k], [0, 1]] and [[1, 0], [k, 1]] is within distance v_p(k) of the vertex 1. -/
theorem dist_le_of_fix {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0) {k : ℤ} (hk : k ≠ 0)
    (h₁ : dd p X (upM k * X) = 0) (h₂ : dd p X (loM k * X) = 0) : dist p X ≤ padicValInt p k := by
  obtain ⟨b1, b2⟩ := fix_bound hX hk hk h₁ h₂
  rw [dist, vc_eq_min hX]
  omega

/-- A vertex fixed by [[1, 1], [0, 1]] and [[1, 0], [N, 1]] (N squarefree) is 1, or diag(1, N) if p ∣ N. -/
theorem dd_eq_zero_of_fix {N : ℕ} (hN : Squarefree N) {X : Matrix (Fin 2) (Fin 2) ℤ} (hX : X.det ≠ 0)
    (h₁ : dd p X (upM 1 * X) = 0) (h₂ : dd p X (loM N * X) = 0) :
    dd p 1 X = 0 ∨ (p ∣ N ∧ dd p (diagN N) X = 0) := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne_zero
  obtain ⟨b1, b2⟩ := fix_bound hX one_ne_zero hN0 h₁ h₂
  have hab := va_add_vb_le (p := p) hX
  rw [padicValInt.one] at b1
  rw [dd_one_left, dist, vc_eq_min hX]
  by_cases hpN : p ∣ N
  · have hvN : padicValInt p N = 1 := by
      rw [padicValInt, Int.natAbs_natCast]
      exact padicValNat_eq_one_of_squarefree hN hp.out hpN
    rw [hvN] at b2
    by_cases hle : vb p X ≤ va p X
    · left; omega
    · right
      refine ⟨hpN, ?_⟩
      obtain ⟨N', hN'⟩ := hpN
      have hpN' : ¬ (p : ℤ) ∣ N' := by
        intro h
        have : p * p ∣ N := by rw [hN']; exact Nat.mul_dvd_mul_left p (by exact_mod_cast h)
        exact hp.out.one_lt.ne' (Nat.isUnit_iff.1 (hN p this))
      have e : (diagN N).adjugate = !![(N' : ℤ), 0; 0, 1] * diagP p 1 := by
        rw [diagN, adjugate_fin_two_of, diagP, hN']
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
        ring
      have hu : ¬ (p : ℤ) ∣ (!![(N' : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa using hpN'
      rw [dd, e, Matrix.mul_assoc, dist_unit_mul hu (det_diagP_mul_ne_zero 1 hX), dist_diagP_mul 1 hX]
      omega
  · have hvN : padicValInt p N = 0 := padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hpN)
    rw [hvN] at b2
    left
    omega

end NormalizerLean.Helling
