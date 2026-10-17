module

public import NormalizerLean.T1General

@[expose] public section

/-!
# The algebra of Newman's form (8′)

For g = (ε/√e)·[[ae, b/h], [Nc/h, de]] (Newman data (a, b, c, d, e, ε)):
* `NData.e_unique`: e is determined by g (the integer matrix W = [[ae, b], [nc, de]] is primitive:
  d·(ae) − (cm)·b = 1 where n = em);
* `NData.mul`: the product of (8′)-matrices with e, e' is an (8′)-matrix with e₁f₁, where
  e = e₁q, e' = f₁q, gcd(e₁, f₁) = 1 (the Atkin–Lehner product law);
* `NData.one_of_mem`: elements of Γ₀(N) have e = 1;
* `NData.inv`.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Newman data (8′) for g. -/
def NData (N : ℕ) (g : SL(2, ℝ)) (a b c d : ℤ) (e : ℕ) (ε : ℝ) : Prop :=
  0 < e ∧ e ∣ nPart N ∧ a * d * (e : ℤ) ^ 2 - b * c * (nPart N : ℤ) = e ∧ (ε = 1 ∨ ε = -1) ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (ε / Real.sqrt e) • !![(a : ℝ) * e, (b : ℝ) / hPart N; (N : ℝ) * c / hPart N, (d : ℝ) * e]

theorem isNewmanForm_iff {N : ℕ} {g : SL(2, ℝ)} :
    IsNewmanForm N g ↔ ∃ a b c d e ε, NData N g a b c d e ε := by
  constructor
  · rintro ⟨a, b, c, d, e, h1, h2, h3, ε, h4, h5⟩
    exact ⟨a, b, c, d, e, ε, h1, h2, h3, h4, h5⟩
  · rintro ⟨a, b, c, d, e, ε, h1, h2, h3, h4, h5⟩
    exact ⟨a, b, c, d, e, h1, h2, h3, ε, h4, h5⟩

theorem sqrt_nat_ne_zero {e : ℕ} (he : 0 < e) : Real.sqrt e ≠ 0 :=
  (Real.sqrt_pos.2 (Nat.cast_pos.2 he)).ne'

theorem eps_div_sqrt_ne_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {e : ℕ} (he : 0 < e) :
    ε / Real.sqrt e ≠ 0 := by
  apply div_ne_zero _ (sqrt_nat_ne_zero he)
  rcases hε with rfl | rfl <;> norm_num

/-! ### Uniqueness of e -/

theorem cross_of_prop {κ κ' : ℝ} (hκ : κ ≠ 0) {x y x' y' : ℤ}
    (h1 : κ * x = κ' * x') (h2 : κ * y = κ' * y') : x * y' = y * x' := by
  have : κ * ((x : ℝ) * y') = κ * ((y : ℝ) * x') := by
    calc κ * ((x : ℝ) * y') = (κ * x) * y' := by ring
      _ = κ' * x' * y' := by rw [h1]
      _ = (κ' * y') * x' := by ring
      _ = κ * y * x' := by rw [h2]
      _ = κ * ((y : ℝ) * x') := by ring
  exact_mod_cast mul_left_cancel₀ hκ this

theorem NData.e_unique {N : ℕ} [NeZero N] {g : SL(2, ℝ)} {a b c d a' b' c' d' : ℤ} {e e' : ℕ}
    {ε ε' : ℝ} (h : NData N g a b c d e ε) (h' : NData N g a' b' c' d' e' ε') : e = e' := by
  obtain ⟨he0, ⟨m, hm⟩, hdet, hε, hg⟩ := h
  obtain ⟨he0', ⟨m', hm'⟩, hdet', hε', hg'⟩ := h'
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  set κ := ε / Real.sqrt e
  set κ' := ε' / Real.sqrt e'
  have hκ : κ ≠ 0 := eps_div_sqrt_ne_zero hε he0
  have hM := hg.symm.trans hg'
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, head_cons, smul_eq_mul] at e00 e01 e10 e11
  have E0 : κ * ((a * e : ℤ) : ℝ) = κ' * ((a' * e' : ℤ) : ℝ) := by push_cast; exact e00
  have E1 : κ * (b : ℝ) = κ' * (b' : ℝ) := by
    have := congrArg (· * (hPart N : ℝ)) e01
    field_simp at this
    linarith
  have E2 : κ * (c : ℝ) = κ' * (c' : ℝ) := by
    have := congrArg (· * ((hPart N : ℝ) / N)) e10
    field_simp at this
    linarith
  have E3 : κ * ((d * e : ℤ) : ℝ) = κ' * ((d' * e' : ℤ) : ℝ) := by push_cast; exact e11
  -- Bezout identities d·(ae) − (cm)·b = 1
  have he0z : (e : ℤ) ≠ 0 := Nat.cast_ne_zero.2 he0.ne'
  have he0z' : (e' : ℤ) ≠ 0 := Nat.cast_ne_zero.2 he0'.ne'
  have bez : d * (a * e) - (c * m) * b = 1 := by
    apply mul_left_cancel₀ he0z
    rw [hm] at hdet
    push_cast at hdet
    linear_combination hdet
  have bez' : d' * (a' * e') - (c' * m') * b' = 1 := by
    apply mul_left_cancel₀ he0z'
    rw [hm'] at hdet'
    push_cast at hdet'
    linear_combination hdet'
  -- proportionality
  have c01 := cross_of_prop hκ E0 E1
  have c02 := cross_of_prop hκ E0 E2
  have c03 := cross_of_prop hκ E0 E3
  have c12 := cross_of_prop hκ E1 E2
  have c13 := cross_of_prop hκ E1 E3
  set μ := d' * (a * e) - (c' * m') * b
  set ν := d * (a' * e') - (c * m) * b'
  have hW0 : a * (e : ℤ) = μ * (a' * e') := by
    linear_combination (-(a * (e : ℤ))) * bez' - c' * m' * c01
  have hW1 : b = μ * b' := by linear_combination (-b) * bez' - d' * c01
  have hW2 : c = μ * c' := by linear_combination (-c) * bez' - d' * c02 + c' * m' * c12
  have hW3 : d * (e : ℤ) = μ * (d' * e') := by
    linear_combination (-(d * (e : ℤ))) * bez' - d' * c03 + c' * m' * c13
  have hμν : μ * ν = 1 := by
    calc μ * ν = d * (μ * (a' * e')) - c * m * (μ * b') := by ring
      _ = d * (a * e) - (c * m) * b := by rw [← hW0, ← hW1]
      _ = 1 := bez
  have hμ2 : μ ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hμν with h1 | h1 <;> rw [h1] <;> norm_num
  -- e = det W
  have hdetW : (e : ℤ) = (a * e) * (d * e) - b * c * (nPart N : ℤ) := by linear_combination -hdet
  have hdetW' : (e' : ℤ) = (a' * e') * (d' * e') - b' * c' * (nPart N : ℤ) := by
    linear_combination -hdet'
  have : (e : ℤ) = e' := by
    rw [hdetW, hW0, hW1, hW2, hW3]
    linear_combination (-μ ^ 2) * hdetW' + (e' : ℤ) * hμ2
  exact_mod_cast this

/-! ### Products -/

theorem sqrt_mul_sqrt_eq (e₁ f₁ q : ℕ) :
    Real.sqrt ((e₁ * q : ℕ) : ℝ) * Real.sqrt ((f₁ * q : ℕ) : ℝ) = q * Real.sqrt ((e₁ * f₁ : ℕ) : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), show ((e₁ * q : ℕ) : ℝ) * ((f₁ * q : ℕ) : ℝ) =
    ((e₁ * f₁ : ℕ) : ℝ) * ((q : ℝ) * q) by push_cast; ring, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_mul_self (Nat.cast_nonneg _), mul_comm]

/-- **The product law.** -/
theorem NData.mul {N : ℕ} [NeZero N] {g g' : SL(2, ℝ)} {a b c d a' b' c' d' : ℤ} {e e' : ℕ}
    {ε ε' : ℝ} (h : NData N g a b c d e ε) (h' : NData N g' a' b' c' d' e' ε') :
    ∃ q e₁ f₁ : ℕ, 0 < q ∧ Nat.Coprime e₁ f₁ ∧ e = e₁ * q ∧ e' = f₁ * q ∧
      ∃ a'' b'' c'' d'' : ℤ, NData N (g * g') a'' b'' c'' d'' (e₁ * f₁) (ε * ε') := by
  obtain ⟨he0, he, hdet, hε, hg⟩ := h
  obtain ⟨he0', he', hdet', hε', hg'⟩ := h'
  obtain ⟨q, e₁, f₁, hq0, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left e' he0)
  refine ⟨q, e₁, f₁, hq0, hcop, rfl, rfl, ?_⟩
  obtain ⟨t, ht⟩ := he
  have hft : f₁ ∣ t := by
    have h1 : f₁ * q ∣ e₁ * q * t := ht ▸ he'
    have h2 : f₁ ∣ e₁ * t := by
      rw [show e₁ * q * t = (e₁ * t) * q by ring] at h1
      exact Nat.dvd_of_mul_dvd_mul_right hq0 h1
    exact hcop.symm.dvd_of_dvd_mul_left h2
  obtain ⟨r, rfl⟩ := hft
  have he₁ : 0 < e₁ := Nat.pos_of_mul_pos_right he0
  have hf₁ : 0 < f₁ := Nat.pos_of_mul_pos_right he0'
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hNr : (N : ℝ) = e₁ * q * (f₁ * r) * (hPart N : ℝ) ^ 2 := by
    have h1 : (e₁ * q * (f₁ * r)) * hPart N ^ 2 = N := by rw [← ht]; exact hNnh
    exact_mod_cast h1.symm
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  refine ⟨a * a' * q + b * c' * r, a * b' * e₁ + b * d' * f₁, c * a' * f₁ + d * e₁ * c',
    c * b' * r + d * d' * q, Nat.mul_pos he₁ hf₁, ⟨q * r, by rw [ht]; ring⟩, ?_, ?_, ?_⟩
  · have hq : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
    apply mul_left_cancel₀ (pow_ne_zero 2 hq)
    rw [ht] at hdet hdet' ⊢
    push_cast at hdet hdet' ⊢
    linear_combination (a' * d' * ((f₁ : ℤ) * q) ^ 2 - b' * c' * (e₁ * q * (f₁ * r))) * hdet +
      ((e₁ : ℤ) * q) * hdet'
  · rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
  · rw [Matrix.SpecialLinearGroup.coe_mul, hg, hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hGG : !![(a : ℝ) * ((e₁ * q : ℕ) : ℝ), (b : ℝ) / hPart N;
          (N : ℝ) * c / hPart N, (d : ℝ) * ((e₁ * q : ℕ) : ℝ)] *
        !![(a' : ℝ) * ((f₁ * q : ℕ) : ℝ), (b' : ℝ) / hPart N;
          (N : ℝ) * c' / hPart N, (d' : ℝ) * ((f₁ * q : ℕ) : ℝ)] =
        (q : ℝ) • !![((a * a' * q + b * c' * r : ℤ) : ℝ) * ((e₁ * f₁ : ℕ) : ℝ),
          ((a * b' * e₁ + b * d' * f₁ : ℤ) : ℝ) / hPart N;
          (N : ℝ) * ((c * a' * f₁ + d * e₁ * c' : ℤ) : ℝ) / hPart N,
          ((c * b' * r + d * d' * q : ℤ) : ℝ) * ((e₁ * f₁ : ℕ) : ℝ)] := by
      rw [mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> ring
    rw [hGG, smul_smul]
    congr 1
    have hs := sqrt_mul_sqrt_eq e₁ f₁ q
    have hs1 : Real.sqrt ((e₁ * q : ℕ) : ℝ) ≠ 0 := sqrt_nat_ne_zero (Nat.mul_pos he₁ hq0)
    have hs2 : Real.sqrt ((f₁ * q : ℕ) : ℝ) ≠ 0 := sqrt_nat_ne_zero (Nat.mul_pos hf₁ hq0)
    have hs3 : Real.sqrt ((e₁ * f₁ : ℕ) : ℝ) ≠ 0 := sqrt_nat_ne_zero (Nat.mul_pos he₁ hf₁)
    have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0.ne'
    rw [div_mul_div_comm, div_mul_eq_mul_div, hs, div_eq_div_iff (mul_ne_zero hqr hs3) hs3]
    ring

theorem NData.inv {N : ℕ} {g : SL(2, ℝ)} {a b c d : ℤ} {e : ℕ} {ε : ℝ}
    (h : NData N g a b c d e ε) : NData N g⁻¹ d (-b) (-c) a e ε := by
  obtain ⟨he0, he, hdet, hε, hg⟩ := h
  refine ⟨he0, he, by linear_combination hdet, hε, ?_⟩
  rw [coe_inv_of_coe_eq_smul hg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Elements of Γ₀(N) have Newman data with e = 1. -/
theorem NData.of_mem_Gamma0R {N : ℕ} [NeZero N] {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N) :
    ∃ a b c d : ℤ, NData N γ a b c d 1 1 := by
  obtain ⟨x, y, c', t, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  refine ⟨x, hPart N * y, hPart N * z, t, one_pos, one_dvd _, ?_, Or.inl rfl, ?_⟩
  · have : (N : ℤ) = nPart N * hPart N ^ 2 := by exact_mod_cast hNnh.symm
    rw [this] at hdet
    push_cast
    linear_combination hdet
  · rw [hγm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- For every exact divisor e ∥ n there is an (8′)-element with that e (an Atkin–Lehner element of
level n, conjugated by D). -/
theorem NData.exists_of_exact {N e : ℕ} [NeZero N] (he : e ∣ nPart N)
    (hcop : Nat.Coprime e (nPart N / e)) : ∃ (g : SL(2, ℝ)) (a b c d : ℤ), NData N g a b c d e 1 := by
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N (NeZero.ne N)
    rw [h0, zero_mul] at this
    exact NeZero.ne N this.symm
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact hn0 he)
  obtain ⟨m, hm⟩ := he
  rw [hm, Nat.mul_div_cancel_left _ he0] at hcop
  have hb := Int.gcd_eq_gcd_ab e m
  rw [Int.gcd_natCast_natCast, hcop] at hb
  set x := Int.gcdA e m
  set y := -Int.gcdB e m
  have hdet : x * 1 * (e : ℤ) ^ 2 - y * 1 * (nPart N : ℤ) = e := by
    rw [hm]
    push_cast at hb ⊢
    linear_combination (e : ℤ) * hb.symm
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  have her : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he0.ne'
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    ((1 : ℝ) / Real.sqrt e) • !![(x : ℝ) * e, (y : ℝ) / hPart N; (N : ℝ) * (1 : ℤ) / hPart N,
      ((1 : ℤ) : ℝ) * e]
  have hG : G.det = 1 := by
    simp only [G, det_smul, Fintype.card_fin, det_fin_two_of]
    have hNr : (N : ℝ) = nPart N * (hPart N : ℝ) ^ 2 := by exact_mod_cast hNnh.symm
    have hdr : ((x * 1 * (e : ℤ) ^ 2 - y * 1 * (nPart N : ℤ) : ℤ) : ℝ) = e := by
      exact_mod_cast hdet
    push_cast at hdr
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _), hNr]
    field_simp
    linear_combination hdr
  exact ⟨⟨G, hG⟩, x, y, 1, 1, he0, ⟨m, hm⟩, hdet, Or.inl rfl, rfl⟩

/-! ### The invariant e(g) and the parities σ_p -/

/-- The invariant e of an (8′)-element (well defined by `NData.e_unique`). -/
def eOf (N : ℕ) (g : SL(2, ℝ)) : ℕ := sInf {e | ∃ a b c d ε, NData N g a b c d e ε}

theorem eOf_eq {N : ℕ} [NeZero N] {g : SL(2, ℝ)} {a b c d : ℤ} {e : ℕ} {ε : ℝ}
    (h : NData N g a b c d e ε) : eOf N g = e := by
  have hmem : e ∈ {e | ∃ a b c d ε, NData N g a b c d e ε} := ⟨a, b, c, d, ε, h⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨e, hmem⟩
  rintro e' ⟨a', b', c', d', ε', h'⟩
  exact (NData.e_unique h h').le

/-- Exactness: e ∥ n. -/
theorem NData.coprime {N : ℕ} {g : SL(2, ℝ)} {a b c d : ℤ} {e : ℕ} {ε : ℝ}
    (h : NData N g a b c d e ε) : Nat.Coprime e (nPart N / e) := by
  obtain ⟨he0, ⟨m, hm⟩, hdet, -, -⟩ := h
  rw [hm, Nat.mul_div_cancel_left _ he0]
  have he0z : (e : ℤ) ≠ 0 := Nat.cast_ne_zero.2 he0.ne'
  have h1 : (a * d) * (e : ℤ) + (-(b * c)) * m = 1 := by
    apply mul_left_cancel₀ he0z
    rw [hm] at hdet
    push_cast at hdet
    linear_combination hdet
  have h2 := Int.isCoprime_iff_gcd_eq_one.1 (⟨a * d, -(b * c), h1⟩ : IsCoprime (e : ℤ) (m : ℤ))
  rw [Int.gcd_natCast_natCast] at h2
  exact h2

/-- The parity rule: p ∣ e(gg') iff exactly one of p ∣ e(g), p ∣ e(g'). -/
theorem NData.dvd_eOf_mul_iff {N : ℕ} [NeZero N] {g g' : SL(2, ℝ)} {a b c d a' b' c' d' : ℤ}
    {e e' : ℕ} {ε ε' : ℝ} (h : NData N g a b c d e ε) (h' : NData N g' a' b' c' d' e' ε')
    {p : ℕ} (hp : p.Prime) : p ∣ eOf N (g * g') ↔ ¬ (p ∣ e ↔ p ∣ e') := by
  have hcop := h.coprime
  have hcop' := h'.coprime
  have he := h.2.1
  have he' := h'.2.1
  obtain ⟨q, e₁, f₁, hq0, hc, rfl, rfl, a'', b'', c'', d'', h''⟩ := h.mul h'
  rw [eOf_eq h'']
  -- n = e₁ q f₁ r
  obtain ⟨t, ht⟩ := he
  have hft : f₁ ∣ t := by
    have h1 : f₁ * q ∣ e₁ * q * t := ht ▸ he'
    have h2 : f₁ ∣ e₁ * t := by
      rw [show e₁ * q * t = (e₁ * t) * q by ring] at h1
      exact Nat.dvd_of_mul_dvd_mul_right hq0 h1
    exact hc.symm.dvd_of_dvd_mul_left h2
  obtain ⟨r, rfl⟩ := hft
  have hn1 : nPart N / (e₁ * q) = f₁ * r := by rw [ht, Nat.mul_div_cancel_left _ (by
    have := h.1; omega)]
  have hn2 : nPart N / (f₁ * q) = e₁ * r := by
    rw [ht, show e₁ * q * (f₁ * r) = f₁ * q * (e₁ * r) by ring,
      Nat.mul_div_cancel_left _ (by have := h'.1; omega)]
  rw [hn1] at hcop
  rw [hn2] at hcop'
  by_cases hpq : p ∣ q
  · -- p divides both e and e'; then p ∤ e₁ f₁
    have h1 : p ∣ e₁ * q := dvd_mul_of_dvd_right hpq _
    have h2 : p ∣ f₁ * q := dvd_mul_of_dvd_right hpq _
    simp only [h1, h2, not_true_eq_false, iff_false]
    intro hpe
    rcases (Nat.Prime.dvd_mul hp).1 hpe with hp1 | hp1
    · refine hp.one_lt.ne' (Nat.dvd_one.1 ?_)
      rw [← Nat.Coprime.gcd_eq_one hcop']
      exact Nat.dvd_gcd h2 (dvd_mul_of_dvd_left hp1 _)
    · refine hp.one_lt.ne' (Nat.dvd_one.1 ?_)
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 (dvd_mul_of_dvd_left hp1 _)
  · have h1 : p ∣ e₁ * q ↔ p ∣ e₁ := by
      rw [Nat.Prime.dvd_mul hp]; simp [hpq]
    have h2 : p ∣ f₁ * q ↔ p ∣ f₁ := by
      rw [Nat.Prime.dvd_mul hp]; simp [hpq]
    rw [h1, h2, Nat.Prime.dvd_mul hp]
    have : ¬ (p ∣ e₁ ∧ p ∣ f₁) := fun ⟨u, v⟩ => by
      refine hp.one_lt.ne' (Nat.dvd_one.1 ?_)
      rw [← Nat.Coprime.gcd_eq_one hc]
      exact Nat.dvd_gcd u v
    tauto

/-- Elements with e = 1 lie in D⁻¹Γ₀(n)D. -/
theorem NData.mem_conjGamma0n {N : ℕ} [NeZero N] {g : SL(2, ℝ)} {a b c d : ℤ} {ε : ℝ}
    (h : NData N g a b c d 1 ε) : g ∈ conjGamma0n N := by
  obtain ⟨-, -, hdet, hε, hg⟩ := h
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ε = s := by
    rcases hε with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  have hNr : (N : ℝ) = nPart N * (hPart N : ℝ) ^ 2 := by exact_mod_cast hNnh.symm
  let γ : SL(2, ℝ) := ⟨!![((s * a : ℤ) : ℝ), ((s * b : ℤ) : ℝ); ((s * (nPart N * c) : ℤ) : ℝ),
      ((s * d : ℤ) : ℝ)], by
    rw [det_fin_two_of]
    have hdet1 : a * d - b * c * (nPart N : ℤ) = 1 := by simpa using hdet
    have : ((s * a * (s * d) - s * b * (s * (nPart N * c)) : ℤ) : ℝ) = 1 := by
      have : s * a * (s * d) - s * b * (s * (nPart N * c)) = 1 := by
        linear_combination (s * s) * hdet1 + hs2
      exact_mod_cast this
    push_cast at this ⊢
    linear_combination this⟩
  have hγ : γ ∈ Gamma0R (nPart N) :=
    mem_Gamma0R_of_entries _ _ _ _ rfl ⟨s * c, by ring⟩
  refine ⟨γ, hγ, ?_⟩
  have hD := coe_Dsl N
  have hDinv := coe_inv_of_coe_eq_smul hD
  have hsq' : Real.sqrt (hPart N) * Real.sqrt (hPart N) = hPart N :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hsq : (Real.sqrt (hPart N))⁻¹ * (Real.sqrt (hPart N))⁻¹ * (hPart N : ℝ) = 1 := by
    rw [← mul_inv, hsq', inv_mul_cancel₀ hhr]
  ext i j
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDinv, hD, hg]
  rw [smul_mul_mul_smul_eq_of hsq (X := (s : ℝ) • !![(a : ℝ), b / hPart N;
    nPart N * c * hPart N, d])]
  · fin_cases i <;> fin_cases j <;> simp [hNr] <;> (try field_simp) <;> (try ring_nf) <;> (try simp)
  · rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end

end NormalizerLean
