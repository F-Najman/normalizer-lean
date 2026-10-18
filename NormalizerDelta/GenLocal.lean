module

public import NormalizerDelta.GenBasic

@[expose] public section

/-!
# General modular curves: §B, local restrictions on the determinant (DLM26, Prop. 4.5)

Let m be an integer matrix with det m > 0, not divisible by p, such that projSL m normalizes Γ_H.
* (1) The lattice argument mod q = p^k: if an entry m_ij is a unit mod q and q ∣ det m, both columns of m are
  multiples mod q of the unimodular column j; and γ m = m γ' shows that γ mod q fixes that line
  (`invariant_line_mod`).  Since p^k ∣ N (`pow_dvd_of_dvd_det`), reduction mod N followed by `ZMod.cast` is
  reduction mod p^k, so H mod p^k fixes the line.
* (2) If H mod p fixes only the line through (1, 0), the column spans of m and of adj m mod p are that line.
* (4) Conjugate the split Cartan to the diagonal by σ ∈ SL₂(ℤ); for m' = σ⁻¹mσ the conjugates
  m' [[1, N], [0, 1]] m'⁻¹ and m' [[1, 0], [N, 1]] m'⁻¹ are diagonal mod p^k, so p^k det m ∣ N m'_ij².
-/

open Matrix MatrixGroups

-- As in `CartanNonsplit.lean`: Mathlib v4.35.0-rc3's instance making `ZMod p` an `AddCommGroup` breaks `simp` on
-- subtractions.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace NormalizerLean

noncomputable section

/-! ### The lattice argument modulo q -/

theorem rel_entry {q : ℕ} {m γ γ' : Matrix (Fin 2) (Fin 2) ℤ} (h : γ * m = m * γ') (r k : Fin 2) :
    ((γ r 0 : ℤ) : ZMod q) * (m 0 k : ℤ) + (γ r 1 : ℤ) * (m 1 k : ℤ) =
      (m r 0 : ℤ) * (γ' 0 k : ℤ) + (m r 1 : ℤ) * (γ' 1 k : ℤ) := by
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => ((M r k : ℤ) : ZMod q)) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
  push_cast at this
  exact this

/-- The lattice argument, column 0. -/
theorem invariant_line_mod_col0 {q : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet' : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - (m 0 1 : ℤ) * (m 1 0 : ℤ) = 0)
    {i : Fin 2} {u : ℤ} (hu : (u : ZMod q) * (m i 0 : ℤ) = 1) :
    ∃ v : Fin 2 → ZMod q, (∃ a b : ZMod q, a * v 0 + b * v 1 = 1) ∧
      (∀ k : Fin 2, ∃ c : ZMod q, ∀ r : Fin 2, ((m r k : ℤ) : ZMod q) = c * v r) ∧
      ∀ γ γ' : Matrix (Fin 2) (Fin 2) ℤ, γ * m = m * γ' →
        ∃ c : ZMod q, (γ.map (Int.cast : ℤ → ZMod q)) *ᵥ v = c • v := by
  set c₀ : ZMod q := (u : ZMod q) * (m i 1 : ℤ) with hc₀
  have hcol : ∀ r : Fin 2, ((m r 1 : ℤ) : ZMod q) = c₀ * (m r 0 : ℤ) := by
    rw [Fin.forall_fin_two, hc₀]
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · exact ⟨by linear_combination (-((m 0 1 : ℤ) : ZMod q)) * hu,
        by linear_combination (-((m 1 1 : ℤ) : ZMod q)) * hu + (u : ZMod q) * hdet'⟩
    · exact ⟨by linear_combination (-((m 0 1 : ℤ) : ZMod q)) * hu - (u : ZMod q) * hdet',
        by linear_combination (-((m 1 1 : ℤ) : ZMod q)) * hu⟩
  refine ⟨fun r => ((m r 0 : ℤ) : ZMod q), ?_, ?_, ?_⟩
  · rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · exact ⟨u, 0, by simpa using hu⟩
    · exact ⟨0, u, by simpa using hu⟩
  · rw [Fin.forall_fin_two]
    exact ⟨⟨1, fun r => (one_mul _).symm⟩, ⟨c₀, hcol⟩⟩
  · intro γ γ' h
    refine ⟨(γ' 0 0 : ZMod q) + c₀ * (γ' 1 0 : ZMod q), ?_⟩
    ext r
    have e := rel_entry (q := q) h r 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, hcol r]; ring

/-- The lattice argument mod q: if an entry of m is a unit mod q and q ∣ det m, some unimodular v ∈ (ℤ/q)²
spans both columns of m mod q, and γ v ∈ (ℤ/q) v whenever γ m = m γ'. -/
theorem invariant_line_mod {q : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : (q : ℤ) ∣ m.det)
    (hunit : ∃ i j : Fin 2, ∃ u : ℤ, (u : ZMod q) * (m i j : ℤ) = 1) :
    ∃ v : Fin 2 → ZMod q, (∃ a b : ZMod q, a * v 0 + b * v 1 = 1) ∧
      (∀ k : Fin 2, ∃ c : ZMod q, ∀ r : Fin 2, ((m r k : ℤ) : ZMod q) = c * v r) ∧
      ∀ γ γ' : Matrix (Fin 2) (Fin 2) ℤ, γ * m = m * γ' →
        ∃ c : ZMod q, (γ.map (Int.cast : ℤ → ZMod q)) *ᵥ v = c • v := by
  obtain ⟨i, j, u, hu⟩ := hunit
  have hdet' : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - (m 0 1 : ℤ) * (m 1 0 : ℤ) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdet
    rw [det_fin_two] at this; push_cast at this; exact this
  rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
  · exact invariant_line_mod_col0 hdet' hu
  · -- swap the columns: m' = m S, S = [[0, 1], [1, 0]]
    set S : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0] with hS
    have hSS : S * S = 1 := by rw [hS]; ext a b; fin_cases a <;> fin_cases b <;> simp
    have hm' : ∀ r, (m * S) r 0 = m r 1 ∧ (m * S) r 1 = m r 0 := fun r => by
      simp [hS, Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨v, hv, hcols, hinv⟩ := invariant_line_mod_col0 (m := m * S) (i := i) (u := u)
      (by rw [(hm' 0).1, (hm' 0).2, (hm' 1).1, (hm' 1).2]; linear_combination -hdet')
      (by rw [(hm' i).1]; exact hu)
    refine ⟨v, hv, ?_, fun γ γ' h => hinv γ (S * γ' * S) ?_⟩
    · rw [Fin.forall_fin_two]
      obtain ⟨c0, hc0⟩ := hcols 1
      obtain ⟨c1, hc1⟩ := hcols 0
      exact ⟨⟨c0, fun r => by rw [← hc0 r, (hm' r).2]⟩, ⟨c1, fun r => by rw [← hc1 r, (hm' r).1]⟩⟩
    · rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc S (S * γ'),
        ← Matrix.mul_assoc S S, hSS, Matrix.one_mul]

/-! ### Reduction and units -/

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

/-- Reduction mod N followed by `ZMod.cast` is reduction mod q, for q ∣ N. -/
theorem map_cast_redSL {N q : ℕ} (hq : q ∣ N) (γ : SL(2, ℤ)) :
    ((redSL N γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ZMod q) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, ZMod.cast_intCast hq]

theorem exists_inv_mod {q : ℕ} {x : ℤ} (h : IsCoprime (q : ℤ) x) : ∃ u : ℤ, (u : ZMod q) * (x : ZMod q) = 1 := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨b, ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod q) hab
  push_cast at this
  rwa [ZMod.natCast_self, mul_zero, zero_add] at this

theorem isCoprime_natCast_pow {p k : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    IsCoprime ((p ^ k : ℕ) : ℤ) x := by
  have := isCoprime_pow_of_not_dvd hp hx k 1
  rw [pow_one] at this; exact_mod_cast this

theorem isCoprime_natCast_prime {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) : IsCoprime (p : ℤ) x :=
  (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp)).2 hx

/-- The line of the lattice argument is fixed by H mod q. -/
theorem fixesLine_of_lattice {N q : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hD : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H))) (hqN : q ∣ N)
    {v : Fin 2 → ZMod q}
    (hinv : ∀ γ γ' : Matrix (Fin 2) (Fin 2) ℤ, γ * m = m * γ' →
      ∃ c : ZMod q, (γ.map (Int.cast : ℤ → ZMod q)) *ᵥ v = c • v) :
    FixesLine H q v := by
  intro h hh
  obtain ⟨γ, rfl⟩ := redSL_surjective N h
  obtain ⟨γ', -, hrel⟩ := exists_rel_right hD hg (show γ ∈ GammaH N H from hh)
  rw [map_cast_redSL hqN]
  exact hinv _ _ hrel

/-! ### Prop. 4.5(1) -/

theorem isBorelMod_of_dvd_det' {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p k : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j) (hk : (p : ℤ) ^ k ∣ m.det) :
    IsBorelMod H (p ^ k) := by
  have hpk : p ^ k ∣ N := pow_dvd_of_dvd_det (Gamma_le_GammaH N H) hdet hg hp hprim hk
  obtain ⟨i, j, hij⟩ := hprim
  obtain ⟨u, hu⟩ := exists_inv_mod (isCoprime_natCast_pow (k := k) hp hij)
  obtain ⟨v, hv, -, hinv⟩ := invariant_line_mod (q := p ^ k) (by push_cast; exact hk) ⟨i, j, u, hu⟩
  exact ⟨v, hv, fixesLine_of_lattice hdet hg hpk hinv⟩

/-! ### Prop. 4.5(2) -/

theorem row_one_dvd {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hB : FixesLine H p ![1, 0]) (hns : ¬ IsSplitMod H p) (hpd : (p : ℤ) ∣ m.det) :
    (p : ℤ) ∣ m 1 0 ∧ (p : ℤ) ∣ m 1 1 := by
  have := Fact.mk hp
  have hpN : p ∣ N := by
    have := pow_dvd_of_dvd_det (Gamma_le_GammaH N H) hdet hg hp hprim (k := 1) (by rwa [pow_one])
    rwa [pow_one] at this
  obtain ⟨i, j, hij⟩ := hprim
  obtain ⟨u, hu⟩ := exists_inv_mod (isCoprime_natCast_prime hp hij)
  obtain ⟨v, -, hcols, hinv⟩ := invariant_line_mod (q := p) hpd ⟨i, j, u, hu⟩
  have hfix := fixesLine_of_lattice hdet hg hpN hinv
  have hv1 : v 1 = 0 := by
    by_contra hne
    apply hns
    refine ⟨![1, 0], v, hB, hfix, ?_⟩
    simpa using (Ne.isUnit hne)
  obtain ⟨c0, hc0⟩ := hcols 0
  obtain ⟨c1, hc1⟩ := hcols 1
  have e0 := hc0 1
  have e1 := hc1 1
  rw [hv1, mul_zero] at e0 e1
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e0, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e1⟩

theorem borel_shape' {N : ℕ} (hN0 : NeZero N) {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hB : FixesLine H p ![1, 0]) (hns : ¬ IsSplitMod H p) (hpd : (p : ℤ) ∣ m.det) :
    (p : ℤ) ∣ m 0 0 ∧ (p : ℤ) ∣ m 1 0 ∧ (p : ℤ) ∣ m 1 1 := by
  obtain ⟨h10, h11⟩ := row_one_dvd hdet hg hp hprim hB hns hpd
  have hdet' : 0 < (adjugate m).det := by rwa [det_adjugate_two]
  have hprim' : ∃ i j, ¬ (p : ℤ) ∣ (adjugate m) i j := by
    obtain ⟨i, j, hij⟩ := hprim
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
    · exact ⟨1, 1, by simpa [adjugate_fin_two] using hij⟩
    · exact ⟨0, 1, by simpa [adjugate_fin_two] using hij⟩
    · exact ⟨1, 0, by simpa [adjugate_fin_two] using hij⟩
    · exact ⟨0, 0, by simpa [adjugate_fin_two] using hij⟩
  obtain ⟨-, g11⟩ := row_one_dvd hdet' (adjugate_mem_normG hdet hg) hp hprim' hB hns
    (by rwa [det_adjugate_two])
  exact ⟨by simpa [adjugate_fin_two] using g11, h10, h11⟩

/-! ### Prop. 4.5(4) -/

/-- The standard split case: if every Y with m τ = Y m (τ ∈ Γ(N)) is diagonal mod q, then q det m ∣ N m_ij². -/
theorem std_split_dvd {N q : ℕ} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hY : ∀ τ ∈ CongruenceSubgroup.Gamma N, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (q : ℤ) ∣ Y 0 1 ∧ (q : ℤ) ∣ Y 1 0 ∧ m * (τ : Matrix (Fin 2) (Fin 2) ℤ) = Y * m) (i j : Fin 2) :
    (q : ℤ) * m.det ∣ N * m i j ^ 2 := by
  obtain ⟨Y₁, ⟨s1, hs1⟩, ⟨t1, ht1⟩, h1⟩ := hY _ (tN_mem N)
  obtain ⟨Y₂, ⟨s2, hs2⟩, ⟨t2, ht2⟩, h2⟩ := hY _ (uN_mem N)
  have E1 := congrArg (fun M => M * adjugate m) h1
  have E2 := congrArg (fun M => M * adjugate m) h2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at E1 E2
  have a01 := congrFun (congrFun E1 0) 1
  have a10 := congrFun (congrFun E1 1) 0
  have b01 := congrFun (congrFun E2 0) 1
  have b10 := congrFun (congrFun E2 1) 0
  simp [tN, uN, mkSL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b01 b10
  rw [hs1] at a01
  rw [ht1] at a10
  rw [hs2] at b01
  rw [ht2] at b10
  have h00 : (q : ℤ) * m.det ∣ N * m 0 0 ^ 2 := ⟨s1, by linear_combination a01⟩
  have h01 : (q : ℤ) * m.det ∣ N * m 0 1 ^ 2 := ⟨-s2, by linear_combination -b01⟩
  have h10 : (q : ℤ) * m.det ∣ N * m 1 0 ^ 2 := ⟨-t1, by linear_combination -a10⟩
  have h11 : (q : ℤ) * m.det ∣ N * m 1 1 ^ 2 := ⟨t2, by linear_combination b10⟩
  rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
  exacts [h00, h01, h10, h11]

theorem le_of_isSplitMod' {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p k : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j) (hk : p ^ k ∣ N)
    (hsplit : IsSplitMod H (p ^ k)) {e : ℕ} (he : (p : ℤ) ^ e ∣ m.det) :
    e + k ≤ N.factorization p := by
  set q := p ^ k with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero q := ⟨hq0⟩
  obtain ⟨v, w, hv, hw, hunit⟩ := hsplit
  obtain ⟨δ, hδ⟩ := hunit
  set w' : Fin 2 → ZMod q := ((δ⁻¹ : (ZMod q)ˣ) : ZMod q) • w with hw'def
  have hw' : FixesLine H q w' := by
    intro h hh
    obtain ⟨c, hc⟩ := hw h hh
    refine ⟨c, ?_⟩
    rw [hw'def, Matrix.mulVec_smul, hc, smul_comm]
  have hdetP : v 0 * w' 1 - v 1 * w' 0 = 1 := by
    simp only [hw'def, Pi.smul_apply, smul_eq_mul]
    calc v 0 * (((δ⁻¹ : (ZMod q)ˣ) : ZMod q) * w 1) - v 1 * (((δ⁻¹ : (ZMod q)ˣ) : ZMod q) * w 0)
        = ((δ⁻¹ : (ZMod q)ˣ) : ZMod q) * (v 0 * w 1 - v 1 * w 0) := by ring
      _ = 1 := by rw [← hδ, Units.inv_mul]
  let P : SL(2, ZMod q) := ⟨!![v 0, w' 0; v 1, w' 1], by rw [det_fin_two_of]; linear_combination hdetP⟩
  obtain ⟨σ, hσ⟩ := redSL_surjective q P
  have hσe : ∀ i j, ((σ i j : ℤ) : ZMod q) = (P : Matrix (Fin 2) (Fin 2) (ZMod q)) i j := by
    intro i j
    rw [← hσ]
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have s00 : ((σ 0 0 : ℤ) : ZMod q) = v 0 := hσe 0 0
  have s01 : ((σ 0 1 : ℤ) : ZMod q) = w' 0 := hσe 0 1
  have s10 : ((σ 1 0 : ℤ) : ZMod q) = v 1 := hσe 1 0
  have s11 : ((σ 1 1 : ℤ) : ZMod q) = w' 1 := hσe 1 1
  have hσσ : (σ : Matrix (Fin 2) (Fin 2) ℤ) * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hσσ' : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set m' : Matrix (Fin 2) (Fin 2) ℤ :=
    ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * m * (σ : Matrix (Fin 2) (Fin 2) ℤ) with hm'
  have hmm' : m = (σ : Matrix (Fin 2) (Fin 2) ℤ) * m' * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hm', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hσσ, Matrix.one_mul, Matrix.mul_assoc, hσσ,
      Matrix.mul_one]
  have hdet' : m'.det = m.det := by
    rw [hm', det_mul, det_mul, (σ⁻¹).2, σ.2, one_mul, mul_one]
  have hprim' : ∃ i j, ¬ (p : ℤ) ∣ m' i j := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, j, hij⟩ := hprim
    apply hij
    rw [hmm']
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    apply dvd_add <;> apply dvd_mul_of_dvd_left <;> apply dvd_add <;> apply dvd_mul_of_dvd_right <;>
      exact hcon _ _
  have hY : ∀ τ ∈ CongruenceSubgroup.Gamma N, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (q : ℤ) ∣ Y 0 1 ∧ (q : ℤ) ∣ Y 1 0 ∧ m' * (τ : Matrix (Fin 2) (Fin 2) ℤ) = Y * m' := by
    intro τ hτ
    have hτ' : σ * τ * σ⁻¹ ∈ GammaH N H :=
      Gamma_le_GammaH N H ((CongruenceSubgroup.Gamma_normal N).conj_mem τ hτ σ)
    obtain ⟨X, hX, hrel⟩ := exists_rel_left hdet hg hτ'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at hrel
    set Y : Matrix (Fin 2) (Fin 2) ℤ :=
      ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * X * σ with hYdef
    have hσY : (σ : Matrix (Fin 2) (Fin 2) ℤ) * Y = (X : Matrix (Fin 2) (Fin 2) ℤ) * σ := by
      rw [hYdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hσσ, Matrix.one_mul]
    obtain ⟨c, hc⟩ := hv _ hX
    obtain ⟨c', hc'⟩ := hw' _ hX
    rw [map_cast_redSL hk] at hc hc'
    have E : ∀ r k, ((((σ : Matrix (Fin 2) (Fin 2) ℤ) * Y) r k : ℤ) : ZMod q) =
        (((X : Matrix (Fin 2) (Fin 2) ℤ) * σ) r k : ℤ) := fun r k => by rw [hσY]
    have E00 := E 0 0
    have E10 := E 1 0
    have E01 := E 0 1
    have E11 := E 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at E00 E10 E01 E11
    push_cast at E00 E10 E01 E11
    simp only [s00, s01, s10, s11] at E00 E10 E01 E11
    have c0 := congrFun hc 0
    have c1 := congrFun hc 1
    have d0 := congrFun hc' 0
    have d1 := congrFun hc' 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul] at c0 c1 d0 d1
    refine ⟨Y, ?_, ?_, ?_⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      linear_combination (-((Y 0 1 : ℤ) : ZMod q)) * hdetP + w' 1 * (E01.trans d0) - w' 0 * (E11.trans d1)
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      linear_combination (-((Y 1 0 : ℤ) : ZMod q)) * hdetP + v 0 * (E10.trans c1) - v 1 * (E00.trans c0)
    · have h1 : m * σ * τ = X * m * σ := by
        calc m * (σ : Matrix (Fin 2) (Fin 2) ℤ) * τ
            = m * (σ * τ * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * σ := by
              simp only [Matrix.mul_assoc, hσσ', Matrix.mul_one]
          _ = X * m * σ := by rw [hrel]
      calc m' * (τ : Matrix (Fin 2) (Fin 2) ℤ)
          = ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (m * σ * τ) := by
            simp only [hm', Matrix.mul_assoc]
        _ = ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (X * m * σ) := by rw [h1]
        _ = Y * m' := by
            have hσσm : ∀ M : Matrix (Fin 2) (Fin 2) ℤ,
                (σ : Matrix (Fin 2) (Fin 2) ℤ) * (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) = M := by
              intro M; rw [← Matrix.mul_assoc, hσσ, Matrix.one_mul]
            simp only [hYdef, hm', Matrix.mul_assoc]
            rw [hσσm]
  obtain ⟨i, j, hij⟩ := hprim'
  have h1 := std_split_dvd hY i j
  rw [hdet'] at h1
  have h2 : (p : ℤ) ^ (k + e) ∣ N * m' i j ^ 2 := by
    refine dvd_trans ?_ h1
    rw [pow_add, hq]; push_cast
    exact mul_dvd_mul_left _ he
  have h3 : (p : ℤ) ^ (k + e) ∣ N := (isCoprime_pow_of_not_dvd hp hij _ 2).dvd_of_dvd_mul_right h2
  have h4 : p ^ (k + e) ∣ N := by exact_mod_cast h3
  have := (hp.pow_dvd_iff_le_factorization (NeZero.ne N)).1 h4
  omega

end

end NormalizerLean
