module

public import NormalizerLean.NewmanMain
public import NormalizerLean.NewmanAlg
public import NormalizerLean.CardC

@[expose] public section

/-!
# T3: B(N)/C(N) ≅ (ℤ/2)^{ω(n)}, |B(N)| and finiteness

By Newman's theorem every g ∈ Norm(Γ₀(N)) has (8′)-data, with a well-defined e(g) (`eOf`).
σ(g) = (p ↦ [p ∣ e(g)]) is a homomorphism by the parity rule `NData.dvd_eOf_mul_iff`, trivial on
Γ₀(N) (e = 1), with kernel C(N) (`NData.mem_conjGamma0n`), and surjective (an (8′)-element with
e = p^{v_p(n)} for each p ∣ n).  Then |B(N)| = |C(N)|·2^{ω(n)}.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem exists_NData_of_mem {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) :
    ∃ a b c d e ε, NData N g a b c d e ε :=
  isNewmanForm_iff.1 (newman' hg)

/-- The parity of p in e(g). -/
def chi (N p : ℕ) (g : SL(2, ℝ)) : ZMod 2 := if p ∣ eOf N g then 1 else 0

theorem chi_mul {N : ℕ} [NeZero N] {g g' : SL(2, ℝ)} (hg : g ∈ Norm0 N) (hg' : g' ∈ Norm0 N)
    {p : ℕ} (hp : p.Prime) : chi N p (g * g') = chi N p g + chi N p g' := by
  obtain ⟨a, b, c, d, e, ε, h⟩ := exists_NData_of_mem hg
  obtain ⟨a', b', c', d', e', ε', h'⟩ := exists_NData_of_mem hg'
  have key := h.dvd_eOf_mul_iff h' hp
  unfold chi
  rw [eOf_eq h, eOf_eq h']
  by_cases h1 : p ∣ e <;> by_cases h2 : p ∣ e' <;> by_cases h3 : p ∣ eOf N (g * g') <;>
    simp only [h1, h2, h3, if_true, if_false] <;> first | decide | (exfalso; tauto)

theorem eOf_of_mem_Gamma0R {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Gamma0R N) :
    eOf N g = 1 := by
  obtain ⟨a, b, c, d, h⟩ := NData.of_mem_Gamma0R hg
  exact eOf_eq h

theorem eOf_of_mem_conjGamma0n {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ conjGamma0n N) :
    eOf N g = 1 := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨a', b', c'', d', hdet, ⟨c', rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have : NData N ((MulAut.conj (Dsl N)⁻¹).toMonoidHom γ) a' b' c' d' 1 1 := by
    refine ⟨one_pos, one_dvd _, by push_cast; linear_combination hdet, Or.inl rfl, ?_⟩
    have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
    have hh0 : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
    have hD := coe_Dsl N
    have hDinv := coe_inv_of_coe_eq_smul hD
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDinv, hγm, hD]
    have hs : Real.sqrt (hPart N) * Real.sqrt (hPart N) = hPart N :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hsq : (Real.sqrt (hPart N))⁻¹ * (Real.sqrt (hPart N))⁻¹ * (hPart N : ℝ) = 1 := by
      rw [← mul_inv, hs, inv_mul_cancel₀ hh0]
    have hNr : (N : ℝ) = nPart N * (hPart N) ^ 2 := by exact_mod_cast hNnh.symm
    rw [smul_mul_mul_smul_eq_of hsq (X := !![(a' : ℝ), b' / hPart N; nPart N * c' * hPart N, d'])]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> ring
    · rw [mul_fin_two, mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  exact eOf_eq this

/-- σ on the normalizer. -/
def sigmaN (N : ℕ) [NeZero N] : Norm0 N →* ((nPart N).primeFactors → Multiplicative (ZMod 2)) where
  toFun g := fun p => Multiplicative.ofAdd (chi N p g)
  map_one' := by
    funext p
    have : eOf N 1 = 1 := eOf_of_mem_Gamma0R (one_mem _)
    simp [chi, this, (Nat.prime_of_mem_primeFactors p.2).one_lt.ne']
  map_mul' g g' := by
    funext p
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    rw [chi_mul g.2 g'.2 (Nat.prime_of_mem_primeFactors p.2), ofAdd_add]

theorem sigmaN_eq_one_iff {N : ℕ} [NeZero N] (g : Norm0 N) :
    sigmaN N g = 1 ↔ eOf N g = 1 := by
  obtain ⟨a, b, c, d, e, ε, h⟩ := exists_NData_of_mem g.2
  have hen : eOf N g ∣ nPart N := by rw [eOf_eq h]; exact h.2.1
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N (NeZero.ne N)
    rw [h0, zero_mul] at this
    exact NeZero.ne N this.symm
  constructor
  · intro hσ
    by_contra hne
    obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd hne
    have hpS : p ∈ (nPart N).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hp, dvd_trans hpe hen, hn0⟩
    have := congrFun hσ ⟨p, hpS⟩
    simp [sigmaN, chi, hpe] at this
  · intro h1
    funext p
    simp [sigmaN, chi, h1, (Nat.prime_of_mem_primeFactors p.2).one_lt.ne']

/-- σ on B(N). -/
def sigmaB (N : ℕ) [NeZero N] : B N →* ((nPart N).primeFactors → Multiplicative (ZMod 2)) :=
  QuotientGroup.lift _ (sigmaN N) (fun g hg => by
    rw [Subgroup.mem_subgroupOf] at hg
    exact (sigmaN_eq_one_iff g).2 (eOf_of_mem_Gamma0R hg))

theorem sigmaB_ker (N : ℕ) [NeZero N] : (sigmaB N).ker = CN N := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MonoidHom.mem_ker]
    change sigmaN N g = 1 ↔ _
    rw [sigmaN_eq_one_iff]
    constructor
    · intro h1
      obtain ⟨a, b, c, d, e, ε, h⟩ := exists_NData_of_mem g.2
      rw [eOf_eq h] at h1
      subst h1
      exact ⟨⟨g, g.2⟩, Subgroup.mem_subgroupOf.2 (h.mem_conjGamma0n), rfl⟩
    · rintro ⟨y, hy, hxy⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      have h1 := eOf_of_mem_conjGamma0n hy
      -- g and y differ by Γ₀(N)
      have hgy : (y : SL(2, ℝ))⁻¹ * g ∈ Gamma0R N := by
        have := QuotientGroup.eq.1 hxy
        simpa [Subgroup.mem_subgroupOf] using this
      have hσ : sigmaN N g = sigmaN N y := by
        have : sigmaN N (y⁻¹ * g) = 1 := (sigmaN_eq_one_iff _).2 (eOf_of_mem_Gamma0R hgy)
        rw [map_mul, map_inv] at this
        exact (inv_mul_eq_one.1 this).symm
      have hy1 : sigmaN N y = 1 := (sigmaN_eq_one_iff y).2 h1
      exact (sigmaN_eq_one_iff g).1 (hσ.trans hy1)

theorem sigmaB_surjective (N : ℕ) [NeZero N] : Function.Surjective (sigmaB N) := by
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N (NeZero.ne N)
    rw [h0, zero_mul] at this
    exact NeZero.ne N this.symm
  -- each basis vector is hit
  have hbasis : ∀ p : (nPart N).primeFactors,
      Pi.mulSingle p (Multiplicative.ofAdd (1 : ZMod 2)) ∈ (sigmaB N).range := by
    intro p
    have hp := Nat.prime_of_mem_primeFactors p.2
    set q := (p : ℕ) ^ (nPart N).factorization p
    have hq : q ∣ nPart N := Nat.ordProj_dvd _ _
    have hqc : Nat.Coprime q (nPart N / q) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
    obtain ⟨g, a, b, c, d, h⟩ := NData.exists_of_exact (N := N) hq hqc
    have hgN : g ∈ Norm0 N := newmanForm_mem_normalizer' (isNewmanForm_iff.2 ⟨a, b, c, d, q, 1, h⟩)
    refine ⟨QuotientGroup.mk ⟨g, hgN⟩, ?_⟩
    funext r
    change Multiplicative.ofAdd (chi N r g) = _
    have hpos : 0 < (nPart N).factorization p :=
      hp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors p.2)
    have hr := Nat.prime_of_mem_primeFactors r.2
    unfold chi
    rw [eOf_eq h]
    by_cases hrp : r = p
    · subst hrp
      simp [q, dvd_pow_self _ hpos.ne']
    · have : ¬ (r : ℕ) ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hd)
        exact hrp (Subtype.ext this)
      simp [this, Pi.mulSingle_apply, hrp]
  intro f
  have : f = ∏ p, Pi.mulSingle p (f p) := (Finset.univ_prod_mulSingle f).symm
  rw [this]
  refine (MonoidHom.mem_range).1 ?_
  apply Subgroup.prod_mem
  intro p _
  -- f p is 1 or ofAdd 1
  have hfp : f p = 1 ∨ f p = Multiplicative.ofAdd (1 : ZMod 2) := by
    generalize f p = z
    revert z
    decide
  rcases hfp with h | h
  · rw [h, Pi.mulSingle_one]; exact one_mem _
  · rw [h]; exact hbasis p

/-- **B(N)/C(N) ≅ (ℤ/2)^{ω(n)}** -/
theorem B_mod_CN' (N : ℕ) [NeZero N] :
    ∃ σ : B N →* ((nPart N).primeFactors → Multiplicative (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = CN N :=
  ⟨sigmaB N, sigmaB_surjective N, sigmaB_ker N⟩

theorem psi_pos {t : ℕ} (ht : t ≠ 0) : 0 < psi t := by
  unfold psi
  apply mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero ht))
  apply Finset.prod_pos
  intro p _
  positivity

theorem card_B_mul (N : ℕ) [NeZero N] :
    Nat.card (B N) = Nat.card (CN N) * 2 ^ (nPart N).primeFactors.card := by
  rw [← Subgroup.card_mul_index (sigmaB N).ker, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (sigmaB_surjective N)).toEquiv,
    sigmaB_ker]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
  congr 1

/-- **T3**: |B(N)| = 2^{ω(n)} ψ(N)/ψ(n). -/
theorem card_B' (N : ℕ) [NeZero N] :
    (Nat.card (B N) : ℚ) = 2 ^ (nPart N).primeFactors.card * psi N / psi (nPart N) := by
  rw [card_B_mul, Nat.cast_mul, card_CN']
  push_cast
  ring

/-- **T3**: B(N) is finite. -/
theorem finite_B' (N : ℕ) [NeZero N] : Finite (B N) := by
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N (NeZero.ne N)
    rw [h0, zero_mul] at this
    exact NeZero.ne N this.symm
  apply Nat.finite_of_card_ne_zero
  intro h0
  have := card_B' N
  rw [h0, Nat.cast_zero] at this
  have hpos : (0 : ℚ) < 2 ^ (nPart N).primeFactors.card * psi N / psi (nPart N) :=
    div_pos (mul_pos (by positivity) (psi_pos (NeZero.ne N))) (psi_pos hn0)
  linarith

end

end NormalizerLean
