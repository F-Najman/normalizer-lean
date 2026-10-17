module

public import NormalizerDelta.Iota

@[expose] public section

/-!
# s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ}: `sDelta_eq_sIota'`

For 4 ∤ N and 9 ∤ N, h(N) = 1 and n(N) = N, so Newman's form (8′) is the Atkin–Lehner form: every
element of Nor(Γ₀(N)) is some w_Q, Q ∥ N, and e(w_Q) = Q.  The class of w_Q in B(N) determines Q
(p ∣ e is invariant under Γ₀(N), by the frozen `chi_mul`), so Q ↦ [w_Q] is a bijection from
{Q ∥ N : ι_Q(Δ) = Δ} onto the elements of B(N) normalizing Γ_Δ(N) (`al_mem_normG_iff`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

theorem hPart_eq_one_of (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) : hPart N = 1 := by
  by_cases hN : N = 0
  · subst hN; exact absurd (dvd_zero 4) h4
  have h2 : N.factorization 2 < 2 := by
    by_contra h
    apply h4
    have : 2 ^ 2 ∣ N := (Nat.prime_two.pow_dvd_iff_le_factorization hN).2 (by omega)
    simpa using this
  have h3 : N.factorization 3 < 2 := by
    by_contra h
    apply h9
    have : 3 ^ 2 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization hN).2 (by omega)
    simpa using this
  unfold hPart
  rw [show N.factorization 2 / 2 = 0 by omega, show N.factorization 3 / 2 = 0 by omega]
  simp

theorem nPart_eq_of (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) : nPart N = N := by
  simp [nPart, hPart_eq_one_of h4 h9]

theorem coprime_of_isAtkinLehner {Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : Nat.Coprime Q (N / Q) := by
  obtain ⟨x, y, z, w, hdet, -⟩ := hg
  have hQ0 : Q ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  obtain ⟨K, hK⟩ := hQ
  have hKdiv : N / Q = K := by rw [hK, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)]
  rw [hKdiv]
  have hdet' : (x * w) * (Q : ℤ) + (-(y * z)) * K = 1 := by
    apply mul_left_cancel₀ (show (Q : ℤ) ≠ 0 by exact_mod_cast hQ0)
    rw [hK] at hdet; push_cast at hdet
    linear_combination hdet
  exact Nat.isCoprime_iff_coprime.1 ⟨_, _, hdet'⟩

/-- For h(N) = 1, every element of Nor(Γ₀(N)) is an Atkin–Lehner element. -/
theorem isAtkinLehner_of_mem_Norm0 [NeZero N] (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) {g : SL(2, ℝ)}
    (hg : g ∈ Norm0 N) : ∃ Q, Q ∣ N ∧ IsAtkinLehner N Q g := by
  obtain ⟨a, b, c, d, e, he0, hen, hdet, ε, hε, hgm⟩ := newman' hg
  rw [nPart_eq_of h4 h9] at hen hdet
  rw [hPart_eq_one_of h4 h9] at hgm
  refine ⟨e, hen, ?_⟩
  rcases hε with rfl | rfl
  · refine ⟨a, b, c, d, by linear_combination hdet, ?_⟩
    rw [hgm, one_div]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  · refine ⟨-a, -b, -c, -d, by linear_combination hdet, ?_⟩
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem eOf_of_isAtkinLehner [NeZero N] (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) {Q : ℕ} (hQ : Q ∣ N)
    {g : SL(2, ℝ)} (hg : IsAtkinLehner N Q g) : eOf N g = Q := by
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  have hQ0 : Q ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  apply eOf_eq (a := x) (b := y) (c := z) (d := w) (ε := 1)
  refine ⟨Nat.pos_of_ne_zero hQ0, by rw [nPart_eq_of h4 h9]; exact hQ, ?_, Or.inl rfl, ?_⟩
  · rw [nPart_eq_of h4 h9]; linear_combination hdet
  · rw [hgm, hPart_eq_one_of h4 h9, one_div]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

/-- An exact divisor of N is determined by its prime divisors. -/
theorem eq_of_exact_dvd {Q Q' : ℕ} [NeZero N] (hQ : Q ∣ N) (hQ' : Q' ∣ N)
    (hc : Nat.Coprime Q (N / Q)) (hc' : Nat.Coprime Q' (N / Q'))
    (h : ∀ p, p.Prime → (p ∣ Q ↔ p ∣ Q')) : Q = Q' := by
  have hN := NeZero.ne N
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ)
  have hQ0' : Q' ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ')
  have key : ∀ R, R ∣ N → Nat.Coprime R (N / R) → ∀ p, p.Prime → p ∣ R →
      R.factorization p = N.factorization p := by
    intro R hR hcR p hp hpR
    have hR0 : R ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hR)
    have hK0 : N / R ≠ 0 := by
      intro h0; rw [Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero hR0)] at h0
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hR) (by omega)
    have hpK : ¬ p ∣ N / R := fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpR hcR) hd
    have hNR : N = R * (N / R) := (Nat.mul_div_cancel' hR).symm
    conv_rhs => rw [hNR]
    rw [Nat.factorization_mul hR0 hK0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpK,
      add_zero]
  apply Nat.eq_of_factorization_eq hQ0 hQ0'
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  by_cases hpQ : p ∣ Q
  · rw [key Q hQ hc p hp hpQ, key Q' hQ' hc' p hp ((h p hp).1 hpQ)]
  · rw [Nat.factorization_eq_zero_of_not_dvd hpQ,
      Nat.factorization_eq_zero_of_not_dvd (fun h' => hpQ ((h p hp).2 h'))]

/-- Two Atkin–Lehner elements in the same class of B(N) have the same Q (for h(N) = 1). -/
theorem eq_of_isAtkinLehner_class [NeZero N] (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) {Q Q' : ℕ}
    (hQ : Q ∣ N) (hQ' : Q' ∣ N) {g g' : SL(2, ℝ)} (hg : IsAtkinLehner N Q g)
    (hg' : IsAtkinLehner N Q' g') (hgg : g⁻¹ * g' ∈ Gamma0R N) : Q = Q' := by
  have hgN := isAtkinLehner_mem_normalizer' hQ hg
  have hγN : g⁻¹ * g' ∈ Norm0 N :=
    mul_mem (inv_mem hgN) (isAtkinLehner_mem_normalizer' hQ' hg')
  refine eq_of_exact_dvd hQ hQ' (coprime_of_isAtkinLehner hQ hg) (coprime_of_isAtkinLehner hQ' hg')
    (fun p hp => ?_)
  have hchi := chi_mul hgN hγN hp
  rw [mul_inv_cancel_left] at hchi
  have h1 : chi N p (g⁻¹ * g') = 0 := by
    simp [chi, eOf_of_mem_Gamma0R hgg, hp.one_lt.ne']
  rw [h1, add_zero] at hchi
  unfold chi at hchi
  rw [eOf_of_isAtkinLehner h4 h9 hQ hg, eOf_of_isAtkinLehner h4 h9 hQ' hg'] at hchi
  by_cases h' : p ∣ Q' <;> by_cases h : p ∣ Q <;> simp [h, h'] at hchi ⊢

/-- **s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ}** for 4 ∤ N, 9 ∤ N. -/
theorem sDelta_eq_sIota' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) (h4 : ¬ 4 ∣ N)
    (h9 : ¬ 9 ∣ N) : sDelta N Δ = sIota N Δ := by
  classical
  let gQ : (Q : ℕ) → Q ∣ N → Nat.Coprime Q (N / Q) → SL(2, ℝ) :=
    fun Q hQ hc => Classical.choose (exists_isAtkinLehner' hQ hc)
  have hgQ : ∀ Q hQ hc, IsAtkinLehner N Q (gQ Q hQ hc) :=
    fun Q hQ hc => Classical.choose_spec (exists_isAtkinLehner' hQ hc)
  let F : {Q : ℕ // Q ∣ N ∧ Nat.Coprime Q (N / Q) ∧ ∀ u, u ∈ Δ ↔ ∃ d ∈ Δ, IsIota N Q d u} →
      {x : B N // ∃ g : SL(2, ℝ), x.IsClassOf g ∧ g ∈ NormG (GammaDeltaR N Δ)} :=
    fun Q => ⟨QuotientGroup.mk ⟨gQ Q.1 Q.2.1 Q.2.2.1,
        isAtkinLehner_mem_normalizer' Q.2.1 (hgQ _ Q.2.1 Q.2.2.1)⟩,
      gQ Q.1 Q.2.1 Q.2.2.1, ⟨_, rfl⟩,
      (al_mem_normG_iff Q.2.1 Q.2.2.1 (hgQ _ Q.2.1 Q.2.2.1) Δ).2 Q.2.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨Q, hQ, hc, hs⟩ ⟨Q', hQ', hc', hs'⟩ hFF
      have := congrArg Subtype.val hFF
      simp only [F] at this
      rw [B.mk_eq_mk_iff] at this
      exact Subtype.ext (eq_of_isAtkinLehner_class h4 h9 hQ hQ' (hgQ Q hQ hc) (hgQ Q' hQ' hc') this)
    · rintro ⟨x, g, ⟨hgB, rfl⟩, hgN⟩
      obtain ⟨Q, hQ, hg⟩ := isAtkinLehner_of_mem_Norm0 h4 h9 hgB
      have hc := coprime_of_isAtkinLehner hQ hg
      refine ⟨⟨Q, hQ, hc, (al_mem_normG_iff hQ hc hg Δ).1 hgN⟩, Subtype.ext ?_⟩
      obtain ⟨-, hcl⟩ := isALClass_mk hQ (hgQ Q hQ hc)
      obtain ⟨hgB', heq⟩ := hcl g hg
      exact heq
  exact (Nat.card_eq_of_bijective F hF).symm

/-- **The index**, combined with `sDelta_eq_sIota'`. -/
theorem card_BG_GammaDeltaR_of_not_dvd' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    (h : hDelta N Δ = hPart N) (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * sIota N Δ := by
  rw [card_BG_GammaDeltaR' Δ h, sDelta_eq_sIota' Δ h4 h9]

end

end NormalizerLean
