module

public import NormalizerLean.CardB
public import NormalizerLean.NewmanVal

@[expose] public section

/-!
# T3, explicit form: 2^{ω(n)} ψ(N)/ψ(n) = f₂(v₂ N) f₃(v₃ N) 2^{#{p ∣ N, p ≥ 5}}

Both sides are products over the primes p ∣ N of local factors; with ν = v_p(N), k = v_p(h) and
ν' = v_p(n) = ν − 2k the local factor of the left side is
[ν' > 0 ? 2 : 1] · p^ν (1 + 1/p) / (p^{ν'} [ν' > 0 ? 1 + 1/p : 1]),
which is f₂(ν) for p = 2, f₃(ν) for p = 3 and 2 otherwise.
-/

namespace NormalizerLean

open Finset

/-- t = ∏_{p ∣ t} p^{v_p(t)} (in ℚ). -/
theorem cast_eq_prod_pow {t : ℕ} (ht : t ≠ 0) :
    (t : ℚ) = ∏ p ∈ t.primeFactors, (p : ℚ) ^ t.factorization p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ht]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  push_cast
  rfl

theorem psi_eq_prod {t : ℕ} (ht : t ≠ 0) :
    psi t = ∏ p ∈ t.primeFactors, ((p : ℚ) ^ t.factorization p * (1 + 1 / (p : ℚ))) := by
  rw [psi, cast_eq_prod_pow ht, ← prod_mul_distrib]

/-- The local factor of the left side. -/
noncomputable def lfac (p ν ν' : ℕ) : ℚ :=
  (if 0 < ν' then 2 else 1) * ((p : ℚ) ^ ν * (1 + 1 / (p : ℚ))) /
    ((p : ℚ) ^ ν' * (if 0 < ν' then 1 + 1 / (p : ℚ) else 1))

/-- The local factor of the right side. -/
def rfac (p ν : ℕ) : ℚ := if p = 2 then f₂ ν else if p = 3 then f₃ ν else 2

theorem f₂_ge {ν : ℕ} (h : 7 ≤ ν) : f₂ ν = 128 := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 7 := ⟨ν - 7, by omega⟩
  rfl

theorem f₃_ge {ν : ℕ} (h : 3 ≤ ν) : f₃ ν = 18 := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m + 3 := ⟨ν - 3, by omega⟩
  rfl

theorem lfac_eq_rfac {p ν k ν' : ℕ} (hp : p.Prime) (hν : 1 ≤ ν)
    (hk : (p = 2 ∧ k = min 3 (ν / 2)) ∨ (p = 3 ∧ k = min 1 (ν / 2)) ∨ (p ≠ 2 ∧ p ≠ 3 ∧ k = 0))
    (hν' : ν' + 2 * k = ν) : lfac p ν ν' = rfac p ν := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hp1 : (1 : ℚ) + 1 / p ≠ 0 := by positivity
  have hν'eq : ν' = ν - 2 * k := by omega
  subst hν'eq
  rcases hk with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨h2, h3, rfl⟩
  · subst hk
    simp only [rfac, ite_true]
    rcases Nat.lt_or_ge ν 7 with h7 | h7
    · interval_cases ν <;> norm_num [lfac, f₂]
    · obtain ⟨m, rfl⟩ : ∃ m, ν = m + 7 := ⟨ν - 7, by omega⟩
      rw [f₂_ge h7, lfac, show min 3 ((m + 7) / 2) = 3 by omega,
        show m + 7 - 2 * 3 = m + 1 by omega, if_pos (by omega), if_pos (by omega),
        show m + 7 = (m + 1) + 6 by omega, pow_add]
      field_simp
      norm_num
  · subst hk
    simp only [rfac, if_neg (by norm_num : (3 : ℕ) ≠ 2), ite_true]
    rcases Nat.lt_or_ge ν 3 with h7 | h7
    · interval_cases ν <;> norm_num [lfac, f₃]
    · obtain ⟨m, rfl⟩ : ∃ m, ν = m + 3 := ⟨ν - 3, by omega⟩
      rw [f₃_ge h7, lfac, show min 1 ((m + 3) / 2) = 1 by omega,
        show m + 3 - 2 * 1 = m + 1 by omega, if_pos (by omega), if_pos (by omega),
        show m + 3 = (m + 1) + 2 by omega, pow_add]
      field_simp
      norm_num
  · simp only [rfac, if_neg h2, if_neg h3]
    rw [lfac, show ν - 2 * 0 = ν by omega, if_pos (by omega), if_pos (by omega)]
    field_simp

theorem f₂_zero : f₂ 0 = 1 := rfl
theorem f₃_zero : f₃ 0 = 1 := rfl

/-- The right side as a product. -/
theorem rhs_eq_prod {N : ℕ} (hN : N ≠ 0) :
    ((f₂ (N.factorization 2) * f₃ (N.factorization 3) * 2 ^ (N.primeFactors \ {2, 3}).card : ℕ)
      : ℚ) = ∏ p ∈ N.primeFactors, rfac p (N.factorization p) := by
  have hsplit : ∀ p ∈ N.primeFactors, rfac p (N.factorization p) =
      (if p = 2 then (f₂ (N.factorization 2) : ℚ) else 1) *
        (if p = 3 then (f₃ (N.factorization 3) : ℚ) else 1) *
        (if p ∈ N.primeFactors \ {2, 3} then 2 else 1) := by
    intro p hp
    unfold rfac
    by_cases h2 : p = 2
    · subst h2; simp
    by_cases h3 : p = 3
    · subst h3; simp
    · simp [h2, h3, hp]
  rw [prod_congr rfl hsplit, prod_mul_distrib, prod_mul_distrib, prod_ite_eq', prod_ite_eq',
    prod_ite_mem, prod_const]
  have hsub : N.primeFactors ∩ (N.primeFactors \ {2, 3}) = N.primeFactors \ {2, 3} :=
    inter_eq_right.2 sdiff_subset
  rw [hsub]
  have e2 : (if 2 ∈ N.primeFactors then (f₂ (N.factorization 2) : ℚ) else 1) =
      f₂ (N.factorization 2) := by
    split_ifs with h
    · rfl
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun hd => h (Nat.mem_primeFactors.2
        ⟨Nat.prime_two, hd, hN⟩))]
      simp [f₂_zero]
  have e3 : (if 3 ∈ N.primeFactors then (f₃ (N.factorization 3) : ℚ) else 1) =
      f₃ (N.factorization 3) := by
    split_ifs with h
    · rfl
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun hd => h (Nat.mem_primeFactors.2
        ⟨Nat.prime_three, hd, hN⟩))]
      simp [f₃_zero]
  rw [e2, e3]
  push_cast
  ring

/-- The left side as a product. -/
theorem lhs_eq_prod {N : ℕ} (hN : N ≠ 0) :
    (2 : ℚ) ^ (nPart N).primeFactors.card * psi N / psi (nPart N) =
      ∏ p ∈ N.primeFactors, lfac p (N.factorization p) ((nPart N).factorization p) := by
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N hN
    rw [h0, zero_mul] at this
    exact hN this.symm
  have hnN : nPart N ∣ N := ⟨hPart N ^ 2, (hPart_sq_mul_nPart N hN).symm⟩
  have hsub : (nPart N).primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono hnN hN
  have hmem : ∀ p ∈ N.primeFactors, (p ∈ (nPart N).primeFactors ↔ 0 < (nPart N).factorization p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.mem_primeFactors]
    constructor
    · exact fun h => (hpp.dvd_iff_one_le_factorization hn0).1 h.2.1
    · exact fun h => ⟨hpp, (hpp.dvd_iff_one_le_factorization hn0).2 h, hn0⟩
  -- ψ(n) and 2^ω(n) as products over the primes of N
  have hψn : psi (nPart N) = ∏ p ∈ N.primeFactors, ((p : ℚ) ^ (nPart N).factorization p *
      (if 0 < (nPart N).factorization p then 1 + 1 / (p : ℚ) else 1)) := by
    rw [psi_eq_prod hn0]
    have step1 : ∏ p ∈ (nPart N).primeFactors, ((p : ℚ) ^ (nPart N).factorization p *
        (1 + 1 / (p : ℚ))) = ∏ p ∈ (nPart N).primeFactors, ((p : ℚ) ^ (nPart N).factorization p *
        (if 0 < (nPart N).factorization p then 1 + 1 / (p : ℚ) else 1)) :=
      prod_congr rfl (fun p hp => by rw [if_pos ((hmem p (hsub hp)).1 hp)])
    rw [step1]
    apply prod_subset hsub
    intro p hp hpn
    have h0 : (nPart N).factorization p = 0 := by
      by_contra h
      exact hpn ((hmem p hp).2 (Nat.pos_of_ne_zero h))
    simp [h0]
  have h2ω : (2 : ℚ) ^ (nPart N).primeFactors.card =
      ∏ p ∈ N.primeFactors, (if 0 < (nPart N).factorization p then (2 : ℚ) else 1) := by
    rw [prod_ite, prod_const_one, mul_one, prod_const]
    congr 2
    ext p
    simp only [mem_filter]
    constructor
    · intro hp; exact ⟨hsub hp, (hmem p (hsub hp)).1 hp⟩
    · rintro ⟨hp, h⟩; exact (hmem p hp).2 h
  rw [h2ω, psi_eq_prod hN, hψn, ← prod_mul_distrib, ← prod_div_distrib]
  rfl

/-- **T3, explicit form.** -/
theorem card_B_explicit' (N : ℕ) [NeZero N] :
    Nat.card (B N) =
      f₂ (N.factorization 2) * f₃ (N.factorization 3) * 2 ^ (N.primeFactors \ {2, 3}).card := by
  have hN := NeZero.ne N
  have h := card_B' N
  rw [lhs_eq_prod hN] at h
  have hloc : ∀ p ∈ N.primeFactors, lfac p (N.factorization p) ((nPart N).factorization p) =
      rfac p (N.factorization p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨-, hk⟩ := local_constants (p := p) hN
    have hν : 1 ≤ N.factorization p :=
      hpp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp)
    refine lfac_eq_rfac hpp hν ?_ (factorization_nPart hN)
    rw [hk, factorization_epsPart hN, factorization_24]
    by_cases h2 : p = 2
    · subst h2; left; simp; omega
    by_cases h3 : p = 3
    · subst h3; right; left; simp; omega
    · right; right; simp [h2, h3]
  rw [prod_congr rfl hloc, ← rhs_eq_prod hN] at h
  exact_mod_cast h

end NormalizerLean
