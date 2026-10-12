import NormalizerDelta.Basic

/-!
# SL₂(ℤ) → SL₂(ℤ/N) is surjective (not in the pinned Mathlib)

Let A ∈ SL₂(ℤ/N) with integer lifts a, b, c, d (so ad − bc ≡ 1 mod N, and no prime divides c, d and N).
1. (`exists_coprime_lift`) Replace c by c' = N if c = 0, and d by d' = d + tN, t the product of the primes
   dividing c' but not d.  Then gcd(c', d') = 1: a common prime p either divides d, hence not t, hence N,
   hence c; or it does not divide d, hence divides t and so d.
2. Choose a₀ d' − b₀ c' = 1, put x = a − a₀, y = b − b₀, m = y a₀ − x b₀, a'' = a₀ + m c', b'' = b₀ + m d'.
   Then a'' d' − b'' c' = 1, a'' − a = a₀ (y c' − x d') and b'' − b = b₀ (y c' − x d'), where
   y c' − x d' = 1 − (a d' − b c') ≡ 0 mod N.
-/

open Matrix MatrixGroups

namespace NormalizerLean

theorem exists_coprime_lift (N : ℕ) [NeZero N] (c d : ℤ)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ d → (p : ℤ) ∣ N → False) :
    ∃ c' d' : ℤ, (N : ℤ) ∣ c' - c ∧ (N : ℤ) ∣ d' - d ∧ IsCoprime c' d' := by
  classical
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set c' : ℤ := if c = 0 then N else c with hc'def
  have hc'0 : c' ≠ 0 := by simp only [c']; split_ifs with h0 <;> assumption
  have hc'c : (N : ℤ) ∣ c' - c := by simp only [c']; split_ifs with h0 <;> simp [h0]
  set S : Finset ℕ := c'.natAbs.primeFactors.filter (fun p : ℕ => ¬ ((p : ℤ) ∣ d))
  set t : ℤ := ∏ p ∈ S, (p : ℤ)
  refine ⟨c', d + t * N, hc'c, ⟨t, by ring⟩, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  apply Nat.coprime_of_dvd
  intro p hp hpc hpd
  have hpc' : (p : ℤ) ∣ c' := Int.natCast_dvd.2 hpc
  have hpd' : (p : ℤ) ∣ d + t * N := Int.natCast_dvd.2 hpd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  by_cases hpdd : (p : ℤ) ∣ d
  · -- p ∤ t, so p ∣ N, so p ∣ c
    have hpt : ¬ (p : ℤ) ∣ t := by
      intro hpt
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hpZ _).1 hpt
      have hq' := Finset.mem_filter.1 hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).1 (Int.natCast_dvd_natCast.1 hpq)
      subst this
      exact hq'.2 hpdd
    have hptN : (p : ℤ) ∣ t * N := by
      have := dvd_sub hpd' hpdd; simpa using this
    have hpN : (p : ℤ) ∣ N := (hpZ.dvd_or_dvd hptN).resolve_left hpt
    have hpcc : (p : ℤ) ∣ c := by
      have := dvd_sub hpc' (hpN.trans hc'c); simpa using this
    exact h p hp hpcc hpdd hpN
  · -- p ∈ S, so p ∣ t, so p ∣ d
    have hpS : p ∈ S := Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpc, Int.natAbs_ne_zero.2 hc'0⟩, hpdd⟩
    have hpt : (p : ℤ) ∣ t := Finset.dvd_prod_of_mem _ hpS
    exact hpdd (by have := dvd_sub hpd' (dvd_mul_of_dvd_left hpt (N : ℤ)); simpa using this)

theorem redSL_surjective (N : ℕ) [NeZero N] : Function.Surjective (redSL N) := by
  intro A
  set a : ℤ := ((A 0 0).val : ℤ)
  set b : ℤ := ((A 0 1).val : ℤ)
  set c : ℤ := ((A 1 0).val : ℤ)
  set d : ℤ := ((A 1 1).val : ℤ)
  have ha : ((a : ℤ) : ZMod N) = A 0 0 := by simp [a]
  have hb : ((b : ℤ) : ZMod N) = A 0 1 := by simp [b]
  have hc : ((c : ℤ) : ZMod N) = A 1 0 := by simp [c]
  have hd : ((d : ℤ) : ZMod N) = A 1 1 := by simp [d]
  have hdvd : (N : ℤ) ∣ a * d - b * c - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha, hb, hc, hd]
    have := A.2
    rw [det_fin_two] at this
    rw [this, sub_self]
  obtain ⟨c', d', hc', hd', hcop⟩ := exists_coprime_lift N c d (fun p hp h1 h2 h3 => by
    have : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_sub (dvd_mul_of_dvd_right h2 a) (dvd_mul_of_dvd_right h1 b)) (h3.trans hdvd)
      simpa using this
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hp.one_lt.ne' (by exact_mod_cast this))
  obtain ⟨u, v, huv⟩ := hcop
  -- a₀ = v, b₀ = −u, x = a − v, y = b + u, m = y a₀ − x b₀
  have hdet'' : (v + ((b + u) * v + (a - v) * u) * c') * d' -
      (-u + ((b + u) * v + (a - v) * u) * d') * c' = 1 := by linear_combination huv
  have key : (N : ℤ) ∣ (b + u) * c' - (a - v) * d' := by
    obtain ⟨k1, hk1⟩ := hc'
    obtain ⟨k2, hk2⟩ := hd'
    obtain ⟨k3, hk3⟩ := hdvd
    exact ⟨-(a * k2 - b * k1 + k3), by linear_combination huv - a * hk2 + b * hk1 - hk3⟩
  obtain ⟨k, hk⟩ := key
  refine ⟨mkSL _ _ _ _ hdet'', ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · change ((((v + ((b + u) * v + (a - v) * u) * c') : ℤ)) : ZMod N) = A 0 0
    rw [← ha, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-(v * k), by linear_combination (-v) * hk + (-(a - v)) * huv⟩
  · change ((((-u + ((b + u) * v + (a - v) * u) * d') : ℤ)) : ZMod N) = A 0 1
    rw [← hb, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨u * k, by linear_combination u * hk + (-(b + u)) * huv⟩
  · change ((c' : ℤ) : ZMod N) = A 1 0
    rw [← hc, ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨k1, hk1⟩ := hc'
    exact ⟨-k1, by linear_combination -hk1⟩
  · change ((d' : ℤ) : ZMod N) = A 1 1
    rw [← hd, ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨k2, hk2⟩ := hd'
    exact ⟨-k2, by linear_combination -hk2⟩

end NormalizerLean
