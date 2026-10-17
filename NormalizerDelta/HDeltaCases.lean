module

public import NormalizerDelta.MDelta

@[expose] public section

/-!
# §H: h_Δ = h(N) unless one of the cases i)–iii) of `hDelta_eq_hPart_iff`, and conversely

Prime by prime: v_p(h_Δ) = min(v_p(ε_Δ), ⌊v_p(N)/2⌋) and v_p(h(N)) = min(v_p(gcd(N, 24)), ⌊v_p(N)/2⌋), with
v_p(gcd(N, 24)) ≤ v_p(ε_Δ) ≤ v_p(N).  So v_p(h_Δ) ≠ v_p(h(N)) iff
* p ≥ 5: p² ∣ N and p ∣ ε_Δ;   * p = 3: 3⁴ ∣ N and 9 ∣ ε_Δ;   * p = 2: 2⁸ ∣ N and 16 ∣ ε_Δ
(`omega`), and m ∣ ε_Δ iff m ∣ d² − 1 for all d ∈ Δ, where p ∣ d² − 1 ⟺ d ≡ ±1 (p), 9 ∣ d² − 1 ⟺ d ≡ ±1 (9),
16 ∣ d² − 1 ⟺ d ≡ ±1 (8) (`decide` on ℤ/9, ℤ/16).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

theorem isPmOneMod_iff_val [NeZero N] (m : ℕ) (u : (ZMod N)ˣ) :
    IsPmOneMod m u ↔ (((u : ZMod N).val : ℕ) : ZMod m) = 1 ∨ (((u : ZMod N).val : ℕ) : ZMod m) = -1 := by
  unfold IsPmOneMod; rw [ZMod.cast_eq_val]

theorem dvd_sq_sub_one_iff {m x : ℕ} (hx : 1 ≤ x) : m ∣ x ^ 2 - 1 ↔ (x : ZMod m) ^ 2 = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx), sub_eq_zero]; push_cast; rfl

theorem dvd_val_sq_iff_prime [NeZero N] {p : ℕ} (hp : p.Prime) (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    p ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod p u := by
  haveI := Fact.mk hp
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val, sq]
  exact mul_self_eq_one_iff

theorem zmod9_sq_eq_one : ∀ y : ZMod 9, y ^ 2 = 1 ↔ y = 1 ∨ y = -1 := by decide

theorem dvd_val_sq_iff_nine [NeZero N] (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    9 ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod 9 u := by
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val]
  exact zmod9_sq_eq_one _

theorem zmod16_sq_eq_one : ∀ y : ZMod 16, y ^ 2 = 1 ↔
    (ZMod.castHom (show 8 ∣ 16 by norm_num) (ZMod 8) y = 1 ∨
      ZMod.castHom (show 8 ∣ 16 by norm_num) (ZMod 8) y = -1) := by decide

theorem dvd_val_sq_iff_sixteen [NeZero N] (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    16 ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod 8 u := by
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val, zmod16_sq_eq_one, map_natCast]

/-- The local criterion at a prime p. -/
theorem factorization_hDelta_ne_iff [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {p : ℕ} (hp : p.Prime) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      (5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod p u) ∨ (p = 3 ∧ 3 ^ 4 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 9 u) ∨
        (p = 2 ∧ 2 ^ 8 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 8 u) := by
  have hN := NeZero.ne N
  have hε0 : epsDelta N Δ ≠ 0 := epsDelta_pos.ne'
  rw [factorization_hDelta, (local_constants (p := p) hN).2]
  have hle : (epsPart N).factorization p ≤ (epsDelta N Δ).factorization p :=
    (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)).ne' hε0).2
      (gcd24_dvd_epsDelta Δ) p
  have heν : (epsDelta N Δ).factorization p ≤ N.factorization p :=
    (Nat.factorization_le_iff_dvd hε0 hN).2 epsDelta_dvd p
  -- m ∣ ε_Δ ⟺ ∀ u ∈ Δ, …, given m ∣ N
  have hconv : ∀ {m m' : ℕ}, m ∣ N → 2 ≤ N →
      (∀ u : (ZMod N)ˣ, m ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod m' u) →
      (m ∣ epsDelta N Δ ↔ ∀ u ∈ Δ, IsPmOneMod m' u) := by
    intro m m' hmN _ hiff
    rw [dvd_epsDelta_iff]
    exact ⟨fun h u hu => (hiff u).1 (h.2 u hu), fun h => ⟨hmN, fun u hu => (hiff u).2 (h u hu)⟩⟩
  have hN2 : ∀ {q : ℕ}, 2 ≤ q → q ∣ N → 2 ≤ N := fun hq hqN =>
    le_trans hq (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hqN)
  have hg : (epsPart N).factorization p =
      min (N.factorization p) (if p = 2 then 3 else if p = 3 then 1 else 0) := by
    rw [factorization_epsPart hN, factorization_24]
  by_cases h2 : p = 2
  · -- p = 2
    subst h2
    rw [if_pos rfl] at hg
    rw [hg] at hle ⊢
    have e1 : 2 ^ 8 ∣ N ↔ 8 ≤ N.factorization 2 := Nat.prime_two.pow_dvd_iff_le_factorization hN
    have e2 : 2 ^ 4 ∣ epsDelta N Δ ↔ 4 ≤ (epsDelta N Δ).factorization 2 :=
      Nat.prime_two.pow_dvd_iff_le_factorization hε0
    constructor
    · intro hne
      have h256 : 2 ^ 8 ∣ N := e1.2 (by omega)
      have h16 : 16 ∣ N := (pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans h256
      refine Or.inr (Or.inr ⟨rfl, h256, ?_⟩)
      exact (hconv h16 (hN2 (by norm_num) h16) (dvd_val_sq_iff_sixteen (hN2 (by norm_num) h16))).1
        (e2.2 (by omega))
    · rintro (⟨h5, -⟩ | ⟨h3, -⟩ | ⟨-, h256, h8⟩)
      · omega
      · omega
      have h16 : 16 ∣ N := (pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans h256
      have := e2.1 ((hconv h16 (hN2 (by norm_num) h16)
        (dvd_val_sq_iff_sixteen (hN2 (by norm_num) h16))).2 h8)
      have := e1.1 h256
      omega
  by_cases h3 : p = 3
  · -- p = 3
    subst h3
    rw [if_neg (by norm_num : (3 : ℕ) ≠ 2), if_pos rfl] at hg
    rw [hg] at hle ⊢
    have e1 : 3 ^ 4 ∣ N ↔ 4 ≤ N.factorization 3 := Nat.prime_three.pow_dvd_iff_le_factorization hN
    have e2 : 3 ^ 2 ∣ epsDelta N Δ ↔ 2 ≤ (epsDelta N Δ).factorization 3 :=
      Nat.prime_three.pow_dvd_iff_le_factorization hε0
    constructor
    · intro hne
      have h81 : 3 ^ 4 ∣ N := e1.2 (by omega)
      have h9 : 9 ∣ N := (pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h81
      refine Or.inr (Or.inl ⟨rfl, h81, ?_⟩)
      exact (hconv h9 (hN2 (by norm_num) h9) (dvd_val_sq_iff_nine (hN2 (by norm_num) h9))).1
        (e2.2 (by omega))
    · rintro (⟨h5, -⟩ | ⟨-, h81, h9'⟩ | ⟨h3, -⟩)
      · omega
      · have h9 : 9 ∣ N := (pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h81
        have := e2.1 ((hconv h9 (hN2 (by norm_num) h9)
          (dvd_val_sq_iff_nine (hN2 (by norm_num) h9))).2 h9')
        have := e1.1 h81
        omega
      · omega
  · -- p ≥ 5
    rw [if_neg h2, if_neg h3, min_zero] at hg
    rw [hg] at hle ⊢
    have h5 : 5 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
      omega
    have e1 : p ^ 2 ∣ N ↔ 2 ≤ N.factorization p := hp.pow_dvd_iff_le_factorization hN
    have e2 : p ^ 1 ∣ epsDelta N Δ ↔ 1 ≤ (epsDelta N Δ).factorization p :=
      hp.pow_dvd_iff_le_factorization hε0
    rw [pow_one] at e2
    have hp2N : ∀ {q : ℕ}, q ^ 2 ∣ N → q ∣ N := fun h => (dvd_pow_self _ two_ne_zero).trans h
    constructor
    · intro hne
      have hpp : p ^ 2 ∣ N := e1.2 (by omega)
      refine Or.inl ⟨h5, hpp, ?_⟩
      exact (hconv (hp2N hpp) (hN2 hp.two_le (hp2N hpp)) (dvd_val_sq_iff_prime hp
        (hN2 hp.two_le (hp2N hpp)))).1 (e2.2 (by omega))
    · rintro (⟨-, hpp, hpm⟩ | ⟨h3', -⟩ | ⟨h2', -⟩)
      · have := e2.1 ((hconv (hp2N hpp) (hN2 hp.two_le (hp2N hpp)) (dvd_val_sq_iff_prime hp
          (hN2 hp.two_le (hp2N hpp)))).2 hpm)
        have := e1.1 hpp
        omega
      · exact absurd h3' h3
      · exact absurd h2' h2

theorem hDelta_eq_hPart_iff' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  constructor
  · intro h habc
    rcases habc with ⟨p, hp, h5, hp2, hpm⟩ | ⟨h81, h9⟩ | ⟨h256, h8⟩
    · exact (factorization_hDelta_ne_iff Δ hp).2 (Or.inl ⟨h5, hp2, hpm⟩) (by rw [h])
    · exact (factorization_hDelta_ne_iff Δ Nat.prime_three).2 (Or.inr (Or.inl ⟨rfl, h81, h9⟩))
        (by rw [h])
    · exact (factorization_hDelta_ne_iff Δ Nat.prime_two).2 (Or.inr (Or.inr ⟨rfl, h256, h8⟩))
        (by rw [h])
  · intro hn
    apply Nat.eq_of_factorization_eq (hDelta_ne_zero Δ) (hPart_pos N).ne'
    intro p
    by_cases hp : p.Prime
    swap
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    by_contra hne
    rcases (factorization_hDelta_ne_iff Δ hp).1 hne with ⟨h5, h2, h⟩ | ⟨rfl, h81, h9⟩ |
      ⟨rfl, h256, h8⟩
    · exact hn (Or.inl ⟨p, hp, h5, h2, h⟩)
    · exact hn (Or.inr (Or.inl ⟨h81, h9⟩))
    · exact hn (Or.inr (Or.inr ⟨h256, h8⟩))

end

end NormalizerLean
