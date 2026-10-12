import NormalizerDelta.Gamma1KK

/-!
# §K: the diamonds, the quotient (ℤ/2)^{ω(N)}, and the order 2^{ω(N)} φ(N)/2

* `eq_of_isAtkinLehner_both`: an element is an Atkin–Lehner element for at most one Q ∥ N (the (0,1)
  entries give y²Q' = y'²Q, while p ∣ Q, p ∤ Q' forces p ∤ y).
* `isAtkinLehner_mul_gen`: w_{Q₁} w_{Q₂} is an Atkin–Lehner element for (Q₁/G)(Q₂/G), G = gcd(Q₁, Q₂).
* σ(g) = (p ↦ [p ∣ Q(g)]) is a homomorphism Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} (N ≠ 4), trivial on
  ±Γ₁(N), onto (w_{Q_T}, Q_T = ∏_{p ∈ T} p^{v_p(N)}), with kernel the image of Γ₀(N).
* The diamonds Γ₀(N)/±Γ₁(N) have order [(ℤ/N)ˣ : {±1}] = φ(N)/2, and are normal since
  Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)) (for N = 4 because ±Γ₁(4) = Γ₀(4)).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Uniqueness of Q -/

theorem eq_of_isAtkinLehner_both [NeZero N] {Q Q' : ℕ} (hQ : Q ∣ N) (hQ' : Q' ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) (hg' : IsAtkinLehner N Q' g) : Q = Q' := by
  have hc := coprime_of_isAtkinLehner hQ hg
  have hc' := coprime_of_isAtkinLehner hQ' hg'
  -- one direction, then symmetry
  have key : ∀ {Q Q' : ℕ}, Q ∣ N → Q' ∣ N → Nat.Coprime Q (N / Q) → Nat.Coprime Q' (N / Q') →
      IsAtkinLehner N Q g → IsAtkinLehner N Q' g → ∀ p, p.Prime → p ∣ Q → p ∣ Q' := by
    intro Q Q' hQ hQ' hc hc' hg hg' p hp hpQ
    by_contra hpQ'
    obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
    obtain ⟨x', y', z', w', hdet', hgm'⟩ := hg'
    have hQ0 : Q ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
    have hQ0' : Q' ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ')
    -- p ∤ y: Q x w − (N/Q) y z = 1 and p ∣ Q
    obtain ⟨K, hK⟩ := hQ
    have hKdiv : N / Q = K := by rw [hK, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)]
    have hred : (Q : ℤ) * x * w - K * y * z = 1 := by
      apply mul_left_cancel₀ (show (Q : ℤ) ≠ 0 by exact_mod_cast hQ0)
      rw [hK] at hdet; push_cast at hdet; linear_combination hdet
    have hpy : ¬ (p : ℤ) ∣ y := by
      intro hpy
      have : (p : ℤ) ∣ 1 := by
        rw [← hred]
        exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hpQ) _) _)
          (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpy _) _)
      have := Int.eq_one_of_dvd_one (by positivity) this
      exact hp.one_lt.ne' (by exact_mod_cast this)
    -- the (0,1) entries: y² Q' = y'² Q
    have e01 := congrFun (congrFun (hgm.symm.trans hgm') 0) 1
    simp at e01
    have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ0
    have hQr' : (0 : ℝ) < Q' := by exact_mod_cast Nat.pos_of_ne_zero hQ0'
    have hsq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQr.le
    have hsq' : Real.sqrt Q' * Real.sqrt Q' = Q' := Real.mul_self_sqrt hQr'.le
    have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.2 hQr).ne'
    have hs' : Real.sqrt Q' ≠ 0 := (Real.sqrt_pos.2 hQr').ne'
    have hyy : (y : ℝ) ^ 2 * Q' = (y' : ℝ) ^ 2 * Q := by
      have h1 : (y : ℝ) * Real.sqrt Q' = y' * Real.sqrt Q := by
        field_simp at e01; linarith
      have := congrArg (· ^ 2) h1
      simp only [mul_pow, Real.sq_sqrt hQr.le, Real.sq_sqrt hQr'.le] at this
      exact this
    have hyyz : y ^ 2 * Q' = y' ^ 2 * Q := by exact_mod_cast hyy
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have : (p : ℤ) ∣ y ^ 2 * Q' := by
      rw [hyyz]; exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hpQ) _
    rcases hpZ.dvd_or_dvd this with h | h
    · exact hpy (hpZ.dvd_of_dvd_pow h)
    · exact hpQ' (Int.natCast_dvd_natCast.1 h)
  exact eq_of_exact_dvd hQ hQ' hc hc' (fun p hp =>
    ⟨key hQ hQ' hc hc' hg hg' p hp, key hQ' hQ hc' hc hg' hg p hp⟩)

/-! ### The general product law -/

theorem isAtkinLehner_mul_gen [NeZero N] {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N)
    {g₁ g₂ : SL(2, ℝ)} (h₁ : IsAtkinLehner N Q₁ g₁) (h₂ : IsAtkinLehner N Q₂ g₂) :
    IsAtkinLehner N (Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂)) (g₁ * g₂) := by
  have hQ10 : Q₁ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₁)
  have hQ20 : Q₂ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₂)
  obtain ⟨G, hGdef⟩ : ∃ G, G = Nat.gcd Q₁ Q₂ := ⟨_, rfl⟩
  rw [← hGdef]
  have hG0 : 0 < G := hGdef ▸ Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ10)
  obtain ⟨q₁, hq₁⟩ : G ∣ Q₁ := hGdef ▸ Nat.gcd_dvd_left Q₁ Q₂
  obtain ⟨q₂, hq₂⟩ : G ∣ Q₂ := hGdef ▸ Nat.gcd_dvd_right Q₁ Q₂
  have e1 : Q₁ / G = q₁ := by rw [hq₁, Nat.mul_div_cancel_left _ hG0]
  have e2 : Q₂ / G = q₂ := by rw [hq₂, Nat.mul_div_cancel_left _ hG0]
  rw [e1, e2]
  have hq10 : q₁ ≠ 0 := by rintro rfl; simp at hq₁; exact hQ10 hq₁
  have hq20 : q₂ ≠ 0 := by rintro rfl; simp at hq₂; exact hQ20 hq₂
  have hL : G * q₁ * q₂ ∣ N := by
    have h := Nat.lcm_dvd hQ₁ hQ₂
    have : Nat.lcm Q₁ Q₂ = G * q₁ * q₂ := by
      rw [Nat.lcm, ← hGdef, hq₁, hq₂]
      rw [show G * q₁ * (G * q₂) = G * (G * q₁ * q₂) by ring, Nat.mul_div_cancel_left _ hG0]
    rwa [this] at h
  obtain ⟨L, hLN⟩ := hL
  obtain ⟨x₁, y₁, z₁, w₁, hd₁, hg₁⟩ := h₁
  obtain ⟨x₂, y₂, z₂, w₂, hd₂, hg₂⟩ := h₂
  have hGz : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
  have hq1z : (q₁ : ℤ) ≠ 0 := by exact_mod_cast hq10
  have hq2z : (q₂ : ℤ) ≠ 0 := by exact_mod_cast hq20
  have r₁ : (G : ℤ) * q₁ * x₁ * w₁ - q₂ * L * y₁ * z₁ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq1z)
    rw [hq₁, hLN] at hd₁; push_cast at hd₁; linear_combination hd₁
  have r₂ : (G : ℤ) * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq2z)
    rw [hq₂, hLN] at hd₂; push_cast at hd₂; linear_combination hd₂
  refine ⟨G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
    L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
  · rw [hLN]; push_cast
    linear_combination ((q₁ : ℤ) * q₂ * (G * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂)) * r₁ +
      ((q₁ : ℤ) * q₂) * r₂
  · have hsq : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt ((q₁ * q₂ : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _), hq₁, hq₂]
      push_cast
      rw [show (G : ℝ) * q₁ * (G * q₂) = G ^ 2 * (q₁ * q₂) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
    have hs1 : Real.sqrt Q₁ ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hQ10)).ne'
    have hs2 : Real.sqrt Q₂ ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hQ20)).ne'
    have hGr : (G : ℝ) ≠ 0 := by exact_mod_cast hG0.ne'
    rw [Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← mul_inv, hsq, mul_inv, mul_comm (G : ℝ)⁻¹, mul_smul]
    congr 1
    rw [hLN, hq₁, hq₂]
    push_cast
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring

/-! ### Exact divisors -/

theorem factorization_exact {Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hc : Nat.Coprime Q (N / Q)) (p : ℕ) :
    Q.factorization p = 0 ∨ Q.factorization p = N.factorization p := by
  by_cases hp : p.Prime
  swap
  · left; exact Nat.factorization_eq_zero_of_not_prime _ hp
  by_cases hpQ : p ∣ Q
  · right
    have hN := NeZero.ne N
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ)
    have hK0 : N / Q ≠ 0 := by
      intro h0; rw [Nat.div_eq_zero_iff_lt (Nat.pos_of_ne_zero hQ0)] at h0
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hQ) (by omega)
    have hpK : ¬ p ∣ N / Q := fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpQ hc) hd
    have hNR : N = Q * (N / Q) := (Nat.mul_div_cancel' hQ).symm
    conv_rhs => rw [hNR]
    rw [Nat.factorization_mul hQ0 hK0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpK,
      add_zero]
  · left; exact Nat.factorization_eq_zero_of_not_dvd hpQ

/-- For exact divisors Q₁, Q₂ and a prime p ∣ N, p divides (Q₁/G)(Q₂/G) iff it divides exactly one. -/
theorem dvd_mul_div_gcd_iff {Q₁ Q₂ p : ℕ} [NeZero N] (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N)
    (hc₁ : Nat.Coprime Q₁ (N / Q₁)) (hc₂ : Nat.Coprime Q₂ (N / Q₂)) (hp : p.Prime) (hpN : p ∣ N) :
    p ∣ Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ↔ ¬ (p ∣ Q₁ ↔ p ∣ Q₂) := by
  have hN := NeZero.ne N
  have hQ10 : Q₁ ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ₁)
  have hQ20 : Q₂ ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ₂)
  set G := Nat.gcd Q₁ Q₂
  have hG0 : G ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ10)).ne'
  have hR0 : Q₁ / G * (Q₂ / G) ≠ 0 := mul_ne_zero
    (Nat.div_ne_zero_iff_of_dvd (Nat.gcd_dvd_left _ _) |>.2 ⟨hQ10, hG0⟩)
    (Nat.div_ne_zero_iff_of_dvd (Nat.gcd_dvd_right _ _) |>.2 ⟨hQ20, hG0⟩)
  have hfac : (Q₁ / G * (Q₂ / G)).factorization p + 2 * G.factorization p =
      Q₁.factorization p + Q₂.factorization p := by
    have h : Q₁ / G * (Q₂ / G) * G ^ 2 = Q₁ * Q₂ := by
      rw [pow_two]
      calc Q₁ / G * (Q₂ / G) * (G * G) = (Q₁ / G * G) * (Q₂ / G * G) := by ring
        _ = Q₁ * Q₂ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),
          Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
    have := congrArg (fun m => m.factorization p) h
    rw [Nat.factorization_mul hR0 (pow_ne_zero 2 hG0), Nat.factorization_mul hQ10 hQ20,
      Nat.factorization_pow] at this
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
    omega
  have hG : G.factorization p = min (Q₁.factorization p) (Q₂.factorization p) := by
    rw [Nat.factorization_gcd hQ10 hQ20]; rfl
  have hν : 0 < N.factorization p := hp.factorization_pos_of_dvd hN hpN
  rw [hp.dvd_iff_one_le_factorization hR0, hp.dvd_iff_one_le_factorization hQ10,
    hp.dvd_iff_one_le_factorization hQ20]
  rcases factorization_exact hQ₁ hc₁ p with h1 | h1 <;>
    rcases factorization_exact hQ₂ hc₂ p with h2 | h2 <;> omega

/-! ### Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)); the diamonds are normal -/

theorem normG_pmGamma1R_le_Norm0 (N : ℕ) [NeZero N] : NormG (pmGamma1R N) ≤ Norm0 N := by
  by_cases hN4 : N = 4
  · subst hN4; rw [pmGamma1R_four']
  · intro g hg
    obtain ⟨Q, hQ, -, hAL⟩ := (normG_pmGamma1R' hN4 g).1 hg
    exact isAtkinLehner_mem_normalizer' hQ hAL

theorem diamonds_normal' (N : ℕ) [NeZero N] : (diamonds N).Normal := by
  have hle := normG_pmGamma1R_le_Norm0 N
  have hK : ((Gamma0R N).subgroupOf (NormG (pmGamma1R N))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hle g.2) n).1 hn⟩
  exact hK.map _ (QuotientGroup.mk'_surjective _)

/-! ### The order of the diamonds -/

theorem card_pmOne {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) : Nat.card (pmOne N) = 2 := by
  haveI : Fact (2 < N) := ⟨by omega⟩
  unfold pmOne
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · simp
  · intro h
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    exact ZMod.neg_one_ne_one this

theorem index_pmOne {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) : (pmOne N).index = N.totient / 2 := by
  have h := (pmOne N).index_mul_card
  rw [card_pmOne hN3, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
  omega

theorem card_diamonds' {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) : Nat.card (diamonds N) = N.totient / 2 := by
  set Nn := NormG (pmGamma1R N)
  set K := (Gamma0R N).subgroupOf Nn
  set H := (pmGamma1R N).subgroupOf Nn
  set f := (QuotientGroup.mk' H).comp K.subtype
  have hrange : f.range = diamonds N := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl
  have hker : f.ker = H.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype,
      QuotientGroup.eq_one_iff]
  rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.relIndex,
    Subgroup.relIndex_subgroupOf (Gamma0R_le_normG_pmGamma1R' N), pmGamma1R, GammaDeltaR, toR,
    Gamma0R, Subgroup.relIndex_map_map_of_injective _ _ ofZ_injective, relindex_GammaDelta',
    index_pmOne hN3]

/-! ### σ : Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} -/

section Sigma

variable [NeZero N] (hN : N ≠ 4)

/-- The Q of an element of Nor(±Γ₁(N)) (N ≠ 4). -/
def Qof (g : NormG (pmGamma1R N)) : ℕ := Classical.choose ((normG_pmGamma1R' hN g).1 g.2)

theorem Qof_spec (g : NormG (pmGamma1R N)) :
    Qof hN g ∣ N ∧ Nat.Coprime (Qof hN g) (N / Qof hN g) ∧ IsAtkinLehner N (Qof hN g) g :=
  Classical.choose_spec ((normG_pmGamma1R' hN g).1 g.2)

theorem Qof_eq {g : NormG (pmGamma1R N)} {Q : ℕ} (hQ : Q ∣ N) (hg : IsAtkinLehner N Q g) :
    Qof hN g = Q :=
  eq_of_isAtkinLehner_both (Qof_spec hN g).1 hQ (Qof_spec hN g).2.2 hg

/-- [p ∣ Q] ∈ ℤ/2. -/
def chiQ (Q p : ℕ) : ZMod 2 := if p ∣ Q then 1 else 0

theorem Qof_one : Qof hN 1 = 1 :=
  Qof_eq hN (one_dvd N) ((isAtkinLehner_one_iff' N 1).2 (Subgroup.one_mem _))

theorem mul_div_gcd_dvd {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N) :
    Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ N := by
  have h1 : Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ Q₁ / Nat.gcd Q₁ Q₂ * Q₂ :=
    mul_dvd_mul_left _ (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
  have h2 : Q₁ / Nat.gcd Q₁ Q₂ * Q₂ = Nat.lcm Q₁ Q₂ := by
    rw [Nat.lcm, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]
  rw [h2] at h1
  exact h1.trans (Nat.lcm_dvd hQ₁ hQ₂)

theorem chiQ_mul (g g' : NormG (pmGamma1R N)) (p : N.primeFactors) :
    chiQ (Qof hN (g * g')) p = chiQ (Qof hN g) p + chiQ (Qof hN g') p := by
  obtain ⟨h1, c1, a1⟩ := Qof_spec hN g
  obtain ⟨h2, c2, a2⟩ := Qof_spec hN g'
  have hmul := isAtkinLehner_mul_gen h1 h2 a1 a2
  rw [Qof_eq hN (g := g * g') (mul_div_gcd_dvd h1 h2) hmul]
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpN := Nat.dvd_of_mem_primeFactors p.2
  have key := dvd_mul_div_gcd_iff h1 h2 c1 c2 hp hpN
  unfold chiQ
  by_cases hq1 : (p : ℕ) ∣ Qof hN g <;> by_cases hq2 : (p : ℕ) ∣ Qof hN g' <;>
    simp only [hq1, hq2, iff_true, iff_false, true_iff, false_iff, not_true, not_false_eq_true] at key <;>
    simp [key, hq1, hq2] <;> decide

/-- σ on the normalizer: g ↦ (p ↦ [p ∣ Q(g)]). -/
def sigmaG : NormG (pmGamma1R N) →* (N.primeFactors → Multiplicative (ZMod 2)) where
  toFun g := fun p => Multiplicative.ofAdd (chiQ (Qof hN g) p)
  map_one' := by
    funext p
    have hp := Nat.prime_of_mem_primeFactors p.2
    simp [Qof_one, chiQ, hp.one_lt.ne']
  map_mul' g g' := by
    funext p
    simp only [Pi.mul_apply]
    rw [chiQ_mul, ofAdd_add]

theorem sigmaG_eq_one_of_mem_Gamma0R {g : NormG (pmGamma1R N)} (hg : (g : SL(2, ℝ)) ∈ Gamma0R N) :
    sigmaG hN g = 1 := by
  funext p
  have hp := Nat.prime_of_mem_primeFactors p.2
  simp [sigmaG, Qof_eq hN (one_dvd N) ((isAtkinLehner_one_iff' N g).2 hg), chiQ, hp.one_lt.ne']

/-- σ on Nor(±Γ₁(N))/±Γ₁(N). -/
def sigma1 : BG (pmGamma1R N) →* (N.primeFactors → Multiplicative (ZMod 2)) :=
  QuotientGroup.lift _ (sigmaG hN) (fun g hg => by
    rw [Subgroup.mem_subgroupOf] at hg
    exact sigmaG_eq_one_of_mem_Gamma0R hN (GammaDeltaR_le_Gamma0R hg))

theorem sigma1_mk (g : NormG (pmGamma1R N)) :
    sigma1 hN (QuotientGroup.mk g) = sigmaG hN g := rfl

theorem dvd_prod_mPart_iff {T : Finset ℕ} (hT : T ⊆ N.primeFactors) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p ∣ ∏ q ∈ T, mPart N q ↔ p ∈ T := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).1 h
    have hqp := Nat.prime_of_mem_primeFactors (hT hq)
    have := (Nat.prime_dvd_prime_iff_eq hpp hqp).1 (hpp.dvd_of_dvd_pow hpq)
    rwa [this]
  · intro h
    refine (dvd_pow_self p ?_).trans (Finset.dvd_prod_of_mem (fun q => mPart N q) h)
    exact (hpp.factorization_pos_of_dvd (NeZero.ne N) (Nat.dvd_of_mem_primeFactors hp)).ne'

end Sigma

/-- The quotient by the diamonds is (ℤ/2)^{ω(N)}. -/
theorem BG_pmGamma1R_mod_diamonds' {N : ℕ} [NeZero N] (hN : N ≠ 4) :
    ∃ σ : BG (pmGamma1R N) →* (N.primeFactors → Multiplicative (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = diamonds N ∧
      ∀ (Q : ℕ) (g : SL(2, ℝ)) (x : BG (pmGamma1R N)), Q ∣ N → IsAtkinLehner N Q g →
        x.IsClassOf g → σ x = fun p : N.primeFactors =>
          if (p : ℕ) ∣ Q then Multiplicative.ofAdd (1 : ZMod 2) else 1 := by
  classical
  have hval : ∀ (Q : ℕ) (g : SL(2, ℝ)) (x : BG (pmGamma1R N)), Q ∣ N → IsAtkinLehner N Q g →
      x.IsClassOf g → sigma1 hN x = fun p : N.primeFactors =>
        if (p : ℕ) ∣ Q then Multiplicative.ofAdd (1 : ZMod 2) else 1 := by
    rintro Q g x hQ hg ⟨hgN, rfl⟩
    rw [sigma1_mk]
    funext p
    simp only [sigmaG, MonoidHom.coe_mk, OneHom.coe_mk, chiQ]
    rw [Qof_eq hN (g := ⟨g, hgN⟩) hQ hg]
    split_ifs <;> rfl
  refine ⟨sigma1 hN, ?_, ?_, hval⟩
  · intro f
    set T := N.primeFactors.filter
      (fun q => ∃ hq : q ∈ N.primeFactors, Multiplicative.toAdd (f ⟨q, hq⟩) = 1)
    have hT : T ⊆ N.primeFactors := Finset.filter_subset _ _
    obtain ⟨g, hg, -⟩ := AL_prod_mem hT
    have hQ := prod_mPart_dvd (NeZero.ne N) hT
    have hgN := isAtkinLehner_mem_normG_pmGamma1R' hQ hg
    refine ⟨QuotientGroup.mk ⟨g, hgN⟩, ?_⟩
    rw [hval _ g _ hQ hg ⟨hgN, rfl⟩]
    funext p
    have hdiv := dvd_prod_mPart_iff hT p.2
    have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    by_cases hpT : (p : ℕ) ∈ T
    · rw [if_pos (hdiv.2 hpT)]
      obtain ⟨-, hp', hfp⟩ := Finset.mem_filter.1 hpT
      rw [← hfp]; rfl
    · rw [if_neg (fun h => hpT (hdiv.1 h))]
      have : Multiplicative.toAdd (f p) ≠ 1 := fun h =>
        hpT (Finset.mem_filter.2 ⟨p.2, p.2, h⟩)
      rcases h01 (Multiplicative.toAdd (f p)) with h | h
      · change (1 : Multiplicative (ZMod 2)) = f p
        rw [← ofAdd_toAdd (f p), h]; rfl
      · exact absurd h this
  · ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
    rw [MonoidHom.mem_ker, sigma1_mk]
    have hiff : sigmaG hN g = 1 ↔ (g : SL(2, ℝ)) ∈ Gamma0R N := by
      constructor
      · intro h1
        have hQ1 : Qof hN g = 1 := by
          by_contra hne
          obtain ⟨p, hp, hpQ⟩ := Nat.exists_prime_and_dvd hne
          have hpN : p ∈ N.primeFactors :=
            Nat.mem_primeFactors.2 ⟨hp, hpQ.trans (Qof_spec hN g).1, NeZero.ne N⟩
          have := congrFun h1 ⟨p, hpN⟩
          simp [sigmaG, chiQ, hpQ] at this
        have := (Qof_spec hN g).2.2
        rw [hQ1] at this
        exact (isAtkinLehner_one_iff' N g).1 this
      · exact sigmaG_eq_one_of_mem_Gamma0R hN
    rw [hiff]
    constructor
    · intro hg
      exact ⟨⟨g, g.2⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
    · rintro ⟨k, hk, hkg⟩
      have hk' : (k : SL(2, ℝ)) ∈ Gamma0R N := hk
      have h3 : k⁻¹ * g ∈ (pmGamma1R N).subgroupOf (NormG (pmGamma1R N)) :=
        QuotientGroup.eq.1 hkg
      have h2 : ((k⁻¹ * g : NormG (pmGamma1R N)) : SL(2, ℝ)) ∈ Gamma0R N :=
        GammaDeltaR_le_Gamma0R (Subgroup.mem_subgroupOf.1 h3)
      have : (g : SL(2, ℝ)) = k * (k⁻¹ * g : NormG (pmGamma1R N)) := by simp
      rw [this]
      exact Subgroup.mul_mem _ hk' h2

/-- **The order of the modular automorphism group of X₁(N).** -/
theorem card_BG_pmGamma1R' {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN4 : N ≠ 4) :
    Nat.card (BG (pmGamma1R N)) = 2 ^ N.primeFactors.card * (N.totient / 2) := by
  obtain ⟨σ, hs, hk, -⟩ := BG_pmGamma1R_mod_diamonds' hN4
  have h1 := σ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, hk,
    card_diamonds' hN3] at h1
  rw [← h1, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, Finset.prod_const, mul_comm]

end

end NormalizerLean
