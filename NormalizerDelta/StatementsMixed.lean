module

public import NormalizerDelta.DefsMixed

@[expose] public section

/-!
# Part 8. Mixed level (2026-10-19): statements (Stage 0, all `sorry`)

Definitions: `NormalizerLean/Defs.lean`, Part 8.  Throughout, N₁ and N₂ are coprime, H₁ ≤ SL₂(ℤ/N₁),
H₂ ≤ SL₂(ℤ/N₂), and Γ = Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) (`GammaH N₁ H₁ ⊓ GammaH N₂ H₂`), which is Γ_H for H = H₁ × H₂.
"H₁ is of type I" is the hypothesis `hloc` of Part 6's `normG_GammaH` at level N₁: for every prime p ∣ N₁, H₁ mod p
fixes no line of F_p², or H₁ mod p^{v_p(N₁)} lies in a split Cartan subgroup.  H₂ is arbitrary.  Det(H₁)
(`IsNormDet`) is the set of determinants of the normalizer of H₁ in GL₂(ℤ/N₁); it contains the squares.  As in
Parts 6 and 7, the quotients are Nor_{SL₂(ℝ)}(Γ)/Γ, and −1 ∈ Γ is not assumed.

* §A, structure.  For H₁ of type I, every x = (det m)^{-1/2}·m ∈ Nor(Γ) has det m prime to N₁, and
  Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)).  With no condition on H₁:
  * x ∈ Nor(Γ_{H₂}(N₂)) normalizes Γ iff m mod N₁ normalizes H₁;
  * Nor(Γ) ∩ Γ_{H₂}(N₂) = Γ_{N(H₁)}(N₁) ∩ Γ_{H₂}(N₂), of index [N(H₁) : H₁] over Γ;
  * the coset x·Γ_{H₂}(N₂) meets Nor(Γ) iff det m mod N₁ ∈ Det(H₁).
* §B, the order (H₁ of type I).
  * In general, |Nor(Γ)/Γ| = [N(H₁) : H₁] · #{x̄ ∈ Nor(Γ_{H₂})/Γ_{H₂} : det m_x mod N₁ ∈ Det(H₁)}. This is a plain
    product when Det(H₁) = (ℤ/N₁)ˣ.
  * For Γ_Δ(N₂) (Part 7): [N(H₁) : H₁] · i_Δ · ψ(N₂)/ψ(n*) · #{Q ∥ n* : ι*_Q(Δ̄) = Δ̄, Q mod N₁ ∈ Det(H₁)}. The
    Atkin–Lehner element w_Q of Part 7 survives iff Q mod N₁ ∈ Det(H₁).
  * For H₂ of prime level p with exactly one fixed line (Part 6, §P):
    [N(H₁) : H₁] · [N(H₂) : H₂] · (2 if p mod N₁ ∈ Det(H₁), else 1).
* §C, corollaries.
  * Γ(N₁) ∩ Γ_{H₂}(N₂) has order |SL₂(ℤ/N₁)| · |Nor(Γ_{H₂})/Γ_{H₂}|.
  * Γ_ns⁺(p) ∩ Γ_{H₂}(N₂) (p ≥ 5) and Γ_sp⁺(p) ∩ Γ_{H₂}(N₂) (p ≥ 7) have the same order as Γ_{H₂}(N₂).
* §S, sanity: for Q₈ ≤ SL₂(F₇), Det(Q₈) is the set of squares, so the Fricke involution of X₀(3) does not survive.
  |Nor(Γ)/Γ| is 6 for Γ_{Q₈}(7), 12 for Γ_{Q₈}(7) ∩ Γ₀(2), and 6 (not 12) for Γ_{Q₈}(7) ∩ Γ₀(3).

For −1 ∈ Γ the orders are numbers of modular automorphisms (Part 6, `BQ_equiv_BG`).  The script
`scripts/check_mixed_statements.py` compares §A–§S with a brute-force computation of Nor(Γ)/Γ (DLM26, Prop. 4.3)
for N₁ ∈ {1, 2, 3, 4, 5, 7, 8, 9} and every H₁ up to conjugacy, with H₂ = H_Δ for every Δ (N ≤ 30) or every
H₂ up to conjugacy at N₂ ≤ 7 (N ≤ 36): 3716 cases, in 66 of which Det(H₁) removes classes, and 143 cases for §C
(output `scripts/check_mixed_statements_output.txt`).
Sources: §A builds on DLM26, Prop. 4.5(1), (4) (det m prime to N₁, as in Part 6), and on J. Box, "Computing
models for quotients of modular curves", Res. Number Theory 7 (2021), arXiv:2101.03797, Lemma 2.7: an
η ∈ GL₂(ℤ/N₁) normalizing H₁ with det η ≡ det m mod N₁ lifts the automorphism of X_{H₂} given by m (the ⇐ of
`exists_mul_mem_normG_inf_iff`).  DLM22 (arXiv:2005.09009v2), Prop. 5.6, is the case of Cartan groups and
N₂ = 2.  The other statements were not found in this form in the literature checked (2026-10-19; the search
was not exhaustive).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## §A. Structure -/

/-- For H₁ of type I, every x = (det m)^{-1/2}·m ∈ Nor(Γ) (m integral, det m > 0, no prime of N₁ dividing all the
entries of m) has det m prime to N₁. -/
theorem isUnit_det_of_mem_normG_inf {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ N₁ → ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) :
    IsUnit ((m.det : ℤ) : ZMod N₁) := by
  sorry

/-- For H₁ of type I, Nor(Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂)) ≤ Nor(Γ_{H₂}(N₂)). -/
theorem normG_inf_le {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p)) :
    NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ≤ NormG (toR (GammaH N₂ H₂)) := by
  sorry

/-- For every H₁: an x = (det m)^{-1/2}·m ∈ Nor(Γ_{H₂}(N₂)) with det m prime to N₁ normalizes Γ iff m mod N₁
normalizes H₁. -/
theorem mem_normG_inf_iff {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂))) :
    projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ↔
      NormalizesMat H₁ (m.map (Int.cast : ℤ → ZMod N₁)) := by
  sorry

/-- For every H₁: Nor(Γ) ∩ Γ_{H₂}(N₂) = Γ_{N(H₁)}(N₁) ∩ Γ_{H₂}(N₂). -/
theorem normG_inf_inf_eq {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) :
    NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ⊓ toR (GammaH N₂ H₂) =
      toR (GammaH N₁ (NormH H₁) ⊓ GammaH N₂ H₂) := by
  sorry

/-- For every H₁: [Nor(Γ) ∩ Γ_{H₂}(N₂) : Γ] = [N(H₁) : H₁]. -/
theorem relIndex_inf_normG {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) :
    (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)).relIndex
        (NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂)) ⊓ toR (GammaH N₂ H₂)) =
      H₁.relIndex (NormH H₁) := by
  sorry

/-- For every H₁: the coset x·Γ_{H₂}(N₂) of x = (det m)^{-1/2}·m ∈ Nor(Γ_{H₂}(N₂)), det m prime to N₁, meets Nor(Γ)
iff det m mod N₁ ∈ Det(H₁). -/
theorem exists_mul_mem_normG_inf_iff {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₁ : Subgroup SL(2, ZMod N₁)) (H₂ : Subgroup SL(2, ZMod N₂)) {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hunit : IsUnit ((m.det : ℤ) : ZMod N₁))
    (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ H₂))) :
    (∃ γ ∈ GammaH N₂ H₂,
        projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ ∈ NormG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) ↔
      IsNormDet H₁ ((m.det : ℤ) : ZMod N₁) := by
  sorry

/-! ## §B. The order -/

/-- **The order**, for H₁ of type I and every H₂: |Nor(Γ)/Γ| = [N(H₁) : H₁] times the number of classes
x̄ ∈ Nor(Γ_{H₂})/Γ_{H₂} with det m_x mod N₁ ∈ Det(H₁). -/
theorem card_BG_inf {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) =
      H₁.relIndex (NormH H₁) *
        Nat.card {x : BG (toR (GammaH N₂ H₂)) // ∃ g, x.IsClassOf g ∧ HasNormDet H₁ g} := by
  sorry

/-- If moreover Det(H₁) = (ℤ/N₁)ˣ: |Nor(Γ)/Γ| = [N(H₁) : H₁] · |Nor(Γ_{H₂})/Γ_{H₂}|. -/
theorem card_BG_inf_of_isNormDet {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)} (H₂ : Subgroup SL(2, ZMod N₂))
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    (hall : ∀ u : (ZMod N₁)ˣ, IsNormDet H₁ u) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH N₂ H₂))) =
      H₁.relIndex (NormH H₁) * Nat.card (BG (toR (GammaH N₂ H₂))) := by
  sorry

/-- **Γ_{H₁}(N₁) ∩ Γ_Δ(N₂)**, for H₁ of type I and every Δ ≤ (ℤ/N₂)ˣ: |Nor(Γ)/Γ| =
[N(H₁) : H₁] · i_Δ · ψ(N₂)/ψ(n*) · #{Q ∥ n* : ι*_Q(Δ̄) = Δ̄, Q mod N₁ ∈ Det(H₁)}, with i_Δ = [(ℤ/N₂)ˣ : Δ]
(Part 7: `card_BG_GammaDeltaR_hStar` is the case N₁ = 1). -/
theorem card_BG_inf_GammaDelta {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    (Δ : Subgroup (ZMod N₂)ˣ) :
    (Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaDelta N₂ Δ))) : ℚ) =
      H₁.relIndex (NormH H₁) * Δ.index * (psi N₂ / psi (nStar N₂ Δ)) * wMixed H₁ N₂ Δ := by
  sorry

/-- **H₂ of prime level p fixing exactly one line, p mod N₁ ∈ Det(H₁)**: the Fricke involution W_p survives, and
|Nor(Γ)/Γ| = 2 · [N(H₁) : H₁] · [N(H₂) : H₂]. -/
theorem card_BG_inf_prime_unique {N₁ p : ℕ} [NeZero N₁] (hp : p.Prime) (hcop : N₁.Coprime p)
    {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ q : ℕ, q.Prime → q ∣ N₁ → ¬ IsBorelMod H₁ q ∨ IsSplitMod H₁ (q ^ N₁.factorization q))
    {H₂ : Subgroup SL(2, ZMod p)} (h : FixesUniqueLine H₂) (hd : IsNormDet H₁ (p : ZMod N₁)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH p H₂))) =
      2 * (H₁.relIndex (NormH H₁) * H₂.relIndex (NormH H₂)) := by
  sorry

/-- **H₂ of prime level p fixing exactly one line, p mod N₁ ∉ Det(H₁)**: W_p does not survive, and
|Nor(Γ)/Γ| = [N(H₁) : H₁] · [N(H₂) : H₂]. -/
theorem card_BG_inf_prime_unique_of_not {N₁ p : ℕ} [NeZero N₁] (hp : p.Prime) (hcop : N₁.Coprime p)
    {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ q : ℕ, q.Prime → q ∣ N₁ → ¬ IsBorelMod H₁ q ∨ IsSplitMod H₁ (q ^ N₁.factorization q))
    {H₂ : Subgroup SL(2, ZMod p)} (h : FixesUniqueLine H₂) (hd : ¬ IsNormDet H₁ (p : ZMod N₁)) :
    Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaH p H₂))) = H₁.relIndex (NormH H₁) * H₂.relIndex (NormH H₂) := by
  sorry

/-! ## §C. Corollaries -/

/-- Γ(N₁) ∩ Γ_{H₂}(N₂): |Nor(Γ)/Γ| = |SL₂(ℤ/N₁)| · |Nor(Γ_{H₂})/Γ_{H₂}|. -/
theorem card_BG_Gamma_inf {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (CongruenceSubgroup.Gamma N₁ ⊓ GammaH N₂ H₂))) =
      Nat.card SL(2, ZMod N₁) * Nat.card (BG (toR (GammaH N₂ H₂))) := by
  sorry

/-- For primes p ≥ 5 (ε a non-square mod p): Γ_ns⁺(p) ∩ Γ_{H₂}(N₂) has as many classes as Γ_{H₂}(N₂). -/
theorem card_BG_GammaNsPlus_inf {p N₂ : ℕ} [NeZero N₂] (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p}
    (hε : ¬ IsSquare ε) (hcop : p.Coprime N₂) (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (GammaNsPlus p ε ⊓ GammaH N₂ H₂))) = Nat.card (BG (toR (GammaH N₂ H₂))) := by
  sorry

/-- For primes p ≥ 7: Γ_sp⁺(p) ∩ Γ_{H₂}(N₂) has as many classes as Γ_{H₂}(N₂). -/
theorem card_BG_GammaSpPlus_inf {p N₂ : ℕ} [NeZero N₂] (hp : p.Prime) (hp7 : 7 ≤ p) (hcop : p.Coprime N₂)
    (H₂ : Subgroup SL(2, ZMod N₂)) :
    Nat.card (BG (toR (GammaSpPlus p ⊓ GammaH N₂ H₂))) = Nat.card (BG (toR (GammaH N₂ H₂))) := by
  sorry

/-! ## §S. Sanity checks -/

/-- Det(Q₈) for Q₈ ≤ SL₂(F₇) is the set of non-zero squares. -/
theorem isNormDet_Q8mod7_iff {u : ZMod 7} (hu : u ≠ 0) : IsNormDet Q8mod7 u ↔ IsSquare u := by
  sorry

/-- |Nor(Γ_{Q₈}(7))/Γ_{Q₈}(7)| = 6 (N(Q₈) = 2.S₄). -/
theorem card_BG_Q8mod7 : Nat.card (BG (toR (GammaH 7 Q8mod7))) = 6 := by
  sorry

/-- With Γ₀(2): 12 = 6 · 2, as 2 = 3² is a square mod 7 (w₂ survives). -/
theorem card_BG_Q8mod7_inf_two :
    Nat.card (BG (toR (GammaH 7 Q8mod7 ⊓ CongruenceSubgroup.Gamma0 2))) = 12 := by
  sorry

/-- With Γ₀(3): 6, not 6 · 2, as 3 is not a square mod 7 (w₃ does not survive). -/
theorem card_BG_Q8mod7_inf_three :
    Nat.card (BG (toR (GammaH 7 Q8mod7 ⊓ CongruenceSubgroup.Gamma0 3))) = 6 := by
  sorry

end

end NormalizerLean
