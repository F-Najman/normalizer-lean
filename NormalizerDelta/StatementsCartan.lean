import NormalizerDelta.DefsCartan
import NormalizerDelta.ProofsCartan

/-!
# Cartan modular curves (2026-10-10): statements (Stage 0, all `sorry`)

The user asked for this project (2026-10-10: "Go ahead and write the statements for that").  Definitions:
`DefsCartan.lean` (Γ_sp(N), Γ_sp⁺(N), Γ_ns(N, ε), Γ_ns⁺(N, ε)).  The modular automorphism group of X_H is
Nor_{SL₂(ℝ)}(Γ_H)/Γ_H (`BG (toR Γ_H)`; all groups here contain −1).

* §L, any level N (Dose–Lido–Mercuri, "Automorphisms of general modular curves", arXiv:2610.08998 ("DLM26"),
  Prop. 4.3(1), (2) and Prop. 4.5(1), there in PGL₂⁺(ℚ) and for H ∋ −1; the rationality of the normalizer is
  [DLM22, Remark 5.2]): for Γ(N) ≤ Γ ≤ SL₂(ℤ) (−1 ∈ Γ is not assumed), every element of Nor_{SL₂(ℝ)}(Γ) is
  (det m)^{-1/2}·m for a primitive integral matrix m with det m ∣ N; if moreover Γ mod p fixes no line in F_p² for
  every prime p ∣ N, then Nor(Γ) ≤ SL₂(ℤ).
* §S, split Cartan: [SL₂(ℤ) : Γ_sp(N)] = N²∏(1 + 1/p); conjugation by diag(N, 1) maps Γ_sp(N) onto Γ₀(N²), so
  X_sp(N) ≅ X₀(N²) and its modular automorphism group has the order of B(N²); for primes p ≥ 5,
  Nor(Γ_sp(p)) = Γ_sp⁺(p) (2 modular automorphisms), and for p ≥ 7, Nor(Γ_sp⁺(p)) = Γ_sp⁺(p) (X_sp⁺(p) has no
  non-trivial modular automorphisms), which fails for p = 2, 3, 5 (`GammaSpPlus_five_lt` records p = 5).
* §N, non-split Cartan (p an odd prime, ε not a square mod p): [SL₂(ℤ) : Γ_ns(p)] = p(p − 1);
  Nor(Γ_ns(p)) = Γ_ns⁺(p) (2 modular automorphisms); for p ≥ 5, Nor(Γ_ns⁺(p)) = Γ_ns⁺(p) (X_ns⁺(p) has no
  non-trivial modular automorphisms), which fails for p = 3.
Only modular automorphisms are counted.  The non-split curves, and X_sp⁺, are treated at prime level only.
References (Dose–Lido–Mercuri, "Automorphisms of Cartan modular curves of prime and composite level",
arXiv:2005.09009v2 ("DLM22"); arXiv numbering): the indices, Table 3.1; X_sp(N) ≅ X₀(N²), Prop. 3.6; the
normalizers and the exceptions p = 5 (C_sp⁺) and p = 3 (C_ns⁺), Prop. 5.6, Lemma 5.10 and Table 5.1.
For the non-split statements, p ≠ 2 is implied by `¬ IsSquare ε` and is kept for readability.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## §L. Normalizers of groups of level N -/

/-- DLM26, Prop. 4.3(2) (with the rationality of the normalizer): if Γ(N) ≤ Γ ≤ SL₂(ℤ), every element of the
normalizer of Γ in SL₂(ℝ) is (det m)^{-1/2}·m (`projSL`) for an integral matrix m with no prime dividing all its
entries and 0 < det m ∣ N.  (The sign is absorbed in m: projSL(−m) = −projSL(m).) -/
theorem normG_level_form {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) {g : SL(2, ℝ)} (hg : g ∈ NormG (toR Γ)) :
    ∃ m : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det ∧ m.det ∣ N ∧
      (∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ m i j) ∧
      g = projSL (m.map (Int.cast : ℤ → ℝ)) := by apply normG_level_form' <;> assumption

/-- DLM26, Prop. 4.5(1) at k = 1, combined with `normG_level_form`: if Γ(N) ≤ Γ ≤ SL₂(ℤ) and, for every prime p ∣ N,
the reduction of Γ mod p fixes no line of F_p² (for every v ≠ 0 some γ ∈ Γ has γ v ∉ F_p v), then the normalizer
of Γ in SL₂(ℝ) is contained in SL₂(ℤ). -/
theorem normG_level_le_SL2ZR {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (hirr : ∀ p : ℕ, p.Prime → p ∣ N → ∀ v : Fin 2 → ZMod p, v ≠ 0 →
      ∃ γ ∈ Γ, ∀ c : ZMod p, (redSL p γ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v ≠ c • v) :
    NormG (toR Γ) ≤ SL2ZR := by apply normG_level_le_SL2ZR' <;> assumption

/-! ## §S. Split Cartan -/

/-- Sanity: [SL₂(ℤ) : Γ_sp(N)] = N² ∏_{p ∣ N} (1 + 1/p) (= [SL₂(ℤ) : Γ₀(N²)]). -/
theorem index_GammaSp (N : ℕ) [NeZero N] :
    ((GammaSp N).index : ℚ) = N ^ 2 * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by apply index_GammaSp' <;> assumption

/-- X_sp(N) ≅ X₀(N²): conjugation by D⁻¹, D = diag(N, 1) (rescaled into SL₂(ℝ)), maps Γ_sp(N) onto Γ₀(N²):
[[a, b], [c, d]] ↦ [[a, b/N], [Nc, d]]. -/
theorem conj_GammaSp (N : ℕ) (hN : 0 < N) :
    (toR (GammaSp N)).map (MulAut.conj (projSL !![(N : ℝ), 0; 0, 1])⁻¹).toMonoidHom =
      Gamma0R (N ^ 2) := by apply conj_GammaSp' <;> assumption

/-- The modular automorphism group of X_sp(N) has the order of B(N²) = Nor(Γ₀(N²))/Γ₀(N²) (given explicitly by the
proved `card_B_explicit`). -/
theorem card_BG_GammaSp (N : ℕ) [NeZero N] :
    Nat.card (BG (toR (GammaSp N))) = Nat.card (B (N ^ 2)) := by apply card_BG_GammaSp' <;> assumption

/-- Sanity: X_sp(2) and X_sp(3) have 6 and 12 modular automorphisms (|B(4)| = 6, |B(9)| = 12). -/
theorem card_BG_GammaSp_two_three :
    Nat.card (BG (toR (GammaSp 2))) = 6 ∧ Nat.card (BG (toR (GammaSp 3))) = 12 := by apply card_BG_GammaSp_two_three' <;> assumption

/-- For primes p ≥ 5, Nor(Γ_sp(p)) = Γ_sp⁺(p). -/
theorem normG_GammaSp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormG (toR (GammaSp p)) = toR (GammaSpPlus p) := by apply normG_GammaSp' <;> assumption

/-- For primes p ≥ 5, X_sp(p) has exactly 2 modular automorphisms. -/
theorem card_BG_GammaSp_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.card (BG (toR (GammaSp p))) = 2 := by apply card_BG_GammaSp_prime' <;> assumption

/-- For primes p ≥ 7, Γ_sp⁺(p) is its own normalizer in SL₂(ℝ). -/
theorem normG_GammaSpPlus {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    NormG (toR (GammaSpPlus p)) = toR (GammaSpPlus p) := by apply normG_GammaSpPlus' <;> assumption

/-- For primes p ≥ 7, X_sp⁺(p) has no non-trivial modular automorphisms. -/
theorem card_BG_GammaSpPlus {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    Nat.card (BG (toR (GammaSpPlus p))) = 1 := by apply card_BG_GammaSpPlus' <;> assumption

/-- `7 ≤ p` is needed: Γ_sp⁺(5) is not its own normalizer (e.g. any γ ∈ SL₂(ℤ) with γ ≡ [[1, 1], [2, 3]] mod 5
normalizes it; [DLM22, Table 5.1]: the quotient is ℤ/3). -/
theorem GammaSpPlus_five_lt : toR (GammaSpPlus 5) < NormG (toR (GammaSpPlus 5)) := by apply GammaSpPlus_five_lt' <;> assumption

/-! ## §N. Non-split Cartan -/

/-- Sanity: for an odd prime p and ε not a square mod p, [SL₂(ℤ) : Γ_ns(p)] = p(p − 1). -/
theorem index_GammaNs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    (GammaNs p ε).index = p * (p - 1) := by apply index_GammaNs' <;> assumption

/-- For an odd prime p and ε not a square mod p, Nor(Γ_ns(p)) = Γ_ns⁺(p). -/
theorem normG_GammaNs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    NormG (toR (GammaNs p ε)) = toR (GammaNsPlus p ε) := by apply normG_GammaNs' <;> assumption

/-- For an odd prime p and ε not a square mod p, X_ns(p) has exactly 2 modular automorphisms. -/
theorem card_BG_GammaNs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Nat.card (BG (toR (GammaNs p ε))) = 2 := by apply card_BG_GammaNs' <;> assumption

/-- For primes p ≥ 5, Γ_ns⁺(p) is its own normalizer in SL₂(ℝ). -/
theorem normG_GammaNsPlus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    NormG (toR (GammaNsPlus p ε)) = toR (GammaNsPlus p ε) := by apply normG_GammaNsPlus' <;> assumption

/-- For primes p ≥ 5, X_ns⁺(p) has no non-trivial modular automorphisms. -/
theorem card_BG_GammaNsPlus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {ε : ZMod p} (hε : ¬ IsSquare ε) :
    Nat.card (BG (toR (GammaNsPlus p ε))) = 1 := by apply card_BG_GammaNsPlus' <;> assumption

/-- `5 ≤ p` is needed: Γ_ns⁺(3) is not its own normalizer (e.g. any γ ∈ SL₂(ℤ) with γ ≡ [[0, 1], [2, 1]] mod 3
normalizes it, for ε = 2, the only non-square mod 3; [DLM22, Table 5.1]: the quotient is ℤ/3). -/
theorem GammaNsPlus_three_lt {ε : ZMod 3} (hε : ¬ IsSquare ε) :
    toR (GammaNsPlus 3 ε) < NormG (toR (GammaNsPlus 3 ε)) := by apply GammaNsPlus_three_lt' <;> assumption

end

end NormalizerLean
