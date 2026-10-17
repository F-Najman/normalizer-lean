module

public import NormalizerDelta.DefsGeneral
public import NormalizerDelta.ProofsGeneral

@[expose] public section

/-!
# General modular curves (2026-10-10): statements (Stage 0, all `sorry`)

The user asked for this project (2026-10-10: "Yes, go ahead.").  Definitions: `DefsGeneral.lean`.  For N ≥ 1 and
H ≤ SL₂(ℤ/N), the statements are about Nor_{SL₂(ℝ)}(Γ_H)/Γ_H (`BG (toR (GammaH N H))`), for every H.  For −1 ∈ H
this is the modular automorphism group MAut(X_H) (DLM26, (4.1) and Prop. 4.3(1); `BQ_equiv_BG`).  For −1 ∉ H the
curve only depends on ±Γ_H (X_H = X_{±H}), so MAut(X_H) = `BG (toR (GammaH N (H ⊔ pmOneSL N)))`: apply the statements
to ±H = H ⊔ {±1}, which satisfies the hypotheses of §G and §P iff H does (−1 acts on (ℤ/q)² as a scalar, so H and ±H
fix the same lines).  The two quotients differ in general: for H = U at p = 5 (Γ_H = Γ₁(5)), |Nor(Γ_H)/Γ_H| = 8, while
X₁(5) has 4 modular automorphisms.  (As for Γ(N) and Γ₁(N) in `NormalizerDelta/Defs.lean`.)
Only modular automorphisms are counted: whether all automorphisms are modular (Dose–Lido–Mercuri,
"Automorphisms of general modular curves", arXiv:2610.08998v1 ("DLM26"), Thm. 3.12, Thm. 3.13 for prime level
p > 311) needs Jacobians, Hecke correspondences and gonality, and is not formalized.

* §H: every Γ ⊇ Γ(N) is a Γ_H; [SL₂(ℤ) : Γ_H] = [SL₂(ℤ/N) : H].
* §R, the elements of SL₂(ℤ) (DLM26, Algorithm 4.9, Step 3, and its correctness proof): γ ∈ SL₂(ℤ) normalizes Γ_H
  iff γ mod N normalizes H; they give a subgroup of Nor(Γ_H)/Γ_H of order [N(H) : H].
* §F, finiteness: the class of a normalizing m only depends on m mod N·det m (DLM26, Prop. 4.3(4)); normalizing can
  be tested on representatives of Γ_H mod Γ(N²) (Prop. 4.3(3)); Nor(Γ)/Γ is finite for every Γ ⊇ Γ(N), of order at
  most [SL₂(ℤ) : Γ]·Σ_{D ∣ N} ψ(D) (`psi`).  (The bound is not stated in DLM26; it follows from Prop. 4.3(2), (4) and
  the count ψ(D) of primitive integral matrices of determinant D up to right multiplication by SL₂(ℤ).)
* §B, local restrictions on det m (DLM26, Prop. 4.5(1), (2), (4)); Prop. 4.3(2) is `normG_level_form` and the
  case k = 1 of Prop. 4.5(1) is `normG_level_le_SL2ZR` (`StatementsCartan.lean`).
* §G, the general theorem: if for every p ∣ N, H mod p fixes no line, or H mod p^{v_p(N)} lies in a split Cartan,
  then Nor(Γ_H) = Γ_{N(H)} and Nor(Γ_H)/Γ_H ≅ N(H)/H.  (Not stated in DLM26; it follows from Prop. 4.3(2),
  Prop. 4.5(1) (k = 1), (4) (k = v_p(N)) and Algorithm 4.9, Step 3: under the hypothesis, Step 1 of the algorithm
  only allows determinant 1.  DLM22 (arXiv:2005.09009v2), Prop. 5.6, proves the case of Cartan groups and their
  normalizers by the same argument.)
* §P, every group of prime level p: |Nor(Γ_H)/Γ_H| = [N(H) : H], times 2 if H fixes exactly one line of F_p² (then
  Γ₁(p) ≤ Γ_H ≤ Γ₀(p) up to conjugation, and the extra elements come from the Fricke involution W_p).
  (Not stated in DLM26 or DLM22; it follows from §G, Prop. 4.3(2), Prop. 4.5(2), the argument in the proof of
  Prop. 4.5(3) that H contains the unipotent group U when it fixes exactly one line, and W_p normalizing Γ_H.)
* §Q (DLM26, (4.1) and Prop. 4.3(1)): for −1 ∈ Γ, the normalizer in GL₂⁺(ℚ) modulo Γ·ℚ^× (DLM26's MAut =
  𝒩/ℙΓ_H) is the same group.
* §S: sanity checks against DLM26, Table 3.
The checks `scripts/check_general_statements.py` compute Nor(Γ_H)/Γ_H by brute force (DLM26, Prop. 4.3) for all
H up to conjugacy at levels N ≤ 11 and compare with §B, §G, §P and §F.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## §H. The groups Γ_H -/

/-- Every congruence subgroup Γ ⊇ Γ(N) is Γ_H for H = Γ mod N. -/
theorem GammaH_map {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    GammaH N (Γ.map (redSL N)) = Γ := by apply GammaH_map' <;> assumption

/-- Sanity: [SL₂(ℤ) : Γ_H] = [SL₂(ℤ/N) : H]. -/
theorem index_GammaH (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) : (GammaH N H).index = H.index := by apply index_GammaH' <;> assumption

/-! ## §R. The elements of SL₂(ℤ) in the normalizer -/

/-- DLM26, Algorithm 4.9, Step 3 (see its correctness proof): γ ∈ SL₂(ℤ) normalizes Γ_H iff γ mod N normalizes H. -/
theorem ofZ_mem_normG_GammaH_iff (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) (γ : SL(2, ℤ)) :
    ofZ γ ∈ NormG (toR (GammaH N H)) ↔ redSL N γ ∈ NormH H := by apply ofZ_mem_normG_GammaH_iff' <;> assumption

/-- Nor(Γ_H) ∩ SL₂(ℤ) = Γ_{N(H)}. -/
theorem normG_GammaH_inf_SL2ZR (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    NormG (toR (GammaH N H)) ⊓ SL2ZR = toR (GammaH N (NormH H)) := by apply normG_GammaH_inf_SL2ZR' <;> assumption

/-- The elements of SL₂(ℤ) in Nor(Γ_H) give a subgroup of Nor(Γ_H)/Γ_H of order [N(H) : H]:
[Nor(Γ_H) ∩ SL₂(ℤ) : Γ_H] = [N(H) : H]. -/
theorem relIndex_normG_inf_SL2ZR (N : ℕ) [NeZero N] (H : Subgroup SL(2, ZMod N)) :
    (toR (GammaH N H)).relIndex (NormG (toR (GammaH N H)) ⊓ SL2ZR) = H.relIndex (NormH H) := by apply relIndex_normG_inf_SL2ZR' <;> assumption

/-! ## §F. Finiteness -/

/-- DLM26, Prop. 4.3(4): if m, m' are integral of the same determinant D > 0 and m ≡ m' mod N·D, then
(D^{-1/2}m)⁻¹(D^{-1/2}m') ∈ Γ(N); so m and m' give the same coset of every Γ ⊇ Γ(N), and one normalizes Γ iff the
other does. -/
theorem projSL_inv_mul_mem_GammaR {N : ℕ} {m m' : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hdet' : m'.det = m.det) (hcong : ∀ i j, (N : ℤ) * m.det ∣ m i j - m' i j) :
    (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * projSL (m'.map (Int.cast : ℤ → ℝ)) ∈ GammaR N := by apply projSL_inv_mul_mem_GammaR' <;> assumption

/-- DLM26, Prop. 4.3(3): let Γ(N) ≤ Γ and let S ⊆ Γ be a finite set containing a representative of every class of
Γ modulo N² (every γ ∈ Γ is ≡ some s ∈ S mod N²).  An integral m with 0 < det m ∣ N normalizes Γ iff
m s m⁻¹ ∈ Γ and m⁻¹ s m ∈ Γ for every s ∈ S. -/
theorem mem_normG_iff_of_reps {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (S : Finset SL(2, ℤ)) (hSΓ : ∀ s ∈ S, s ∈ Γ)
    (hS : ∀ γ ∈ Γ, ∃ s ∈ S, redSL (N ^ 2) γ = redSL (N ^ 2) s)
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hdvd : m.det ∣ N) :
    projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ) ↔
      ∀ s ∈ S, projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ s * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈ toR Γ ∧
        (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * ofZ s * projSL (m.map (Int.cast : ℤ → ℝ)) ∈ toR Γ := by apply mem_normG_iff_of_reps' <;> assumption

/-- Nor(Γ)/Γ is finite for every Γ ⊇ Γ(N).  (Applied to ±Γ ⊇ Γ(N): every modular curve has finitely many modular
automorphisms.) -/
theorem finite_BG {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    Finite (BG (toR Γ)) := by apply finite_BG' <;> assumption

/-- An explicit bound (not stated in DLM26): |Nor(Γ)/Γ| ≤ [SL₂(ℤ) : Γ]·Σ_{D ∣ N} ψ(D) for every Γ ⊇ Γ(N)
(ψ(D) = D∏_{p ∣ D}(1 + 1/p) is the number of primitive integral matrices of determinant D up to right multiplication
by SL₂(ℤ)). -/
theorem card_BG_le {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    (Nat.card (BG (toR Γ)) : ℚ) ≤ Γ.index * ∑ D ∈ N.divisors, psi D := by apply card_BG_le' <;> assumption

/-! ## §B. Local restrictions on the determinant

In this section m is an integral matrix with det m > 0, not divisible by p (some entry is prime to p), and
D^{-1/2}m normalizes Γ_H, D = det m.  (Every element of Nor(Γ_H) has this form, with m primitive and D ∣ N:
`normG_level_form`.) -/

/-- DLM26, Prop. 4.5(1): if p^k ∣ det m, then H mod p^k lies in a Borel subgroup.  (Then p^k ∣ N.) -/
theorem isBorelMod_of_dvd_det {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p k : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j) (hk : (p : ℤ) ^ k ∣ m.det) :
    IsBorelMod H (p ^ k) := by apply isBorelMod_of_dvd_det' <;> assumption

/-- DLM26, Prop. 4.5(2): if H mod p lies in the standard Borel subgroup (it fixes the line through (1, 0)) but not
in a split Cartan subgroup, and p ∣ det m, then m ≡ [[0, *], [0, 0]] mod p. -/
theorem borel_shape {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j)
    (hB : FixesLine H p ![1, 0]) (hns : ¬ IsSplitMod H p) (hpd : (p : ℤ) ∣ m.det) :
    (p : ℤ) ∣ m 0 0 ∧ (p : ℤ) ∣ m 1 0 ∧ (p : ℤ) ∣ m 1 1 := by apply borel_shape' <;> assumption

/-- DLM26, Prop. 4.5(4): if p^k ∣ N and H mod p^k lies in a split Cartan subgroup, then
v_p(det m) ≤ v_p(N) − k. -/
theorem le_of_isSplitMod {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)} {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : 0 < m.det) (hg : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N H)))
    {p k : ℕ} (hp : p.Prime) (hprim : ∃ i j, ¬ (p : ℤ) ∣ m i j) (hk : p ^ k ∣ N)
    (hsplit : IsSplitMod H (p ^ k)) {e : ℕ} (he : (p : ℤ) ^ e ∣ m.det) :
    e + k ≤ N.factorization p := by apply le_of_isSplitMod' <;> assumption

/-! ## §G. The general theorem -/

/-- If for every prime p ∣ N, H mod p fixes no line of F_p² or H mod p^{v_p(N)} lies in a split Cartan subgroup,
then Nor(Γ_H) = Γ_{N(H)}.  (The condition is sufficient, not necessary: some groups of level 4, 8, 9 have
Nor(Γ_H) = Γ_{N(H)} without it.) -/
theorem normG_GammaH {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    NormG (toR (GammaH N H)) = toR (GammaH N (NormH H)) := by apply normG_GammaH' <;> assumption

/-- **Nor(Γ_H)/Γ_H ≅ N(H)/H** (for −1 ∈ H: the modular automorphism group of X_H is N(H)/H), under the hypothesis
of `normG_GammaH`: the class of γ ∈ SL₂(ℤ) goes to the class of γ mod N.  (φ is pinned down: by `normG_GammaH`
every class has such a γ.) -/
theorem BG_GammaH_equiv {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    ∃ φ : BG (toR (GammaH N H)) ≃* QH H,
      ∀ (γ : SL(2, ℤ)) (hγ : redSL N γ ∈ NormH H) (x : BG (toR (GammaH N H))),
        x.IsClassOf (ofZ γ) → φ x = QuotientGroup.mk ⟨redSL N γ, hγ⟩ := by apply BG_GammaH_equiv' <;> assumption

/-- Under the hypothesis of `normG_GammaH`, |Nor(Γ_H)/Γ_H| = [N(H) : H] (for −1 ∈ H: X_H has [N(H) : H] modular
automorphisms). -/
theorem card_BG_GammaH {N : ℕ} [NeZero N] {H : Subgroup SL(2, ZMod N)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N → ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)) :
    Nat.card (BG (toR (GammaH N H))) = H.relIndex (NormH H) := by apply card_BG_GammaH' <;> assumption

/-! ## §P. Prime level -/

/-- For H ≤ SL₂(F_p) in the standard Borel subgroup, (1, 0) spans the only line fixed by H iff Γ₁(p) ≤ Γ_H (then
Γ₁(p) ≤ Γ_H ≤ Γ₀(p): X_H lies between X₁(p) and X₀(p)). -/
theorem fixesUniqueLine_iff {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0]) :
    (∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) ↔ CongruenceSubgroup.Gamma1 p ≤ GammaH p H := by apply fixesUniqueLine_iff' <;> assumption

/-- **Prime level, first case**: if H ≤ SL₂(F_p) fixes no line or at least two lines of F_p², then
|Nor(Γ_H)/Γ_H| = [N(H) : H] (for −1 ∈ H: the number of modular automorphisms of X_H). -/
theorem card_BG_GammaH_prime {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (h : ¬ FixesUniqueLine H) :
    Nat.card (BG (toR (GammaH p H))) = H.relIndex (NormH H) := by apply card_BG_GammaH_prime' <;> assumption

/-- **Prime level, second case**: if H ≤ SL₂(F_p) fixes exactly one line of F_p², then
|Nor(Γ_H)/Γ_H| = 2·[N(H) : H] (for −1 ∈ H: the number of modular automorphisms of X_H). -/
theorem card_BG_GammaH_prime_unique {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)}
    (h : FixesUniqueLine H) :
    Nat.card (BG (toR (GammaH p H))) = 2 * H.relIndex (NormH H) := by apply card_BG_GammaH_prime_unique' <;> assumption

/-- In the second case, with the fixed line moved to the line through (1, 0): Nor(Γ_H) is generated by Γ_{N(H)}
and the Fricke involution W_p. -/
theorem normG_GammaH_prime_unique {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)}
    (hB : FixesLine H p ![1, 0]) (huniq : ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) :
    NormG (toR (GammaH p H)) = toR (GammaH p (NormH H)) ⊔ Subgroup.zpowers (frickeP p) := by apply normG_GammaH_prime_unique' <;> assumption

/-! ## §Q. In GL₂⁺(ℚ) -/

/-- DLM26, (4.1) and Prop. 4.3(1), for every Γ ⊇ Γ(N) with −1 ∈ Γ: g ↦ (det g)^{-1/2} g maps Nor_{GL₂⁺(ℚ)}(Γ) onto
Nor_{SL₂(ℝ)}(Γ)/Γ, with kernel Γ·ℚ^×; the clause `IsClassOf` pins φ down.  (As `BQ_GammaQ_equiv_BG` for Γ(N)
and `B0_equiv` for Γ₀(N).) -/
theorem BQ_equiv_BG {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    ∃ φ : NormGQ (Γ.map toGLPosQ) →* BG (toR Γ), Function.Surjective φ ∧
      φ.ker = (Γ.map toGLPosQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (Γ.map toGLPosQ)) ∧
      ∀ g : NormGQ (Γ.map toGLPosQ), (φ g).IsClassOf (normSL g) := by apply BQ_equiv_BG' <;> assumption

/-! ## §S. Sanity checks -/

/-- DLM26, Table 3 lists groups of modular automorphisms of orders 25308 (PSL₂(F₃₇)), 20520 (PSL₂(F₁₉) × S₃) and
26208 (SL₂(F₃).PSL₂(F₁₃)); the table gives no levels.  These are |SL₂(ℤ/N)|/2 for N = 37, 38, 39, the orders for
H = {±1} (X_H ≅ X(N) over ℂ).  (That the curves of the table are these is not checked here.) -/
theorem card_BG_GammaH_pmOne :
    Nat.card (BG (toR (GammaH 37 (pmOneSL 37)))) = 25308 ∧
      Nat.card (BG (toR (GammaH 38 (pmOneSL 38)))) = 20520 ∧
      Nat.card (BG (toR (GammaH 39 (pmOneSL 39)))) = 26208 := by apply card_BG_GammaH_pmOne' <;> assumption

end

end NormalizerLean
