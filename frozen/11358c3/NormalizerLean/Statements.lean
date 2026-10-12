import Mathlib

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions and main statements

This file fixes the definitions and the statements T1–T8 of the handover note
`~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).  Every theorem is `sorry`;
proofs live in other files.  After the user's review, no definition or statement in this file
changes without the user's approval.

Blueprint references (paths relative to `~/automorphisms_X1/audit/`):
* [Nw]  `newman_normalizer.md`
* [BA]  `bars_all_levels.md`
* [BAu] `bars_audit.md`

Conventions.
* `B N` is defined honestly as a quotient of the normalizer in SL₂(ℝ); no statement uses a
  presented group as a definition of `B N`.
* An element of `B N` is tied to a real matrix by `B.IsClassOf x g`, which asserts that `g`
  normalizes Γ₀(N) and that `x` is its coset.  So no statement silently assumes membership.
* Atkin–Lehner elements are handled through the predicate `IsAtkinLehner N Q g` (all choices of
  x, y, z, w at once), not through one hard-wired choice of Bézout coefficients.
* `[x, y] = x⁻¹ y⁻¹ x y` (the blueprint's convention, `bracket` below).  Mathlib's `⁅x, y⁆` is
  `x y x⁻¹ y⁻¹`; it is not used.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Definitions -/

/-- Γ₀(N) as a subgroup of SL₂(ℝ): the image of Mathlib's `CongruenceSubgroup.Gamma0 N ≤ SL(2, ℤ)`. -/
def Gamma0R (N : ℕ) : Subgroup SL(2, ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The normalizer of Γ₀(N) in SL₂(ℝ). -/
abbrev Norm0 (N : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Gamma0R N : Set SL(2, ℝ))

/-- **B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N).** -/
abbrev B (N : ℕ) : Type :=
  Norm0 N ⧸ (Gamma0R N).subgroupOf (Norm0 N)

instance (N : ℕ) : ((Gamma0R N).subgroupOf (Norm0 N)).Normal :=
  Subgroup.normal_in_normalizer

/-- `x : B N` is the class of the real matrix `g`: `g` normalizes Γ₀(N) and `x = g Γ₀(N)`. -/
def B.IsClassOf {N : ℕ} (x : B N) (g : SL(2, ℝ)) : Prop :=
  ∃ hg : g ∈ Norm0 N, x = QuotientGroup.mk ⟨g, hg⟩

/-- The image in SL₂(ℝ) of a real 2×2 matrix `A` of positive determinant: `(det A)^{-1/2} • A`.
Junk value `1` if `det A ≤ 0`; below it is only applied to matrices of positive determinant. -/
def projSL (A : Matrix (Fin 2) (Fin 2) ℝ) : SL(2, ℝ) :=
  if hA : 0 < A.det then
    ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩
  else 1

/-- h(N) = 2^{min(3, ⌊v₂(N)/2⌋)} · 3^{min(1, ⌊v₃(N)/2⌋)}.  By `hPart_isGreatest` this is the largest
divisor of 24 whose square divides N. -/
def hPart (N : ℕ) : ℕ :=
  2 ^ min 3 (N.factorization 2 / 2) * 3 ^ min 1 (N.factorization 3 / 2)

/-- n(N) = N / h(N)². -/
def nPart (N : ℕ) : ℕ := N / hPart N ^ 2

/-- m_p = p^{v_p(N)}, the exact power of `p` dividing `N`. -/
def mPart (N p : ℕ) : ℕ := p ^ N.factorization p

/-- ψ(t) = t ∏_{p ∣ t} (1 + 1/p).  By `Gamma0_index` this is μ(t) = [SL₂(ℤ) : Γ₀(t)]. -/
def psi (t : ℕ) : ℚ := t * ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℚ))

/-- S_k = [[1, 1/k], [0, 1]]. -/
def S (k : ℕ) : SL(2, ℝ) :=
  ⟨!![1, (k : ℝ)⁻¹; 0, 1], by simp [det_fin_two]⟩

/-- `g` is an Atkin–Lehner element w_Q of level N:
`g = (1/√Q)·[[Qx, y], [Nz, Qw]]` with `x y z w : ℤ` and `Q²xw − Nyz = Q`.
No divisibility is built in: the theorems below add the hypothesis `Q ∣ N`, which then forces
Q ∥ N.  That hypothesis is essential: for N = 4, Q = 8 the element (1/√8)·[[0, 1], [−8, 0]]
satisfies the equation but does not normalize Γ₀(4).  For Q = 0 the predicate is false. -/
def IsAtkinLehner (N Q : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ x y z w : ℤ, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w]

/-- `x : B N` is the class w_Q: an Atkin–Lehner element for `Q` exists, and every one represents `x`. -/
def B.IsALClass {N : ℕ} (x : B N) (Q : ℕ) : Prop :=
  (∃ g, IsAtkinLehner N Q g) ∧ ∀ g, IsAtkinLehner N Q g → x.IsClassOf g

/-- `g` has Newman's form (8′) [Nw, Theorem]:
`g = ±(1/√e)·[[ae, b/h], [Nc/h, de]]` with `a b c d : ℤ`, `e ≥ 1`, `e ∣ n`, `ade² − bcn = e`. -/
def IsNewmanForm (N : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ nPart N ∧
    a * d * (e : ℤ) ^ 2 - b * c * (nPart N : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / hPart N; (N : ℝ) * c / hPart N, (d : ℝ) * e]

/-- D = diag(h, 1), rescaled into SL₂(ℝ): `diag(√h, 1/√h)`.  Conjugation by it equals conjugation by D. -/
def Dsl (N : ℕ) : SL(2, ℝ) := projSL !![(hPart N : ℝ), 0; 0, 1]

/-- D⁻¹ Γ₀(n) D ≤ SL₂(ℝ). -/
def conjGamma0n (N : ℕ) : Subgroup SL(2, ℝ) :=
  (Gamma0R (nPart N)).map (MulAut.conj (Dsl N)⁻¹).toMonoidHom

/-- C(N) = D⁻¹ Γ₀(n) D / Γ₀(N), as a subgroup of B(N): by definition the image in B(N) of
D⁻¹ Γ₀(n) D ∩ Norm(Γ₀(N)).  By `conjGamma0n_le_normalizer` the intersection is all of D⁻¹ Γ₀(n) D. -/
def CN (N : ℕ) : Subgroup (B N) :=
  ((conjGamma0n N).subgroupOf (Norm0 N)).map
    (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N)))

/-- The classes of w_{m_p} and S_{h(m_p)} in B(N): the set of `x` that are the class w_{m_p}
(`B.IsALClass`) or the class of S_{h(m_p)}.  That both classes exist is part of T1
(`exists_isAtkinLehner`, `isAtkinLehner_mem_normalizer`, `isAtkinLehner_mul_inv_mem`,
`S_mem_normalizer`); if one did not, this set would be smaller and T4–T7 would become harder,
not weaker. -/
def localGens (N p : ℕ) : Set (B N) :=
  {x | x.IsALClass (mPart N p) ∨ x.IsClassOf (S (hPart (mPart N p)))}

/-- The local subgroup B_p = ⟨w_{m_p}, S_{h(m_p)}⟩ ≤ B(N). -/
def Bloc (N p : ℕ) : Subgroup (B N) := Subgroup.closure (localGens N p)

/-- f₂(a) = |B(2ᵃ)|: 1, 2, 6, 8, 24, 32, 96, 128 for a = 0, …, 6, ≥ 7. -/
def f₂ : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 8 | 4 => 24 | 5 => 32 | 6 => 96 | _ => 128

/-- f₃(b) = |B(3ᵇ)|: 1, 2, 12, 18 for b = 0, 1, 2, ≥ 3. -/
def f₃ : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 12 | _ => 18

/-! ### Presentations -/

/-- The two generators of a local presentation. -/
inductive LGen
  | w
  | s
  deriving DecidableEq

/-- `[x, y] = x⁻¹ y⁻¹ x y` (blueprint convention, not Mathlib's `⁅x, y⁆`). -/
def bracket {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

namespace Words

/-- The word `w`. -/
abbrev w : FreeGroup LGen := FreeGroup.of .w
/-- The word `s`. -/
abbrev s : FreeGroup LGen := FreeGroup.of .s
/-- `r = w s⁻¹ w`, an abbreviation, not a generator [BA]. -/
abbrev r : FreeGroup LGen := w * s⁻¹ * w

end Words

open Words in
/-- The relations of [BA] beyond `w² = sʰ = 1`, for the prime power `pᵃ`:
* 4, 9, 16: (ws)³ = 1;
* 8, 2ᵃ (a ≥ 9), 3ᵇ (b ≥ 3): [r, s] = 1;
* 32, 64, 128, 256: relations (4), (5), (6), (7) of [BA];
* otherwise (h = 1): nothing.
(A `List`, so that the relators can be evaluated numerically as a sanity check.) -/
def localExtraRels : ℕ → ℕ → List (FreeGroup LGen)
  | 2, 2 | 2, 4 | 3, 2 => [(w * s) ^ 3]
  | 2, 3 => [bracket r s]
  -- (4), m = 32
  | 2, 5 => [bracket (r ^ 2) s, bracket (s ^ 2) r, bracket r s * (r ^ 2 * s ^ 2)⁻¹]
  -- (5), m = 64, with u = s⁴, v = w s⁴ w
  | 2, 6 =>
    let u := s ^ 4
    let v := w * s ^ 4 * w
    [(w * s) ^ 3, bracket u v, s * v * s⁻¹ * (u * v)⁻¹]
  -- (6), m = 128
  | 2, 7 => [bracket (r ^ 2) (s ^ 2), r⁻¹ * s ^ 2 * r * (r ^ 4 * s ^ 2)⁻¹,
      s⁻¹ * r ^ 2 * s * (r ^ 2 * s ^ 4)⁻¹, bracket r s * (r ^ 6 * s ^ 2)⁻¹]
  -- (7), m = 256
  | 2, 8 => [bracket (r ^ 2) s, r⁻¹ * s * r * (r ^ 4 * s ^ 5)⁻¹]
  | 2, a => if 9 ≤ a then [bracket r s] else []
  | 3, b => if 3 ≤ b then [bracket r s] else []
  | _, _ => []

/-- The relators of the local presentation of B(pᵃ): `w²`, `s^{h(pᵃ)}` and `localExtraRels p a`. -/
def localRelList (p a : ℕ) : List (FreeGroup LGen) :=
  [Words.w ^ 2, Words.s ^ hPart (p ^ a)] ++ localExtraRels p a

/-- The local presentation of B(pᵃ), as a set of relators. -/
def localRels (p a : ℕ) : Set (FreeGroup LGen) := {ρ | ρ ∈ localRelList p a}

/-- Generators of the global presentation: `(p, w)` and `(p, s)` for each prime `p ∣ N`. -/
abbrev GGen (N : ℕ) : Type := N.primeFactors × LGen

/-- The global presentation of B(N) [BA, (1)]: the local relations for each p ∣ N, and for p ≠ q
`[w_p, w_q] = [s_p, s_q] = 1`, `w_p s_q w_p⁻¹ = s_q^{m_p}`. -/
def globalRels (N : ℕ) : Set (FreeGroup (GGen N)) :=
  (⋃ p : N.primeFactors,
      FreeGroup.map (fun x : LGen => (p, x)) '' localRels p (N.factorization p)) ∪
    ⋃ (p : N.primeFactors) (q : N.primeFactors) (_ : p ≠ q),
      {bracket (FreeGroup.of (p, .w)) (FreeGroup.of (q, .w)),
        bracket (FreeGroup.of (p, .s)) (FreeGroup.of (q, .s)),
        FreeGroup.of (p, .w) * FreeGroup.of (q, .s) * (FreeGroup.of (p, .w))⁻¹ *
          (FreeGroup.of (q, .s) ^ mPart N p)⁻¹}

open Words in
/-- Bars's local presentation ⟨w, s | w², sʰ, (ws)ᵏ⟩ (Bars 2008, Prop. 13(2) / Thm 16). -/
def barsRels (h k : ℕ) : Set (FreeGroup LGen) := {w ^ 2, s ^ h, (w * s) ^ k}

/-- w₂₅₆ = [[0, −1/16], [16, 0]]. -/
def w256 : SL(2, ℝ) :=
  ⟨!![0, -1 / 16; 16, 0], by norm_num [det_fin_two]⟩

/-! ## T1: explicit elements of the normalizer -/

/-- h(N) is the largest divisor of 24 whose square divides N. -/
theorem hPart_isGreatest (N : ℕ) [NeZero N] :
    IsGreatest {d : ℕ | d ∣ 24 ∧ d ^ 2 ∣ N} (hPart N) := sorry

/-- **T1** for Atkin–Lehner elements: every w_Q with Q ∣ N normalizes Γ₀(N).
(`hQ` is essential; see `IsAtkinLehner`.) -/
theorem isAtkinLehner_mem_normalizer {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : g ∈ Norm0 N := sorry

/-- Atkin–Lehner elements exist for every exact divisor Q ∥ N. -/
theorem exists_isAtkinLehner {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hcop : Nat.Coprime Q (N / Q)) :
    ∃ g, IsAtkinLehner N Q g := sorry

/-- Any two Atkin–Lehner elements for Q differ by an element of Γ₀(N), so w_Q ∈ B(N) is
well defined. -/
theorem isAtkinLehner_mul_inv_mem {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g g' : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) (hg' : IsAtkinLehner N Q g') : g * g'⁻¹ ∈ Gamma0R N := sorry

/-- **T1** for translations: S_k normalizes Γ₀(N) for every k ∣ h(N); in particular S_h does. -/
theorem S_mem_normalizer {N k : ℕ} [NeZero N] (hk : k ∣ hPart N) : S k ∈ Norm0 N := sorry

/-- **T1** in general [Nw §1]: every matrix of the form (8′) normalizes Γ₀(N). -/
theorem newmanForm_mem_normalizer {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : IsNewmanForm N g) :
    g ∈ Norm0 N := sorry

/-! ## T2: Newman's theorem -/

/-- **T2** (Newman) [Nw §§2–8]: every element of the normalizer has the form (8′). -/
theorem newman {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) : IsNewmanForm N g := sorry

/-! ## T3: the order of B(N) -/

/-- The index formula μ(t) = [SL₂(ℤ) : Γ₀(t)] = t ∏_{p ∣ t} (1 + 1/p). -/
theorem Gamma0_index (t : ℕ) [NeZero t] :
    ((CongruenceSubgroup.Gamma0 t).index : ℚ) = psi t := sorry

/-- **T3**: B(N) is finite. -/
theorem finite_B (N : ℕ) [NeZero N] : Finite (B N) := sorry

/-- **T3**: |B(N)| = 2^{ω(n)} μ(N)/μ(n). -/
theorem card_B (N : ℕ) [NeZero N] :
    (Nat.card (B N) : ℚ) = 2 ^ (nPart N).primeFactors.card * psi N / psi (nPart N) := sorry

/-- **T3**, explicit form: for N = 2ᵃ 3ᵇ M with gcd(M, 6) = 1, |B(N)| = f₂(a) f₃(b) 2^{ω(M)}. -/
theorem card_B_explicit (N : ℕ) [NeZero N] :
    Nat.card (B N) =
      f₂ (N.factorization 2) * f₃ (N.factorization 3) * 2 ^ (N.primeFactors \ {2, 3}).card := sorry

/-- D⁻¹ Γ₀(n) D ⊆ Norm(Γ₀(N)), so `CN N` is literally D⁻¹ Γ₀(n) D / Γ₀(N).  (The e = 1 case of T1.) -/
theorem conjGamma0n_le_normalizer (N : ℕ) [NeZero N] : conjGamma0n N ≤ Norm0 N := sorry

/-- |C(N)| = μ(N)/μ(n). -/
theorem card_CN (N : ℕ) [NeZero N] : (Nat.card (CN N) : ℚ) = psi N / psi (nPart N) := sorry

/-- B(N)/C(N) ≅ (ℤ/2)^{ω(n)} [Nw §9], stated as: a surjection onto (ℤ/2)^{primes of n}
with kernel C(N). -/
theorem B_mod_CN (N : ℕ) [NeZero N] :
    ∃ σ : B N →* ((nPart N).primeFactors → Multiplicative (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = CN N := sorry

/-! ## T4: generation -/

/-- **T4** [BA]: B(N) is generated by the classes of w_{m_p} and S_{h(m_p)}, p ∣ N. -/
theorem closure_localGens (N : ℕ) [NeZero N] :
    Subgroup.closure (⋃ p ∈ N.primeFactors, localGens N p) = ⊤ := sorry

/-! ## T5: local presentations -/

/-- **T5** [BA, table and (4)–(7)]: for a prime power pᵃ, the local presentation is a presentation
of B(pᵃ), with w ↦ w_{pᵃ} and s ↦ S_{h(pᵃ)}. -/
theorem localPresentation (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    ∃ φ : PresentedGroup (localRels p a) ≃* B (p ^ a),
      (φ (.of .w)).IsALClass (p ^ a) ∧ (φ (.of .s)).IsClassOf (S (hPart (p ^ a))) := sorry

/-! ## T6: the prime-power embedding and the global presentation -/

/-- **T6** [BA, (12)]: for p ∣ N, B_p = ⟨w_{m_p}, S_{h(m_p)}⟩ ≤ B(N) maps isomorphically onto
B(m_p) by "forgetting the extra level": the class of g mod Γ₀(N) goes to the class of g mod Γ₀(m_p). -/
theorem localEmbedding (N p : ℕ) [NeZero N] (hp : p ∈ N.primeFactors) :
    ∃ φ : Bloc N p ≃* B (mPart N p),
      ∀ (x : Bloc N p) (g : SL(2, ℝ)), (x : B N).IsClassOf g → (φ x).IsClassOf g := sorry

/-- **T6** [BA, (1)]: the global presentation is a presentation of B(N), with w_p ↦ w_{m_p} and
s_p ↦ S_{h(m_p)}. -/
theorem globalPresentation (N : ℕ) [NeZero N] :
    ∃ φ : PresentedGroup (globalRels N) ≃* B N, ∀ p : N.primeFactors,
      (φ (.of (p, .w))).IsALClass (mPart N p) ∧
        (φ (.of (p, .s))).IsClassOf (S (hPart (mPart N p))) := sorry

/-! ## T7: the direct-product criterion -/

/-- **T7** [BA, (3)]: the local subgroups B_p form an internal direct product (the product of the
inclusions is an isomorphism ∏_p B_p ≅ B(N)) iff m_p ≡ 1 (mod h(m_q)) for all p ≠ q. -/
theorem internalDirectProduct_iff (N : ℕ) [NeZero N] :
    (∃ φ : ((p : N.primeFactors) → Bloc N p) ≃* B N,
        ∀ (p : N.primeFactors) (x : Bloc N p), φ (Pi.mulSingle p x) = x) ↔
      ∀ p ∈ N.primeFactors, ∀ q ∈ N.primeFactors, p ≠ q →
        mPart N p ≡ 1 [MOD hPart (mPart N q)] := sorry

/-- **T7**, example: B(18) ≅ S₄. -/
theorem B18_equiv_perm : Nonempty (B 18 ≃* Equiv.Perm (Fin 4)) := sorry

/-- **T7**, example: B(18) is not C₂ × A₄. -/
theorem B18_not_C2_prod_A4 :
    IsEmpty (B 18 ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 4)) := sorry

/-! ## T8: the errors in the literature -/

/-- **T8(a)**, matrix identity [BAu §4]: with w = w₂₅₆ and s = S₈,
(w s² w s)(s² w s w)⁻¹ = [[5, −9/8], [−288, 65]]. -/
theorem AS_quotient_matrix :
    ((w256 * S 8 ^ 2 * w256 * S 8 * (S 8 ^ 2 * w256 * S 8 * w256)⁻¹ : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![5, -9 / 8; -288, 65] := sorry

/-- **T8(a)**: the Akbaş–Singerman relation w s² w s = s² w s w fails in B(256). -/
theorem AS_relation_fails :
    ∃ x y : B 256, x.IsClassOf w256 ∧ y.IsClassOf (S 8) ∧
      x * y ^ 2 * x * y ≠ y ^ 2 * x * y * x := sorry

/-- **T8(a)**, matrix identity [BAu §4]: w s w s w s³ w s³ = −[[11, 4], [−256, −93]]. -/
theorem bars_word_matrix :
    ((w256 * S 8 * w256 * S 8 * w256 * S 8 ^ 3 * w256 * S 8 ^ 3 : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = -!![11, 4; -256, -93] := sorry

/-- **T8(a)**: Bars's relation w s w s w s³ w s³ = 1 holds in B(256). -/
theorem bars_relation_holds :
    ∃ x y : B 256, x.IsClassOf w256 ∧ y.IsClassOf (S 8) ∧
      x * y * x * y * x * y ^ 3 * x * y ^ 3 = 1 := sorry

/-- **T8(b)**: Bars's presentation at λ = 5, Δ(2, 4, 4), is infinite. -/
theorem bars_lambda5_infinite : Infinite (PresentedGroup (barsRels 4 4)) := sorry

/-- **T8(b)**: Bars's presentation at λ = 6, Δ(2, 8, 3), is infinite. -/
theorem bars_lambda6_infinite : Infinite (PresentedGroup (barsRels 8 3)) := sorry

/-- **T8(b)**: Bars's presentation at λ = 7, Δ(2, 8, 4), is infinite. -/
theorem bars_lambda7_infinite : Infinite (PresentedGroup (barsRels 8 4)) := sorry

open Words in
/-- **T8(c)**: adding (w s⁻¹ w s)² = 1 at λ = 5 gives order 32. -/
theorem completed_lambda5_card :
    Nat.card (PresentedGroup (barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2})) = 32 := sorry

open Words in
/-- **T8(c)**, stronger: the completed λ = 5 presentation presents B(32), w ↦ w₃₂, s ↦ S₄. -/
theorem completed_lambda5 :
    ∃ φ : PresentedGroup (barsRels 4 4 ∪ {(w * s⁻¹ * w * s) ^ 2}) ≃* B 32,
      (φ (.of .w)).IsALClass 32 ∧ (φ (.of .s)).IsClassOf (S 4) := sorry

open Words in
/-- **T8(c)**: adding (w s⁻¹ w s)³ = 1 at λ = 6 gives order 96. -/
theorem completed_lambda6_card :
    Nat.card (PresentedGroup (barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3})) = 96 := sorry

open Words in
/-- **T8(c)**, stronger: the completed λ = 6 presentation presents B(64), w ↦ w₆₄, s ↦ S₈. -/
theorem completed_lambda6 :
    ∃ φ : PresentedGroup (barsRels 8 3 ∪ {(w * s⁻¹ * w * s) ^ 3}) ≃* B 64,
      (φ (.of .w)).IsALClass 64 ∧ (φ (.of .s)).IsClassOf (S 8) := sorry

open Words in
/-- **T8(d)**: Bars's λ = 8 presentation ⟨w, s | w², s⁸, w s w s w s³ w s³⟩ has order 128. -/
theorem bars_lambda8_card :
    Nat.card (PresentedGroup ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
      Set (FreeGroup LGen))) = 128 := sorry

open Words in
/-- **T8(d)**, stronger: Bars's λ = 8 presentation presents B(256), w ↦ w₂₅₆, s ↦ S₈. -/
theorem bars_lambda8 :
    ∃ φ : PresentedGroup ({w ^ 2, s ^ 8, w * s * w * s * w * s ^ 3 * w * s ^ 3} :
        Set (FreeGroup LGen)) ≃* B 256,
      (φ (.of .w)).IsALClass 256 ∧ (φ (.of .s)).IsClassOf (S 8) := sorry

/-! ## Stage-1 milestones (relations hold; consequences of T5/T6, proved first) -/

/-- The local relators hold in B(pᵃ): they evaluate into Γ₀(pᵃ) under w ↦ any Atkin–Lehner
element w_{pᵃ} and s ↦ S_{h(pᵃ)}.  This covers the relations of the table of [BA] and (4)–(7),
including the [r, s] = 1 cases of (14) (not the formula (14) itself). -/
theorem localRels_mem_Gamma0 (p a : ℕ) (hp : p.Prime) (ha : 0 < a) {wg : SL(2, ℝ)}
    (hw : IsAtkinLehner (p ^ a) (p ^ a) wg) :
    ∀ ρ ∈ localRels p a,
      FreeGroup.lift (fun x : LGen => match x with | .w => wg | .s => S (hPart (p ^ a))) ρ ∈
        Gamma0R (p ^ a) := sorry

/-- The global relators hold in B(N), for any choice of Atkin–Lehner elements w_{m_p}.
This covers (1) and (15) of [BA]. -/
theorem globalRels_mem_Gamma0 (N : ℕ) [NeZero N] (wg : N.primeFactors → SL(2, ℝ))
    (hw : ∀ p : N.primeFactors, IsAtkinLehner N (mPart N p) (wg p)) :
    ∀ ρ ∈ globalRels N,
      FreeGroup.lift (fun x : GGen N => match x.2 with
        | .w => wg x.1
        | .s => S (hPart (mPart N x.1))) ρ ∈ Gamma0R N := sorry

end

end NormalizerLean
