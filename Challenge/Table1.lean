module

public import Mathlib

@[expose] public section

/-!
# Modular automorphism counts for Table 1

The challenge states the 42 modular automorphism counts from Table 1 of
*Automorphisms of the modular curves X_Δ(N)*, with the corresponding diamond
indices. The normalizer
definitions are copied from Parts 1 and 2 of `NormalizerLean/Defs.lean`.
The row definitions and the statement are copied from
`NormalizerDelta/Table1.lean`.
-/

/-! # From `NormalizerLean/Defs.lean`, Part 1 (verbatim) -/

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions

The definitions of the handover note `~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).
They were moved verbatim from `Statements.lean` (frozen at commit 11358c3), so that the proof files can
import them and `Statements.lean` can import the proofs.  No definition changes without the user's
approval.  The conventions are explained in `Statements.lean`.

This file holds the definitions of all six parts: those of Parts 2–6 follow, moved verbatim from
`NormalizerDelta/Defs.lean`, `DefsExtra.lean`, `DefsXN.lean`, `DefsCartan.lean` and `DefsGeneral.lean`, which
now only import this file.  They are in one file because the Comparator challenges (`Challenge/*.lean`) copy
them: Lean shares the auxiliary `_proof_n` lemmas of a file between its declarations, so a copy compiles to the
same constants as the library only if it keeps the library's order; each challenge copies whole parts of this
file, in order.
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


end

end NormalizerLean

/-! # From `NormalizerLean/Defs.lean`, Part 2 (verbatim) -/

-- Part 2, moved verbatim from `NormalizerDelta/Defs.lean`.

/-!
# Normalizers of Γ_Δ(N), Γ(N) and ±Γ₁(N): definitions

Definitions for the second project in `~/normalizer_lean` (plan:
`~/automorphisms_X1/notes/2026-10-08-lean-delta-plan.md`).  The B(N) definitions of
`NormalizerLean/Defs.lean` (`Gamma0R`, `IsAtkinLehner`, `projSL`, `hPart`, …) are reused unchanged.

Conventions (as for B(N)).
* Every quotient is the honest one: Nor_{SL₂(ℝ)}(Γ) / Γ for a subgroup Γ ≤ SL₂(ℝ) (`BG`).
* Modular automorphism groups are quotients in PSL₂(ℝ).  For a group Γ ∋ −1 the
  SL₂(ℝ)-quotient is the same group; for Γ(N) and Γ₁(N), which do not contain −1 when N ≥ 3, the
  modular automorphism group of the curve is the quotient for ±Γ (`pmGammaR`, `pmGamma1R`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Normalizer quotients -/

/-- The image in SL₂(ℝ) of a subgroup of SL₂(ℤ). -/
def toR (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℝ) :=
  Γ.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The normalizer of Γ in SL₂(ℝ). -/
abbrev NormG (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Γ : Set SL(2, ℝ))

/-- **Nor_{SL₂(ℝ)}(Γ) / Γ.** -/
abbrev BG (Γ : Subgroup SL(2, ℝ)) : Type :=
  NormG Γ ⧸ Γ.subgroupOf (NormG Γ)

instance (Γ : Subgroup SL(2, ℝ)) : (Γ.subgroupOf (NormG Γ)).Normal :=
  Subgroup.normal_in_normalizer

/-- `x : BG Γ` is the class of the real matrix `g`: `g` normalizes Γ and `x = g Γ`. -/
def BG.IsClassOf {Γ : Subgroup SL(2, ℝ)} (x : BG Γ) (g : SL(2, ℝ)) : Prop :=
  ∃ hg : g ∈ NormG Γ, x = QuotientGroup.mk ⟨g, hg⟩

/-! ## Γ_Δ(N) -/

/-- Γ_Δ(N) = {γ ∈ Γ₀(N) : γ₁₁ mod N ∈ Δ} ≤ SL₂(ℤ), for a subgroup Δ ≤ (ℤ/N)ˣ.
(`γ 1 1` is the lower right entry.  For γ ∈ Γ₀(N) it is a unit mod N, since det γ = 1.) -/
def GammaDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧
    ∃ u ∈ Δ, (u : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro γ γ' ⟨h0, u, hu, hγ⟩ ⟨h0', u', hu', hγ'⟩
    refine ⟨Subgroup.mul_mem _ h0 h0', u * u', Subgroup.mul_mem _ hu hu', ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have e : ((γ * γ') 1 1 : ℤ) = γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Units.val_mul, hγ, hγ', e]
    push_cast
    rw [hc, zero_mul, zero_add]
  inv_mem' := by
    rintro γ ⟨h0, u, hu, hγ⟩
    refine ⟨Subgroup.inv_mem _ h0, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have h := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h
      rw [hc, mul_zero, sub_zero] at h
      exact h
    have e : (γ⁻¹ 1 1 : ℤ) = γ 0 0 := by
      simp [Matrix.adjugate_fin_two]
    rw [e]
    rw [← hγ] at hdet
    exact Units.inv_eq_of_mul_eq_one_left hdet

/-- Γ_Δ(N) in SL₂(ℝ). -/
def GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) := toR (GammaDelta N Δ)

/-- ε_Δ = gcd(N, d² − 1 : d ∈ Δ), with d running over the representatives
`(d : ZMod N).val ∈ [0, N)`.  The truncated subtraction is harmless: for N ≥ 2 a unit has
`val ≥ 1`, and for N = 1 the result is gcd(1, ·) = 1 anyway. -/
def epsDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  haveI := Classical.decPred (· ∈ Δ)
  Nat.gcd N ((Finset.univ.filter (· ∈ Δ)).gcd fun d : (ZMod N)ˣ => (d : ZMod N).val ^ 2 - 1)

/-- h_Δ = ∏_{p ∣ N} p^{min(v_p(ε_Δ), ⌊v_p(N)/2⌋)}. -/
def hDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  ∏ p ∈ N.primeFactors, p ^ min ((epsDelta N Δ).factorization p) (N.factorization p / 2)

/-- `g` has the form of the generalized Newman bound, with parameter h (and n = N/h²):
`g = ±(1/√e)·[[ae, b/h], [Nc/h, de]]` with `a b c d : ℤ`, `e ≥ 1`, `e ∣ n`, `ade² − bcn = e`.
(Together with e ∣ n, the equation forces e ∥ n.  The sign ± is there because we work in SL₂(ℝ).)
For h = h(N) this is `IsNewmanForm N`.  The statements only use h = h(N) or h = h_Δ, which are ≥ 1
with h² ∣ N, so the divisions by h and the ℕ-division N / h² are exact. -/
def IsNewmanFormH (N h : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ N / h ^ 2 ∧
    a * d * (e : ℤ) ^ 2 - b * c * ((N / h ^ 2 : ℕ) : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / h; (N : ℝ) * c / h, (d : ℝ) * e]

/-! ## s_Δ and ι_Q -/

/-- s_Δ: the number of elements of B(N) = Nor(Γ₀(N))/Γ₀(N) that normalize Γ_Δ(N),
i.e. that have a representative normalizing Γ_Δ(N).  (Since Γ₀(N) normalizes Γ_Δ(N), one
representative does iff all do.) -/
def sDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card {x : B N // ∃ g : SL(2, ℝ), x.IsClassOf g ∧ g ∈ NormG (GammaDeltaR N Δ)}

/-- `u = ι_Q(d)`: u ≡ d⁻¹ mod Q and u ≡ d mod N/Q.  The reductions are `ZMod.cast`
(for N ≥ 1: take the representative in [0, N) and reduce), which for Q ∣ N are the reduction
maps. -/
def IsIota (N Q : ℕ) (d u : (ZMod N)ˣ) : Prop :=
  (ZMod.cast (u : ZMod N) : ZMod Q) * (ZMod.cast (d : ZMod N) : ZMod Q) = 1 ∧
    (ZMod.cast (u : ZMod N) : ZMod (N / Q)) = (ZMod.cast (d : ZMod N) : ZMod (N / Q))

/-- #{Q ∥ N : ι_Q(Δ) = Δ}, where ι_Q(Δ) = Δ is spelled out as
`u ∈ Δ ↔ u = ι_Q(d)` for some `d ∈ Δ`. -/
def sIota (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card {Q : ℕ // Q ∣ N ∧ Nat.Coprime Q (N / Q) ∧ ∀ u, u ∈ Δ ↔ ∃ d ∈ Δ, IsIota N Q d u}

/-! ## Γ(N) and SL₂(ℤ) -/

/-- SL₂(ℤ) as a subgroup of SL₂(ℝ). -/
def SL2ZR : Subgroup SL(2, ℝ) := toR ⊤

/-- Γ(N) in SL₂(ℝ) (Mathlib's `CongruenceSubgroup.Gamma N`: γ ≡ 1 mod N). -/
def GammaR (N : ℕ) : Subgroup SL(2, ℝ) := toR (CongruenceSubgroup.Gamma N)

/-- ±Γ(N) = ⟨Γ(N), −1⟩ in SL₂(ℝ). -/
def pmGammaR (N : ℕ) : Subgroup SL(2, ℝ) := GammaR N ⊔ Subgroup.zpowers (-1)

/-- {±1} ≤ SL₂(ℤ/N) (trivial for N ≤ 2, where −1 = 1). -/
def pmOneSL (N : ℕ) : Subgroup SL(2, ZMod N) := Subgroup.zpowers (-1)

instance (N : ℕ) : (pmOneSL N).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * (-1 : SL(2, ZMod N)) = -1 * g := by rw [mul_neg, neg_mul, mul_one, one_mul]
    rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

/-- Reduction mod N, SL₂(ℤ) → SL₂(ℤ/N). -/
abbrev redSL (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) := SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- The image in SL₂(ℝ) of an integer matrix. -/
abbrev ofZ (γ : SL(2, ℤ)) : SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ) γ

/-- Δ = {d mod N : d ≡ ±1 mod M} ≤ (ℤ/N)ˣ, for M ∣ N. -/
def deltaPm (N M : ℕ) (hM : M ∣ N) : Subgroup (ZMod N)ˣ :=
  (Subgroup.zpowers (-1 : (ZMod M)ˣ)).comap (Units.map (ZMod.castHom hM (ZMod M)).toMonoidHom)

/-! ## ±Γ₁(N) -/

/-- Δ = {±1} ≤ (ℤ/N)ˣ (trivial for N ≤ 2, where −1 = 1). -/
def pmOne (N : ℕ) : Subgroup (ZMod N)ˣ := Subgroup.zpowers (-1)

/-- ±Γ₁(N) = Γ_{±1}(N) in SL₂(ℝ). -/
def pmGamma1R (N : ℕ) : Subgroup SL(2, ℝ) := GammaDeltaR N (pmOne N)

/-- The diamond subgroup of Nor(±Γ₁(N))/±Γ₁(N): the image of Γ₀(N) ∩ Nor(±Γ₁(N)).
(By `Gamma0R_le_normG_pmGamma1R` this intersection is all of Γ₀(N).) -/
def diamonds (N : ℕ) : Subgroup (BG (pmGamma1R N)) :=
  ((Gamma0R N).subgroupOf (NormG (pmGamma1R N))).map
    (QuotientGroup.mk' ((pmGamma1R N).subgroupOf (NormG (pmGamma1R N))))

end

end NormalizerLean

namespace NormalizerLean.Table1

open Finset

/-- The subgroup generated by `-1` and the listed units, with unused generator slots set to `1`. -/
def delta {N : ℕ} (a b c : (ZMod N)ˣ) : Subgroup (ZMod N)ˣ :=
  Subgroup.zpowers (-1) ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c

/-- A row of Table 1. The periods and `h` are witnesses for the finite verification. -/
structure Row where
  level : ℕ
  generator₁ : ℕ
  generator₂ : ℕ
  generator₃ : ℕ
  diamondIndex : ℕ
  modularCount : ℕ
  period₁ : ℕ
  period₂ : ℕ
  period₃ : ℕ
  h : ℕ
  level_ne_zero : level ≠ 0
  coprime₁ : Nat.Coprime generator₁ level
  coprime₂ : Nat.Coprime generator₂ level
  coprime₃ : Nat.Coprime generator₃ level

/-- Construct a row from numerals, checking that the generators are units. -/
def row (N a b c i count r s t h : ℕ) (hN : N ≠ 0 := by decide)
    (ha : Nat.Coprime a N := by decide) (hb : Nat.Coprime b N := by decide)
    (hc : Nat.Coprime c N := by decide) : Row :=
  ⟨N, a, b, c, i, count, r, s, t, h, hN, ha, hb, hc⟩

/-- The first listed generator as a unit modulo the level. -/
def Row.unit₁ (r : Row) : (ZMod r.level)ˣ := ZMod.unitOfCoprime _ r.coprime₁

/-- The second listed generator, or the identity if the slot is unused. -/
def Row.unit₂ (r : Row) : (ZMod r.level)ˣ := ZMod.unitOfCoprime _ r.coprime₂

/-- The third listed generator, or the identity if the slot is unused. -/
def Row.unit₃ (r : Row) : (ZMod r.level)ˣ := ZMod.unitOfCoprime _ r.coprime₃

/-- The subgroup generated by the residues in the paper's second column and by `-1`. -/
def Row.subgroup (r : Row) : Subgroup (ZMod r.level)ˣ := delta r.unit₁ r.unit₂ r.unit₃

/-- The 42 rows of Table 1, in printed order. At levels 37 and 63 the modular count
is the second number in the split entry. -/
def entries : Fin 42 → Row := ![
  row 21 13 8 1 3 12 2 2 1 1,
  row 24 17 7 1 2 8 2 2 1 1,
  row 24 23 5 1 2 8 2 2 1 1,
  row 25 7 1 1 5 10 4 1 1 1,
  row 26 17 1 1 2 8 6 1 1 1,
  row 26 21 1 1 3 12 4 1 1 1,
  row 28 13 15 1 3 36 2 2 1 2,
  row 28 19 1 1 2 8 6 1 1 1,
  row 30 19 11 1 2 16 2 2 1 1,
  row 31 26 1 1 5 10 6 1 1 1,
  row 32 17 31 1 4 32 2 2 1 2,
  row 33 29 1 1 2 8 10 1 1 1,
  row 36 17 19 1 3 36 2 2 1 2,
  row 36 23 1 1 2 48 6 1 1 3,
  row 37 8 1 1 3 6 12 1 1 1,
  row 40 37 31 1 2 8 4 2 1 1,
  row 40 39 21 1 4 64 2 2 1 2,
  row 40 9 21 31 2 32 2 2 2 2,
  row 42 5 1 1 2 16 6 1 1 1,
  row 44 7 1 1 2 8 10 1 1 1,
  row 45 34 44 1 2 48 6 2 1 3,
  row 48 19 47 1 2 32 4 2 1 2,
  row 48 25 17 31 2 32 2 2 2 2,
  row 48 25 47 1 4 64 2 2 1 2,
  row 48 37 47 1 2 96 4 2 1 4,
  row 49 27 1 1 3 168 14 1 1 7,
  row 50 29 1 1 2 120 10 1 1 5,
  row 54 35 1 1 3 108 6 1 1 3,
  row 56 31 29 1 2 32 6 2 1 2,
  row 60 43 11 1 2 16 4 2 1 1,
  row 63 59 37 1 2 48 6 3 1 3,
  row 64 25 63 1 2 192 8 2 1 8,
  row 69 44 1 1 2 8 22 1 1 1,
  row 72 23 53 1 2 48 6 2 1 3,
  row 72 47 1 1 4 96 6 1 1 3,
  row 72 47 37 1 2 192 6 2 1 6,
  row 75 59 1 1 4 240 10 1 1 5,
  row 96 43 95 1 2 128 8 2 1 4,
  row 120 7 71 61 2 64 4 2 2 2,
  row 128 25 127 1 2 256 16 2 1 8,
  row 144 11 71 1 2 576 12 2 1 12,
  row 192 91 191 1 2 384 16 2 1 8]

/-- Every published modular automorphism count in Table 1, together with the
corresponding diamond index. -/
theorem indices (i : Fin 42) :
    let r := entries i
    r.subgroup.index = r.diamondIndex ∧
    Nat.card (BG (GammaDeltaR r.level r.subgroup)) = r.modularCount :=
  sorry

end NormalizerLean.Table1
