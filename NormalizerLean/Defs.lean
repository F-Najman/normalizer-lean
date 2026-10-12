import Mathlib

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions

The definitions of the handover note `~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).
They were moved verbatim from `Statements.lean` (frozen at commit 11358c3), so that the proof files can
import them and `Statements.lean` can import the proofs.  No definition changes without the user's
approval.  The conventions are explained in `Statements.lean`.
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
