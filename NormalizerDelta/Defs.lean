import NormalizerLean.Defs

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
