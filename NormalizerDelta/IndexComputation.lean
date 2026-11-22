module

public import NormalizerDelta.StatementsStar

import Mathlib.Tactic

/-! Finite computations for the normalizer index formula used in Tables 1 and 2. -/

@[expose] public section

namespace NormalizerLean.IndexComputation

open Finset

/-- The least nonnegative residue of a unit modulo the level. -/
def residue {N : ℕ} (u : (ZMod N)ˣ) : ℕ := (u : ZMod N).val

/-- The least nonnegative residues of all units modulo the level. -/
def unitResidues (N : ℕ) : Finset ℕ :=
  (range N).filter (Nat.Coprime · N)

/-- A positive period suffices to enumerate a cyclic subgroup. -/
theorem mem_zpowers_iff_bounded_pow {G : Type*} [Group G] {a x : G} {r : ℕ}
    (hr : 0 < r) (ha : a ^ r = 1) : x ∈ Subgroup.zpowers a ↔ ∃ i < r, a ^ i = x := by
  classical
  constructor
  · have hf := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, ha⟩
    intro hx
    obtain ⟨i, hi, hix⟩ := mem_image.mp (hf.mem_zpowers_iff_mem_range_orderOf.mp hx)
    have hle : orderOf a ≤ r := Nat.le_of_dvd hr (orderOf_dvd_of_pow_eq_one ha)
    exact ⟨i, (mem_range.mp hi).trans_le hle, hix⟩
  · rintro ⟨i, _, rfl⟩
    exact (Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) _

private def unitEquiv (N : ℕ) [NeZero N] : (ZMod N)ˣ ≃ {d // d ∈ unitResidues N} where
  toFun u := ⟨residue u, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),
    ZMod.val_coe_unit_coprime u⟩⟩
  invFun d := ZMod.unitOfCoprime d.val (mem_filter.mp d.property).2
  left_inv u := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact ZMod.natCast_zmod_val _
  right_inv d := by
    apply Subtype.ext
    dsimp only [residue]
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (mem_range.mp (mem_filter.mp d.property).1)]

private theorem forall_units_iff (N : ℕ) [NeZero N] (P : ℕ → Prop) :
    (∀ u : (ZMod N)ˣ, P (residue u)) ↔ ∀ u ∈ unitResidues N, P u := by
  constructor
  · intro h u hu
    obtain ⟨d, hd⟩ := (unitEquiv N).surjective ⟨u, hu⟩
    have he : residue d = u := congrArg Subtype.val hd
    exact he ▸ h d
  · exact fun h u => h _ ((unitEquiv N) u).property

/-- The condition defining h* in terms of a finite enumeration of residues. -/
def admissible (N : ℕ) (members : Finset ℕ) (h : ℕ) : Prop :=
  0 < h ∧ h ^ 2 ∣ N ∧
    (∀ d ∈ unitResidues N, d ∈ members → d ^ 2 % h = 1 % h) ∧
    ∀ u ∈ unitResidues N, u % (N / h) = 1 % (N / h) → u ∈ members

instance decidableAdmissible (N : ℕ) (members : Finset ℕ) : DecidablePred (admissible N members) :=
  fun h => inferInstanceAs (Decidable
    (0 < h ∧ h ^ 2 ∣ N ∧
      (∀ d ∈ unitResidues N, d ∈ members → d ^ 2 % h = 1 % h) ∧
      ∀ u ∈ unitResidues N, u % (N / h) = 1 % (N / h) → u ∈ members))

private theorem cast_sq_eq_one_iff {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (m : ℕ) :
    (ZMod.cast (u : ZMod N) : ZMod m) ^ 2 = 1 ↔ residue u ^ 2 % m = 1 % m := by
  rw [ZMod.cast_eq_val, ← Nat.cast_pow]
  simpa only [Nat.cast_one, residue] using ZMod.natCast_eq_natCast_iff' (residue u ^ 2) 1 m

private theorem isHStar_iff_admissible {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (members : Finset ℕ) (coverage : ∀ u, u ∈ D ↔ residue u ∈ members) (h : ℕ) :
    IsHStar N D h ↔ admissible N members h := by
  have hone (u : (ZMod N)ˣ) :
      (ZMod.cast (u : ZMod N) : ZMod (N / h)) = 1 ↔ residue u % (N / h) = 1 % (N / h) := by
    rw [ZMod.cast_eq_val]
    simpa only [Nat.cast_one, residue] using
      ZMod.natCast_eq_natCast_iff' (residue u) 1 (N / h)
  unfold IsHStar admissible
  simp only [coverage, cast_sq_eq_one_iff, hone]
  rw [forall_units_iff N (fun d => d ∈ members → d ^ 2 % h = 1 % h),
      forall_units_iff N (fun u => u % (N / h) = 1 % (N / h) → u ∈ members)]

private theorem hStar_eq_findGreatest {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (members : Finset ℕ) (coverage : ∀ u, u ∈ D ↔ residue u ∈ members) :
    hStar N D = Nat.findGreatest (admissible N members) N := by
  classical
  have same (b : ℕ) :
      @Nat.findGreatest (IsHStar N D) (Classical.decPred _) b =
        Nat.findGreatest (admissible N members) b := by
    induction b with
    | zero => rfl
    | succ b ih =>
      simp only [Nat.findGreatest_succ, isHStar_iff_admissible D members coverage, ih]
  exact same N

/-- Every listed residue squares to one modulo the given modulus. -/
def squaresToOne (members : Finset ℕ) (m : ℕ) : Prop :=
  ∀ d ∈ members, d ^ 2 % m = 1 % m

instance (members : Finset ℕ) (m : ℕ) : Decidable (squaresToOne members m) :=
  inferInstanceAs (Decidable (∀ d ∈ members, d ^ 2 % m = 1 % m))

/-- The action on the reduced subgroup is the identity or inversion when one side
of the prime-power decomposition has exponent at most two. -/
def fixesOrInverts (L : ℕ) (members : Finset ℕ) (Q : ℕ) : Prop :=
  (∀ p ∈ L.primeFactors, p ∣ Q → squaresToOne members (p ^ L.factorization p)) ∨
  (∀ p ∈ L.primeFactors, ¬ p ∣ Q → squaresToOne members (p ^ L.factorization p))

instance (L : ℕ) (members : Finset ℕ) (Q : ℕ) :
    Decidable (fixesOrInverts L members Q) := by
  unfold fixesOrInverts
  infer_instance

private theorem isIotaStable_of_fixesOrInverts {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (members : Finset ℕ) (coverage : ∀ u, u ∈ D ↔ residue u ∈ members) (Q : ℕ)
    (h : fixesOrInverts (N / hStar N D) members Q) :
    IsIotaStable N D Q := by
  let L := N / hStar N D
  have matchUnit (d : (ZMod N)ˣ) (hd : d ∈ D) :
      ∃ u ∈ D, IsIotaStar N D Q d u := by
    rcases h with hfix | hinv
    · refine ⟨d, hd, fun p hp => ?_⟩
      split_ifs with hpQ
      · simpa only [pow_two] using
          (cast_sq_eq_one_iff d (p ^ L.factorization p)).mpr (hfix p hp hpQ _ ((coverage d).mp hd))
      · rfl
    · refine ⟨d⁻¹, D.inv_mem hd, fun p hp => ?_⟩
      let m := p ^ L.factorization p
      have hm : m ∣ N := (Nat.ordProj_dvd L p).trans (Nat.div_dvd_of_dvd (hStar_dvd N D))
      have hinvMul : (ZMod.cast (↑(d⁻¹) : ZMod N) : ZMod m) * ZMod.cast (d : ZMod N) = 1 := by
        rw [cast_mul_cast hm, ← Units.val_mul, inv_mul_cancel, Units.val_one, cast_one' hm]
      split_ifs with hpQ
      · exact hinvMul
      · have hsq := (cast_sq_eq_one_iff d m).mpr (hinv p hp hpQ _ ((coverage d).mp hd))
        change (ZMod.cast (↑(d⁻¹) : ZMod N) : ZMod m) = ZMod.cast (d : ZMod N)
        linear_combination
          -(ZMod.cast (↑(d⁻¹) : ZMod N) : ZMod m) * hsq + ZMod.cast (d : ZMod N) * hinvMul
  intro u
  constructor
  · intro hu
    obtain ⟨d, hd, hdu⟩ := matchUnit u hu
    exact ⟨d, hd, isIotaStar_symm hdu⟩
  · rintro ⟨d, hd, hdu⟩
    obtain ⟨v, hv, hdv⟩ := matchUnit d hd
    exact (mem_iff_of_cast_eq (cast_eq_of_isIotaStar hdu hdv)).mpr hv

/-- The positive exact divisors of a positive integer. -/
def exactDivisors (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun Q => Q ∣ n ∧ Nat.Coprime Q (n / Q)

private theorem card_finset_subtype (s : Finset ℕ) : Nat.card {x // x ∈ s} = s.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem wStar_eq_card {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (h : ∀ Q ∈ exactDivisors (nStar N D), IsIotaStable N D Q) :
    wStar N D = (exactDivisors (nStar N D)).card := by
  have hn : 0 < nStar N D := by
    have hm := nStar_mul N D
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh, zero_mul] at hm
    exact NeZero.ne N hm.symm
  rw [← card_finset_subtype]
  unfold wStar
  apply Nat.card_congr (Equiv.subtypeEquivRight _)
  intro Q
  have hrange (hQ : Q ∣ nStar N D) : Q ∈ range (nStar N D + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hn hQ))
  constructor
  · rintro ⟨hQ, hc, _⟩
    exact mem_filter.mpr ⟨hrange hQ, hQ, hc⟩
  · intro hQ
    obtain ⟨hd, hc⟩ := (mem_filter.mp hQ).2
    exact ⟨hd, hc, h Q hQ⟩

private theorem index_eq_div {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (members : Finset ℕ) (coverage : ∀ u, u ∈ D ↔ residue u ∈ members) :
    D.index = (unitResidues N).card / ((unitResidues N).filter (· ∈ members)).card := by
  have e : D ≃ {x // x ∈ (unitResidues N).filter (· ∈ members)} :=
    ((unitEquiv N).subtypeEquiv (p := (· ∈ D)) (q := fun n => n.val ∈ members)
      (fun u => coverage u)).trans
      { toFun := fun x => ⟨x.val.val, mem_filter.mpr ⟨x.val.property, x.property⟩⟩
        invFun := fun x => ⟨⟨x.val, (mem_filter.mp x.property).1⟩, (mem_filter.mp x.property).2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hD := (Nat.card_congr e).trans (card_finset_subtype _)
  have hU := (Nat.card_congr (unitEquiv N)).trans (card_finset_subtype _)
  have h := Subgroup.index_mul_card D
  rw [hD, hU] at h
  rw [← h, Nat.mul_div_cancel]
  exact Nat.card_pos (α := D) |> fun hpos => hD ▸ hpos

/-- A finite subgroup enumeration and stability checks certify the normalizer index.
The three results give the certified value of h*, the diamond index, and the normalizer index. -/
theorem indices_of_checks {N : ℕ} [NeZero N] (D : Subgroup (ZMod N)ˣ)
    (members : Finset ℕ) (h i index : ℕ) (coverage : ∀ u, u ∈ D ↔ residue u ∈ members)
    (hmax : Nat.findGreatest (admissible N members) N = h)
    (hi : (unitResidues N).card / ((unitResidues N).filter (· ∈ members)).card = i)
    (hstable : ∀ Q ∈ exactDivisors (N / h ^ 2), fixesOrInverts (N / h) members Q)
    (hformula : (i : ℚ) * (psi N / psi (N / h ^ 2)) * (exactDivisors (N / h ^ 2)).card = index) :
    hStar N D = h ∧ D.index = i ∧ Nat.card (BG (GammaDeltaR N D)) = index := by
  have hstar : hStar N D = h := (hStar_eq_findGreatest D members coverage).trans hmax
  have hi' : D.index = i := (index_eq_div D members coverage).trans hi
  refine ⟨hstar, hi', ?_⟩
  have he := card_BG_GammaDeltaR_hStar N D
  have hw : wStar N D = (exactDivisors (nStar N D)).card := by
    refine wStar_eq_card _ (fun Q hQ => isIotaStable_of_fixesOrInverts _ _ coverage Q ?_)
    rw [nStar, hstar] at hQ
    rw [hstar]
    exact hstable Q hQ
  rw [hi', hw, nStar, hstar, hformula] at he
  exact_mod_cast he

end NormalizerLean.IndexComputation
