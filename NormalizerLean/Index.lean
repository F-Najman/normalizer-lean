module

public import NormalizerLean.Basic

@[expose] public section

/-!
# The index formula [SL₂(ℤ) : Γ₀(t)] = ψ(t)

For a prime p and t ≥ 1, [Γ₀(t) : Γ₀(pt)] = p if p ∣ t and p + 1 otherwise, with explicit coset
representatives [[1, 0], [tv, 1]] (0 ≤ v < p) and, if p ∤ t, [[p, b], [t, d]] (pd − bt = 1).
Induction over the prime factors then gives `Gamma0_index`.
-/

open Matrix MatrixGroups CongruenceSubgroup

namespace NormalizerLean

/-! ### ψ -/

theorem psi_one : psi 1 = 1 := by simp [psi]

theorem psi_prime_mul_of_dvd {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0) (h : p ∣ t) :
    psi (p * t) = p * psi t := by
  unfold psi
  have hsub : ({p} : Finset ℕ) ⊆ t.primeFactors := by
    simpa [Nat.mem_primeFactors] using ⟨hp, h, ht⟩
  rw [Nat.primeFactors_mul hp.ne_zero ht, hp.primeFactors, Finset.union_eq_right.2 hsub]
  push_cast
  ring

theorem psi_prime_mul_of_not_dvd {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0) (h : ¬ p ∣ t) :
    psi (p * t) = (p + 1) * psi t := by
  unfold psi
  have hp' : p ∉ t.primeFactors := by simp [Nat.mem_primeFactors, h]
  rw [Nat.primeFactors_mul hp.ne_zero ht, hp.primeFactors, ← Finset.insert_eq,
    Finset.prod_insert hp']
  have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  push_cast
  field_simp

/-! ### Matrices in SL₂(ℤ) -/

theorem mem_Gamma0_iff_dvd {N : ℕ} {A : SL(2, ℤ)} :
    A ∈ Gamma0 N ↔ (N : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem inv_mul_apply_10 (r γ : SL(2, ℤ)) :
    ((r⁻¹ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (r : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 -
        (r : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two,
    Matrix.mul_apply]
  simp [Fin.sum_univ_two]
  ring

/-- [[1, 0], [t v, 1]]. -/
def lowU (t v : ℤ) : SL(2, ℤ) := ⟨!![1, 0; t * v, 1], by rw [det_fin_two_of]; ring⟩

/-- [[p, b], [t, d]] with pd − bt = 1. -/
def topP (p t b d : ℤ) (h : p * d - b * t = 1) : SL(2, ℤ) :=
  ⟨!![p, b; t, d], by rw [det_fin_two_of]; exact h⟩

theorem lowU_mem (t : ℕ) (v : ℤ) : lowU t v ∈ Gamma0 t := by
  rw [mem_Gamma0_iff_dvd]
  exact ⟨v, rfl⟩

theorem topP_mem {p t : ℕ} {b d : ℤ} (h) : topP p t b d h ∈ Gamma0 t := by
  rw [mem_Gamma0_iff_dvd]
  exact ⟨1, by simp [topP]⟩

theorem Gamma0_mul_le (p t : ℕ) : Gamma0 (p * t) ≤ Gamma0 t := by
  intro A hA
  rw [mem_Gamma0_iff_dvd] at hA ⊢
  exact dvd_trans ⟨p, by push_cast; ring⟩ hA

/-- Lower-left entry criterion for x⁻¹ y ∈ Γ₀(pt). -/
theorem mk_eq_mk_iff_Gamma0 {p t : ℕ} (x y : Gamma0 t) :
    (QuotientGroup.mk x : Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t)) = QuotientGroup.mk y ↔
      ((p * t : ℕ) : ℤ) ∣ ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
          ((y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 -
        ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
          ((y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    mem_Gamma0_iff_dvd, inv_mul_apply_10]

theorem eq_of_dvd_sub {p : ℕ} {u v : ℕ} (hu : u < p) (hv : v < p) (h : (p : ℤ) ∣ (v : ℤ) - u) :
    u = v := by
  have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
  omega

/-- [Γ₀(t) : Γ₀(pt)] = p or p + 1. -/
theorem relIndex_Gamma0_prime_mul {p t : ℕ} (hp : p.Prime) (ht : t ≠ 0) :
    (Gamma0 (p * t)).relIndex (Gamma0 t) = if p ∣ t then p else p + 1 := by
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have ht0 : (t : ℤ) ≠ 0 := Nat.cast_ne_zero.2 ht
  -- cancel t
  have hcancel : ∀ z : ℤ, ((p * t : ℕ) : ℤ) ∣ t * z ↔ (p : ℤ) ∣ z := by
    intro z
    push_cast
    rw [mul_comm (p : ℤ), mul_dvd_mul_iff_left ht0]
  -- the lower representatives
  let L : ℕ → Gamma0 t := fun v => ⟨lowU t v, lowU_mem t v⟩
  have hLmat : ∀ v : ℕ, ((L v : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, 0; (t : ℤ) * v, 1] := fun v => rfl
  have hLL : ∀ u v : ℕ, u < p → v < p →
      (QuotientGroup.mk (L u) : Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t)) =
        QuotientGroup.mk (L v) → u = v := by
    intro u v hu hv h
    rw [mk_eq_mk_iff_Gamma0, hLmat, hLmat] at h
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      head_cons, head_fin_const, one_mul, mul_one] at h
    rw [show (t : ℤ) * v - t * u = t * (v - u) by ring, hcancel] at h
    exact eq_of_dvd_sub hu hv h
  -- surjectivity onto the cosets with p ∤ a
  have hsurjL : ∀ γ : Gamma0 t,
      ¬ (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 →
        ∃ v < p, (QuotientGroup.mk (L v) : Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t)) =
          QuotientGroup.mk γ := by
    intro γ ha
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.1 γ.2
    set a := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    have : Fact p.Prime := ⟨hp⟩
    have ha' : (a : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    let v := ((c : ZMod p) * (a : ZMod p)⁻¹).val
    refine ⟨v, ZMod.val_lt _, ?_⟩
    rw [mk_eq_mk_iff_Gamma0, hLmat, hc]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      head_cons, head_fin_const, one_mul]
    rw [show (t : ℤ) * c - t * v * a = t * (c - v * a) by ring, hcancel,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha', mul_one, sub_self]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  split_ifs with hpt
  · -- p ∣ t: representatives L 0, …, L (p − 1)
    let F : Fin p → Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t) :=
      fun v => QuotientGroup.mk (L v)
    have hbij : Function.Bijective F := by
      refine ⟨fun u v h => Fin.ext (hLL u v u.2 v.2 h), fun q => ?_⟩
      induction q using QuotientGroup.induction_on with
      | H γ =>
        -- p ∤ a, since a d − b c = 1 and p ∣ t ∣ c
        have ha : ¬ (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
          intro hpa
          have hdet := (γ : SL(2, ℤ)).2
          rw [det_fin_two] at hdet
          have hpc : (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
            dvd_trans (Int.natCast_dvd_natCast.2 hpt) (mem_Gamma0_iff_dvd.1 γ.2)
          have : (p : ℤ) ∣ 1 := by
            rw [← hdet]
            exact dvd_sub (dvd_mul_of_dvd_left hpa _) (dvd_mul_of_dvd_right hpc _)
          exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
        obtain ⟨v, hv, hγ⟩ := hsurjL γ ha
        exact ⟨⟨v, hv⟩, hγ⟩
    rw [← Nat.card_eq_of_bijective F hbij, Nat.card_eq_fintype_card, Fintype.card_fin]
  · -- p ∤ t: one more representative [[p, b], [t, d]]
    have hcop : Nat.Coprime p t := (Nat.Prime.coprime_iff_not_dvd hp).2 hpt
    have hb := Int.gcd_eq_gcd_ab p t
    rw [Int.gcd_natCast_natCast, hcop] at hb
    have hdet : (p : ℤ) * Int.gcdA p t - (-Int.gcdB p t) * t = 1 := by
      push_cast at hb
      linarith
    let T : Gamma0 t := ⟨topP p t _ _ hdet, topP_mem hdet⟩
    have hTmat : ((T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![(p : ℤ), -Int.gcdB p t; t, Int.gcdA p t] := rfl
    let F : Option (Fin p) → Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t) :=
      fun o => match o with
        | none => QuotientGroup.mk T
        | some v => QuotientGroup.mk (L v)
    have hLT : ∀ v : ℕ, (QuotientGroup.mk (L v) :
        Gamma0 t ⧸ (Gamma0 (p * t)).subgroupOf (Gamma0 t)) ≠ QuotientGroup.mk T := by
      intro v h
      rw [mk_eq_mk_iff_Gamma0, hLmat, hTmat] at h
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        head_cons, head_fin_const, one_mul] at h
      rw [show (t : ℤ) - t * v * p = t * (1 - v * p) by ring, hcancel] at h
      have : (p : ℤ) ∣ 1 := by
        have := dvd_add h (dvd_mul_left (p : ℤ) v)
        simpa using this
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    have hbij : Function.Bijective F := by
      refine ⟨fun o o' h => ?_, fun q => ?_⟩
      · rcases o with _ | u <;> rcases o' with _ | v
        · rfl
        · exact absurd h.symm (hLT v)
        · exact absurd h (hLT u)
        · exact congrArg some (Fin.ext (hLL u v u.2 v.2 h))
      · induction q using QuotientGroup.induction_on with
        | H γ =>
          by_cases ha : (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
          · refine ⟨none, ?_⟩
            show QuotientGroup.mk T = _
            obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.1 γ.2
            obtain ⟨a', ha'⟩ := ha
            rw [mk_eq_mk_iff_Gamma0, hTmat, hc, ha']
            simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
              cons_val_fin_one, head_cons, head_fin_const]
            rw [show (p : ℤ) * (t * c) - t * (p * a') = t * (p * (c - a')) by ring, hcancel]
            exact dvd_mul_right _ _
          · obtain ⟨v, hv, hγ⟩ := hsurjL γ ha
            exact ⟨some ⟨v, hv⟩, hγ⟩
    rw [← Nat.card_eq_of_bijective F hbij, Nat.card_eq_fintype_card, Fintype.card_option,
      Fintype.card_fin]

/-- **The index formula** [SL₂(ℤ) : Γ₀(t)] = ψ(t). -/
theorem Gamma0_index_aux : ∀ t : ℕ, t ≠ 0 → ((Gamma0 t).index : ℚ) = psi t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.lt_or_ge t 2 with h1 | h2
    · have : t = 1 := by omega
      subst this
      have : Gamma0 1 = ⊤ := by
        ext A
        simp only [Subgroup.mem_top, iff_true]
        rw [Gamma0_mem]
        exact Subsingleton.elim _ _
      rw [this, Subgroup.index_top, psi_one]
      simp
    · obtain ⟨p, hp, t', rfl⟩ : ∃ p, p.Prime ∧ ∃ t', t = p * t' :=
        ⟨t.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd t⟩
      have ht'0 : t' ≠ 0 := by rintro rfl; simp at ht
      have hlt : t' < p * t' := lt_mul_left (Nat.pos_of_ne_zero ht'0) hp.one_lt
      rw [← Subgroup.relIndex_mul_index (Gamma0_mul_le p t'), relIndex_Gamma0_prime_mul hp ht'0,
        Nat.cast_mul, ih t' hlt ht'0]
      split_ifs with hpt
      · rw [psi_prime_mul_of_dvd hp ht'0 hpt]
      · rw [psi_prime_mul_of_not_dvd hp ht'0 hpt]
        push_cast
        ring

theorem Gamma0_index' (t : ℕ) [NeZero t] :
    ((CongruenceSubgroup.Gamma0 t).index : ℚ) = psi t :=
  Gamma0_index_aux t (NeZero.ne t)

end NormalizerLean
