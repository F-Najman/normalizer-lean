module

public import NormalizerDelta.NewmanDelta

@[expose] public section

/-!
# §D: the sanity statements for Γ_Δ(N), ε_Δ, h_Δ

* Γ_{(ℤ/N)ˣ}(N) = Γ₀(N) and Γ_{±1}(N) = Γ₁(N) ⊔ {±1};
* ε_⊤ = gcd(N, 24): gcd(N, 24) ∣ ε_Δ for every Δ (units modulo a divisor of 24 square to 1), and
  ε_⊤ ∣ gcd(N, 24) by the element γ_p of the T2 proof (`exists_gamma_p`), whose lower right entry is
  a unit t with v_p(t − x) = v_p(gcd(N, 24));
* ε_{±1} = N; h(N) ∣ h_Δ; h_Δ² ∣ N; h_⊤ = h(N); the form of `newman_delta` with h(N) is (8′).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

theorem mem_pmOne {u : (ZMod N)ˣ} : u ∈ pmOne N ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rcases Int.even_or_odd k with hk | hk
    · left; exact hk.neg_one_zpow
    · right; exact hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/-- The lower right entry of γ ∈ Γ₀(N) is a unit mod N. -/
theorem exists_unit_of_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
  have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [hc, mul_zero, sub_zero] at h1
    exact h1
  have hd : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by rw [mul_comm]; exact hdet
  exact ⟨(IsUnit.of_mul_eq_one _ hd).unit, rfl⟩

theorem GammaDelta_top' (N : ℕ) : GammaDelta N ⊤ = CongruenceSubgroup.Gamma0 N := by
  ext γ
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨u, hu⟩ := exists_unit_of_mem_Gamma0 h
  exact ⟨u, Subgroup.mem_top _, hu⟩

theorem GammaDelta_pmOne' (N : ℕ) :
    GammaDelta N (pmOne N) = CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1) := by
  apply le_antisymm
  · rintro γ ⟨h0, u, hu, hγ⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have h1 := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
      rw [hc, mul_zero, sub_zero] at h1
      exact h1
    rcases mem_pmOne.1 hu with rfl | rfl
    · apply Subgroup.mem_sup_left
      rw [CongruenceSubgroup.Gamma1_mem]
      simp only [Units.val_one] at hγ
      rw [← hγ, mul_one] at hdet
      exact ⟨hdet, hγ.symm, hc⟩
    · have hm : -γ ∈ CongruenceSubgroup.Gamma1 N := by
        rw [CongruenceSubgroup.Gamma1_mem]
        simp only [Units.val_neg, Units.val_one] at hγ
        rw [← hγ] at hdet
        simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
        refine ⟨?_, by rw [← hγ, neg_neg], by rw [hc, neg_zero]⟩
        linear_combination hdet
      have : γ = (-1) * -γ := by rw [neg_mul, one_mul, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left hm)
  · refine sup_le ?_ ?_
    · intro γ hγ
      rw [CongruenceSubgroup.Gamma1_mem] at hγ
      refine ⟨CongruenceSubgroup.Gamma0_mem.2 hγ.2.2, 1, Subgroup.one_mem _, ?_⟩
      rw [Units.val_one, hγ.2.1]
    · rw [Subgroup.zpowers_le]
      refine ⟨CongruenceSubgroup.Gamma0_mem.2 (by simp), -1, Subgroup.mem_zpowers _, ?_⟩
      simp

/-! ### ε_Δ -/

/-- Units modulo a divisor of 24 square to 1, so gcd(N, 24) ∣ ε_Δ. -/
theorem gcd24_dvd_epsDelta [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Nat.gcd N 24 ∣ epsDelta N Δ := by
  refine dvd_epsDelta_iff.2 ⟨Nat.gcd_dvd_left _ _, fun u _ => ?_⟩
  set k := Nat.gcd N 24
  by_cases hN : N = 1
  · subst hN; simp [k]
  have hN2 : 2 ≤ N := by have := NeZero.ne N; omega
  have h1 := one_le_val_unit hN2 u
  set a : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)
  set d : ℤ := ((u : ZMod N).val : ℤ)
  have had : a * d ≡ 1 [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp [a, d]
  have hadk : a * d ≡ 1 [ZMOD k] := had.of_dvd (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
  have hk : a ≡ d [ZMOD k] := modEq_of_mul_modEq_one (Nat.gcd_dvd_right _ _) hadk
  have hdd : d * d ≡ 1 [ZMOD k] := ((hk.symm.mul_right d).trans (by rw [mul_comm] at hadk ⊢; exact hadk))
  have : (k : ℤ) ∣ d ^ 2 - 1 := by
    have := (Int.ModEq.dvd hdd.symm)
    rw [pow_two]
    exact this
  have h2 : (k : ℤ) ∣ (((u : ZMod N).val ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ h1)]; push_cast; exact this
  exact_mod_cast h2

/-- ε_⊤ ∣ gcd(N, 24), via the element γ_p of the T2 proof. -/
theorem epsDelta_top_dvd [NeZero N] : epsDelta N ⊤ ∣ Nat.gcd N 24 := by
  have hN := NeZero.ne N
  have hε0 : epsDelta N ⊤ ≠ 0 := epsDelta_pos.ne'
  rw [← Nat.factorization_le_iff_dvd hε0 (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)).ne']
  intro p
  have hεN : (epsDelta N ⊤).factorization p ≤ N.factorization p :=
    (Nat.factorization_le_iff_dvd hε0 hN).2 epsDelta_dvd p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  by_cases hpN : p ∣ N
  swap
  · rw [Nat.factorization_eq_zero_of_not_dvd hpN] at hεN; omega
  obtain ⟨x, y, t, hdet, hs⟩ := exists_gamma_p hN hp hpN
  simp only [epsPart] at hs
  rcases hs with hs | ⟨hs0, hvs⟩
  · rw [← hs]; exact hεN
  rw [← hvs]
  -- the unit t mod N
  have htx : ((t : ℤ) : ZMod N) * ((x : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      sub_zero, Int.cast_one] at this
    rw [mul_comm]; exact this
  set u : (ZMod N)ˣ := (IsUnit.of_mul_eq_one _ htx).unit
  set e := (epsDelta N ⊤).factorization p
  have hpe : (p : ℤ) ^ e ∣ (epsDelta N ⊤ : ℤ) := by exact_mod_cast Nat.ordProj_dvd _ p
  have hpeN : (p : ℤ) ^ e ∣ (N : ℤ) := hpe.trans (Int.natCast_dvd_natCast.2 epsDelta_dvd)
  have h1 : (p : ℤ) ^ e ∣ ((u : ZMod N).val : ℤ) ^ 2 - 1 :=
    hpe.trans (epsDelta_dvd_val_int (Subgroup.mem_top u))
  have h2 : (N : ℤ) ∣ ((u : ZMod N).val : ℤ) - t := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp [u]
  have h3 : (p : ℤ) ^ e ∣ t * (t - x) := by
    obtain ⟨k1, hk1⟩ := h1
    obtain ⟨k2, hk2⟩ := hpeN.trans h2
    obtain ⟨k3, hk3⟩ := hpeN
    refine ⟨k1 - k2 * (((u : ZMod N).val : ℤ) + t) - y * k3, ?_⟩
    linear_combination hk1 - (((u : ZMod N).val : ℤ) + t) * hk2 - y * hk3 - hdet
  have hcop : IsCoprime ((p : ℤ) ^ e) t := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    have hpt : (p : ℤ) ∣ t := by
      have := Int.gcd_dvd_right (p : ℤ) t
      have hg' : Int.gcd (p : ℤ) t = p := by
        have hd := Int.gcd_dvd_left (p : ℤ) t
        have : Int.gcd (p : ℤ) t ∣ p := by exact_mod_cast hd
        rcases (Nat.dvd_prime hp).1 this with h | h
        · exact absurd h hg
        · exact h
      rw [hg'] at this; exact this
    have : (p : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (dvd_mul_of_dvd_right hpt _) (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hpN) _)
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hp.one_lt.ne' (by exact_mod_cast this)
  exact (pow_dvd_iff_le_vz hp hs0 e).1 (hcop.dvd_of_dvd_mul_left h3)

theorem epsDelta_top' (N : ℕ) [NeZero N] : epsDelta N ⊤ = Nat.gcd N 24 :=
  Nat.dvd_antisymm epsDelta_top_dvd (gcd24_dvd_epsDelta ⊤)

theorem epsDelta_pmOne' (N : ℕ) [NeZero N] : epsDelta N (pmOne N) = N := by
  refine Nat.dvd_antisymm epsDelta_dvd (dvd_epsDelta_iff.2 ⟨dvd_rfl, fun u hu => ?_⟩)
  by_cases hN : N = 1
  · subst hN; exact one_dvd _
  have h1 := one_le_val_unit (by have := NeZero.ne N; omega) u
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ h1)]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rcases mem_pmOne.1 hu with rfl | rfl <;> simp

/-! ### h_Δ -/

theorem hDelta_ne_zero [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ≠ 0 :=
  (newmanData_delta N Δ).h_pos.ne'

theorem hPart_dvd_hDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hPart N ∣ hDelta N Δ := by
  have hN := NeZero.ne N
  rw [← Nat.factorization_le_iff_dvd (hPart_pos N).ne' (hDelta_ne_zero Δ)]
  intro p
  rw [factorization_hDelta, (local_constants (p := p) hN).2]
  have := (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)).ne'
    epsDelta_pos.ne').2 (gcd24_dvd_epsDelta Δ) p
  exact min_le_min_right _ this

theorem hDelta_sq_dvd' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ^ 2 ∣ N :=
  (newmanData_delta N Δ).h_sq_dvd

theorem hDelta_top' (N : ℕ) [NeZero N] : hDelta N ⊤ = hPart N := by
  have hN := NeZero.ne N
  apply Nat.eq_of_factorization_eq (hDelta_ne_zero ⊤) (hPart_pos N).ne'
  intro p
  rw [factorization_hDelta, (local_constants (p := p) hN).2, epsDelta_top']
  rfl

theorem isNewmanFormH_hPart_iff' (N : ℕ) (g : SL(2, ℝ)) :
    IsNewmanFormH N (hPart N) g ↔ IsNewmanForm N g := Iff.rfl

end

end NormalizerLean
