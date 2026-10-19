module

public import NormalizerDelta.ProofsExtra
public import NormalizerDelta.DefsStar

@[expose] public section

/-!
# Part 7, §S: h*_Δ

The condition C(h) (`IsHStar`) in integer form, its closure under lcm (so the largest h is divisible by every
other one), h*_Δ ∣ h_Δ, and h*_Δ for Γ₀(N), ±Γ₁(N) and X_Δ(M²).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Reductions in integer form -/

theorem cast_val_eq {m : ℕ} [NeZero N] (x : ZMod N) : (ZMod.cast x : ZMod m) = ((x.val : ℕ) : ZMod m) :=
  ZMod.cast_eq_val x

theorem cast_sq_eq_one_iff {m : ℕ} [NeZero N] (x : ZMod N) :
    (ZMod.cast x : ZMod m) ^ 2 = 1 ↔ x.val ^ 2 ≡ 1 [MOD m] := by
  rw [cast_val_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

theorem cast_eq_one_iff {m : ℕ} [NeZero N] (x : ZMod N) :
    (ZMod.cast x : ZMod m) = 1 ↔ x.val ≡ 1 [MOD m] := by
  rw [cast_val_eq, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]

/-- C(h) with the congruences spelled out on representatives. -/
theorem isHStar_iff [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {h : ℕ} :
    IsHStar N Δ h ↔ 0 < h ∧ h ^ 2 ∣ N ∧ (∀ d ∈ Δ, (d : ZMod N).val ^ 2 ≡ 1 [MOD h]) ∧
      ∀ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD N / h] → u ∈ Δ := by
  unfold IsHStar
  simp only [cast_sq_eq_one_iff, cast_eq_one_iff]

theorem one_le_val_of_unit [NeZero N] (hN : N ≠ 1) (u : (ZMod N)ˣ) : 1 ≤ (u : ZMod N).val :=
  one_le_val_unit (by have := NeZero.ne N; omega) u

/-! ### Units ≡ 1 modulo a divisor that every prime of N divides -/

/-- If h² ∣ N, every prime divisor of N divides N/h, so N ∣ (N/h)². -/
theorem dvd_div_sq {h : ℕ} (hh : 0 < h) (hsq : h ^ 2 ∣ N) : N ∣ (N / h) ^ 2 := by
  obtain ⟨k, rfl⟩ := hsq
  have : h ^ 2 * k / h = h * k := by
    rw [sq, mul_assoc, Nat.mul_div_cancel_left _ hh]
  rw [this]
  exact ⟨k, by ring⟩

/-- A natural number ≡ 1 mod N/h (h² ∣ N) is a unit mod N. -/
theorem coprime_of_modEq_one {h k : ℕ} (hh : 0 < h) (hsq : h ^ 2 ∣ N) (hk : k ≡ 1 [MOD N / h]) :
    Nat.Coprime k N := by
  have h1 : Nat.Coprime k (N / h) := by
    unfold Nat.Coprime
    rw [hk.gcd_eq, Nat.gcd_one_left]
  exact Nat.Coprime.coprime_dvd_right (dvd_div_sq hh hsq) (Nat.Coprime.pow_right 2 h1)

/-! ### Closure of C(h) under lcm -/

theorem modEq_lcm {a b m n : ℕ} (h1 : a ≡ b [MOD m]) (h2 : a ≡ b [MOD n]) : a ≡ b [MOD Nat.lcm m n] := by
  have e1 := Nat.modEq_iff_dvd.1 h1
  have e2 := Nat.modEq_iff_dvd.1 h2
  rw [Int.natCast_dvd] at e1 e2
  exact Nat.modEq_iff_dvd.2 (Int.natCast_dvd.2 (Nat.lcm_dvd e1 e2))

theorem lcm_sq_dvd {a b M : ℕ} (ha : 0 < a) (hb : 0 < b) (hM : M ≠ 0) (h1 : a ^ 2 ∣ M) (h2 : b ^ 2 ∣ M) :
    Nat.lcm a b ^ 2 ∣ M := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ (Nat.lcm_ne_zero ha.ne' hb.ne')) hM]
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ ha.ne') hM] at h1
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hb.ne') hM] at h2
  intro p
  have e1 := h1 p
  have e2 := h2 p
  simp only [Nat.factorization_pow, Nat.factorization_lcm ha.ne' hb.ne', Finsupp.smul_apply, smul_eq_mul,
    Finsupp.sup_apply] at e1 e2 ⊢
  rcases le_total (a.factorization p) (b.factorization p) with h | h
  · rw [sup_of_le_right h]; exact e2
  · rw [sup_of_le_left h]; exact e1

theorem isHStar_lcm [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {h₁ h₂ : ℕ} (h1 : IsHStar N Δ h₁)
    (h2 : IsHStar N Δ h₂) : IsHStar N Δ (Nat.lcm h₁ h₂) := by
  rw [isHStar_iff] at h1 h2 ⊢
  obtain ⟨hp1, hs1, hd1, hk1⟩ := h1
  obtain ⟨hp2, hs2, hd2, hk2⟩ := h2
  have hN := NeZero.ne N
  have hL0 : 0 < Nat.lcm h₁ h₂ := Nat.lcm_pos hp1 hp2
  have hLsq : Nat.lcm h₁ h₂ ^ 2 ∣ N := lcm_sq_dvd hp1 hp2 hN hs1 hs2
  refine ⟨hL0, hLsq, fun d hd => modEq_lcm (hd1 d hd) (hd2 d hd), ?_⟩
  intro u hu
  set L := Nat.lcm h₁ h₂
  have hdvd1 : h₁ ∣ N := (dvd_pow_self h₁ two_ne_zero).trans hs1
  have hdvd2 : h₂ ∣ N := (dvd_pow_self h₂ two_ne_zero).trans hs2
  -- gcd(N/h₁, N/h₂) ∣ N/L
  have hg : Nat.gcd (N / h₁) (N / h₂) ∣ N / L := by
    set g := Nat.gcd (N / h₁) (N / h₂)
    have e1 : g * h₁ ∣ N := by
      have := Nat.mul_dvd_mul_right (Nat.gcd_dvd_left (N / h₁) (N / h₂)) h₁
      rwa [Nat.div_mul_cancel hdvd1] at this
    have e2 : g * h₂ ∣ N := by
      have := Nat.mul_dvd_mul_right (Nat.gcd_dvd_right (N / h₁) (N / h₂)) h₂
      rwa [Nat.div_mul_cancel hdvd2] at this
    have : g * L ∣ N := by
      have := Nat.lcm_dvd e1 e2
      rwa [Nat.lcm_mul_left] at this
    exact Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at this)
  have hcong : 1 ≡ (u : ZMod N).val [MOD Nat.gcd (N / h₁) (N / h₂)] :=
    (Nat.ModEq.of_dvd hg hu).symm
  obtain ⟨k, hk1', hk2'⟩ := Nat.chineseRemainder' hcong
  have hkcop : Nat.Coprime k N := coprime_of_modEq_one hp1 hs1 hk1'
  let u₁ : (ZMod N)ˣ := ZMod.unitOfCoprime k hkcop
  have hu₁val : (u₁ : ZMod N).val ≡ k [MOD N] := by
    simp only [u₁, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq k N
  have hu₁ : u₁ ∈ Δ := hk1 u₁ ((Nat.ModEq.of_dvd (Nat.div_dvd_of_dvd hdvd1) hu₁val).trans hk1')
  -- u₁ ≡ u mod N/h₂, so u * u₁⁻¹ ≡ 1 mod N/h₂
  have hK2 : N / h₂ ∣ N := Nat.div_dvd_of_dvd hdvd2
  have hcast : ZMod.castHom hK2 (ZMod (N / h₂)) (u₁ : ZMod N) =
      ZMod.castHom hK2 (ZMod (N / h₂)) (u : ZMod N) := by
    rw [ZMod.castHom_apply, ZMod.castHom_apply, cast_val_eq, cast_val_eq,
      ZMod.natCast_eq_natCast_iff]
    exact (Nat.ModEq.of_dvd hK2 hu₁val).trans hk2'
  have hu₂ : u * u₁⁻¹ ∈ Δ := by
    apply hk2
    rw [← cast_eq_one_iff]
    rw [← ZMod.castHom_apply (h := hK2), Units.val_mul, map_mul, ← hcast, ← map_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, map_one]
  have := Δ.mul_mem hu₂ hu₁
  rwa [inv_mul_cancel_right] at this

/-! ### h*_Δ -/

theorem isHStar_one' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : IsHStar N Δ 1 := by
  refine ⟨one_pos, by simp, fun d _ => Subsingleton.elim _ _, fun u hu => ?_⟩
  rw [Nat.div_one, ZMod.cast_id', id] at hu
  rw [show u = 1 from Units.ext hu]
  exact Δ.one_mem

theorem le_of_isHStar [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {h : ℕ} (hh : IsHStar N Δ h) : h ≤ N :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) ((dvd_pow_self h two_ne_zero).trans hh.2.1)

theorem isHStar_hStar' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : IsHStar N Δ (hStar N Δ) := by
  classical
  unfold hStar
  exact Nat.findGreatest_spec (m := 1) (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) (isHStar_one' N Δ)

theorem dvd_hStar' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {h : ℕ} (hh : IsHStar N Δ h) :
    h ∣ hStar N Δ := by
  classical
  have hL := isHStar_lcm hh (isHStar_hStar' N Δ)
  have hle : Nat.lcm h (hStar N Δ) ≤ hStar N Δ := by
    unfold hStar at hL ⊢
    exact Nat.le_findGreatest (le_of_isHStar hL) hL
  have heq : Nat.lcm h (hStar N Δ) = hStar N Δ :=
    le_antisymm hle (Nat.le_of_dvd hL.1 (Nat.dvd_lcm_right _ _))
  rw [← heq]
  exact Nat.dvd_lcm_left _ _

theorem hStar_pos (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : 0 < hStar N Δ := (isHStar_hStar' N Δ).1

theorem hStar_sq_dvd (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hStar N Δ ^ 2 ∣ N :=
  (isHStar_hStar' N Δ).2.1

theorem hStar_dvd (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hStar N Δ ∣ N :=
  (dvd_pow_self _ two_ne_zero).trans (hStar_sq_dvd N Δ)

theorem nStar_mul (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : nStar N Δ * hStar N Δ ^ 2 = N :=
  Nat.div_mul_cancel (hStar_sq_dvd N Δ)

instance nStar_neZero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : NeZero (nStar N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nStar_mul N Δ, h, zero_mul])⟩

/-- N / h* = n* h*. -/
theorem div_hStar (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : N / hStar N Δ = nStar N Δ * hStar N Δ := by
  apply Nat.div_eq_of_eq_mul_left (hStar_pos N Δ)
  rw [mul_assoc, ← sq, nStar_mul]

/-- d² ≡ 1 mod h* for d ∈ Δ, in ℤ. -/
theorem hStar_dvd_sq_sub_one [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {d : (ZMod N)ˣ} (hd : d ∈ Δ) :
    (hStar N Δ : ℤ) ∣ ((d : ZMod N).val : ℤ) ^ 2 - 1 := by
  have h := ((isHStar_iff.1 (isHStar_hStar' N Δ)).2.2.1 d hd)
  have := (Nat.modEq_iff_dvd.1 h.symm)
  push_cast at this
  exact this

/-- Δ contains every unit ≡ 1 mod N/h*, in ℤ. -/
theorem mem_of_dvd_sub_one [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {u : (ZMod N)ˣ}
    (hu : ((N / hStar N Δ : ℕ) : ℤ) ∣ ((u : ZMod N).val : ℤ) - 1) : u ∈ Δ := by
  apply (isHStar_iff.1 (isHStar_hStar' N Δ)).2.2.2 u
  apply Nat.ModEq.symm
  exact (Nat.modEq_iff_dvd.2 (by push_cast; exact hu))

/-- Two units congruent mod N/h*: one is in Δ iff the other is. -/
theorem mem_iff_of_cast_eq [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {u v : (ZMod N)ˣ}
    (huv : (ZMod.cast (u : ZMod N) : ZMod (N / hStar N Δ)) = ZMod.cast (v : ZMod N)) :
    u ∈ Δ ↔ v ∈ Δ := by
  have hK : N / hStar N Δ ∣ N := Nat.div_dvd_of_dvd (hStar_dvd N Δ)
  have hk : ∀ w : (ZMod N)ˣ, ZMod.castHom hK (ZMod (N / hStar N Δ)) (w : ZMod N) = 1 → w ∈ Δ := by
    intro w hw
    rw [ZMod.castHom_apply] at hw
    exact (isHStar_hStar' N Δ).2.2.2 w hw
  have e : ZMod.castHom hK (ZMod (N / hStar N Δ)) (u : ZMod N) =
      ZMod.castHom hK (ZMod (N / hStar N Δ)) (v : ZMod N) := by
    rw [ZMod.castHom_apply, ZMod.castHom_apply, huv]
  constructor
  · intro hu
    have : u⁻¹ * v ∈ Δ := hk _ (by
      rw [Units.val_mul, map_mul, ← e, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
    have := Δ.mul_mem hu this
    rwa [mul_inv_cancel_left] at this
  · intro hv
    have : v⁻¹ * u ∈ Δ := hk _ (by
      rw [Units.val_mul, map_mul, e, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
    have := Δ.mul_mem hv this
    rwa [mul_inv_cancel_left] at this

/-! ### h*_Δ ∣ h_Δ -/

theorem hDelta_dvd_epsDelta [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hDelta N Δ ∣ epsDelta N Δ := by
  rw [← Nat.factorization_le_iff_dvd (hDelta_ne_zero Δ) (epsDelta_pos (Δ := Δ)).ne']
  intro p
  rw [factorization_hDelta]
  exact min_le_left _ _

theorem dvd_hDelta_of_isHStar [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {h : ℕ} (hh : IsHStar N Δ h) :
    h ∣ hDelta N Δ := by
  obtain ⟨hp, hs, hd, -⟩ := isHStar_iff.1 hh
  have hN := NeZero.ne N
  have hε : h ∣ epsDelta N Δ := by
    refine dvd_epsDelta_iff.2 ⟨(dvd_pow_self h two_ne_zero).trans hs, fun u hu => ?_⟩
    by_cases hN1 : N = 1
    · subst hN1
      have : h ∣ 1 := (dvd_pow_self h two_ne_zero).trans hs
      have h1 : h = 1 := Nat.dvd_one.1 this
      subst h1
      exact one_dvd _
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (one_le_val_of_unit hN1 u))).1 (hd u hu).symm
  rw [← Nat.factorization_le_iff_dvd hp.ne' (hDelta_ne_zero Δ)]
  intro p
  rw [factorization_hDelta]
  refine le_min ((Nat.factorization_le_iff_dvd hp.ne' (epsDelta_pos (Δ := Δ)).ne').2 hε p) ?_
  have := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne') hN).2 hs p
  rw [Nat.factorization_pow] at this
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  omega

theorem hStar_dvd_hDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : hStar N Δ ∣ hDelta N Δ :=
  dvd_hDelta_of_isHStar (isHStar_hStar' N Δ)

/-! ### Γ₀(N), ±Γ₁(N) and X_Δ(M²) -/

theorem hStar_top' (N : ℕ) [NeZero N] : hStar N ⊤ = hPart N := by
  apply Nat.dvd_antisymm
  · rw [← hDelta_top']; exact hStar_dvd_hDelta' N ⊤
  · apply dvd_hStar'
    have hdvd : hPart N ∣ epsDelta N ⊤ := by rw [← hDelta_top']; exact hDelta_dvd_epsDelta ⊤
    refine isHStar_iff.2 ⟨hPart_pos N, hPart_sq_dvd (NeZero.ne N), fun d _ => ?_, fun u _ => Subgroup.mem_top u⟩
    by_cases hN1 : N = 1
    · subst hN1
      have : hPart 1 = 1 := Nat.dvd_one.1 ((dvd_pow_self _ two_ne_zero).trans (hPart_sq_dvd one_ne_zero))
      rw [this]; exact Nat.modEq_one
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (one_le_val_of_unit hN1 d))).2
      (hdvd.trans (epsDelta_dvd_val (Subgroup.mem_top d)))).symm

theorem eq_one_of_isHStar_pmOne [NeZero N] (hN : N ≠ 4) {h : ℕ} (hh : IsHStar N (pmOne N) h) : h = 1 := by
  obtain ⟨hp, hs, -, hk⟩ := isHStar_iff.1 hh
  have hN0 := NeZero.ne N
  by_contra h1
  have h2 : 2 ≤ h := by omega
  have hdvd : h ∣ N := (dvd_pow_self h two_ne_zero).trans hs
  have hN4 : 4 ≤ N := le_trans (by nlinarith) (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hs)
  set K := N / h with hKdef
  have hKpos : 0 < K := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd) hp
  have hKN : K * h = N := Nat.div_mul_cancel hdvd
  have hKle : 2 * K ≤ N := by rw [← hKN]; nlinarith
  have hK1 : 1 + K ≡ 1 [MOD K] := Nat.add_mod_right 1 K
  have hKdvd : K ∣ N := Nat.div_dvd_of_dvd hdvd
  have hcop : Nat.Coprime (1 + K) N := coprime_of_modEq_one hp hs hK1
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime (1 + K) hcop
  have hu : u ∈ pmOne N := hk u (by
    simp only [u, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact (Nat.ModEq.of_dvd hKdvd (Nat.mod_modEq _ _)).trans hK1)
  rcases mem_pmOne.1 hu with h3 | h3
  · have := congrArg (fun x : (ZMod N)ˣ => (x : ZMod N)) h3
    simp only [u, ZMod.coe_unitOfCoprime, Units.val_one] at this
    have : ((K : ℕ) : ZMod N) = 0 := by push_cast at this; linear_combination this
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd hKpos this
    omega
  · have := congrArg (fun x : (ZMod N)ˣ => (x : ZMod N)) h3
    simp only [u, ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one] at this
    have : ((K + 2 : ℕ) : ZMod N) = 0 := by push_cast at this ⊢; linear_combination this
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    have : N = 4 := by omega
    exact hN this

theorem hStar_pmOne' {N : ℕ} [NeZero N] (hN : N ≠ 4) : hStar N (pmOne N) = 1 :=
  eq_one_of_isHStar_pmOne hN (isHStar_hStar' N (pmOne N))

theorem hStar_pmOne_four' : hStar 4 (pmOne 4) = 2 := by
  have h2 : IsHStar 4 (pmOne 4) 2 := by
    refine isHStar_iff.2 ⟨by norm_num, by norm_num, fun d hd => ?_, fun u _ => ?_⟩
    · rcases mem_pmOne.1 hd with rfl | rfl <;> decide
    · rw [mem_pmOne]; revert u; decide
  have hd := dvd_hStar' (pmOne 4) h2
  have hs := hStar_sq_dvd 4 (pmOne 4)
  have hle : hStar 4 (pmOne 4) ≤ 2 := by
    have := Nat.le_of_dvd (by norm_num) hs
    nlinarith
  have := Nat.le_of_dvd (hStar_pos 4 _) hd
  omega

theorem hStar_deltaPm_sq' (M : ℕ) [NeZero M] :
    hStar (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)) = M := by
  have hM := NeZero.ne M
  have hM0 : 0 < M := Nat.pos_of_ne_zero hM
  set Δ := deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)
  have hdiv : M ^ 2 / M = M := by rw [sq, Nat.mul_div_cancel _ hM0]
  have hC : IsHStar (M ^ 2) Δ M := by
    refine ⟨hM0, dvd_rfl, fun d hd => ?_, fun u hu => ?_⟩
    · rcases mem_deltaPm.1 hd with h1 | h1 <;> rw [ZMod.castHom_apply] at h1 <;> rw [h1] <;> ring
    · apply mem_deltaPm.2
      left
      rw [ZMod.castHom_apply]
      generalize hK : M ^ 2 / M = K at hu
      have : K = M := hK ▸ hdiv
      subst this
      exact hu
  apply Nat.dvd_antisymm _ (dvd_hStar' Δ hC)
  have := hStar_sq_dvd (M ^ 2) Δ
  exact (Nat.pow_dvd_pow_iff two_ne_zero).1 this

end

end NormalizerLean
