module

public import NormalizerDelta.StarCount

@[expose] public section

/-!
# Part 7: the link with Part 2's count, and two sanity checks

* For h* = 1, ι*_Q is Part 2's ι_Q (`IsIota`), prime power by prime power, so w*_Δ = s_ι(Δ).
* X_Δ(50), Δ = {±1 mod 5}: h* = 5, n* = 2, i_Δ = 2, w* = 2: 2 · 90/3 · 2 = 120.
* Γ₁(4) = Γ_{1}(4): h* = 1, n* = 4, i_Δ = 2, w* = 2: 2 · 1 · 2 = 4.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-- `IsIotaStar` with the level N/h* named. -/
theorem isIotaStar_iff_of_eq {Δ : Subgroup (ZMod N)ˣ} {Q : ℕ} {d u : (ZMod N)ˣ} {L : ℕ}
    (hL : N / hStar N Δ = L) :
    IsIotaStar N Δ Q d u ↔ ∀ p ∈ L.primeFactors,
      if p ∣ Q then (ZMod.cast (u : ZMod N) : ZMod (p ^ L.factorization p)) *
          (ZMod.cast (d : ZMod N) : ZMod (p ^ L.factorization p)) = 1
      else (ZMod.cast (u : ZMod N) : ZMod (p ^ L.factorization p)) =
          (ZMod.cast (d : ZMod N) : ZMod (p ^ L.factorization p)) := by
  subst hL; rfl

theorem cast_mul_cast [NeZero N] {m : ℕ} (hm : m ∣ N) (x y : ZMod N) :
    (ZMod.cast x : ZMod m) * (ZMod.cast y : ZMod m) = ZMod.cast (x * y) := by
  rw [← ZMod.castHom_apply (h := hm), ← ZMod.castHom_apply (h := hm), ← ZMod.castHom_apply (h := hm),
    map_mul]

theorem cast_one' [NeZero N] {m : ℕ} (hm : m ∣ N) : (ZMod.cast (1 : ZMod N) : ZMod m) = 1 := by
  rw [← ZMod.castHom_apply (h := hm), map_one]

/-- For Q ∥ N, the congruences prime power by prime power are Part 2's ι_Q. -/
theorem forall_primePow_iff_isIota [NeZero N] {Q : ℕ} (hQ : Q ∣ N) (hc : Nat.Coprime Q (N / Q))
    (d u : (ZMod N)ˣ) :
    (∀ p ∈ N.primeFactors,
      if p ∣ Q then (ZMod.cast (u : ZMod N) : ZMod (p ^ N.factorization p)) *
          (ZMod.cast (d : ZMod N) : ZMod (p ^ N.factorization p)) = 1
      else (ZMod.cast (u : ZMod N) : ZMod (p ^ N.factorization p)) =
          (ZMod.cast (d : ZMod N) : ZMod (p ^ N.factorization p))) ↔ IsIota N Q d u := by
  have hN := NeZero.ne N
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hN (Nat.eq_zero_of_zero_dvd hQ)
  have hK : N / Q ∣ N := Nat.div_dvd_of_dvd hQ
  have hK0 : N / Q ≠ 0 := fun h => hN (by rw [← Nat.div_mul_cancel hQ, h, zero_mul])
  have hNQ : N = Q * (N / Q) := (Nat.mul_div_cancel' hQ).symm
  -- everything in terms of divisibility of two integers
  set z₁ : ℤ := ((1 : ZMod N).val : ℤ) - ((u : ZMod N) * d).val
  set z₂ : ℤ := ((d : ZMod N).val : ℤ) - (u : ZMod N).val
  have e1 : ∀ {m : ℕ}, m ∣ N → ((ZMod.cast (u : ZMod N) : ZMod m) * (ZMod.cast (d : ZMod N) : ZMod m) = 1 ↔
      (m : ℤ) ∣ z₁) := by
    intro m hm
    rw [cast_mul_cast hm, ← cast_one' hm, cast_eq_cast_iff]
  have e2 : ∀ {m : ℕ}, (ZMod.cast (u : ZMod N) : ZMod m) = ZMod.cast (d : ZMod N) ↔ (m : ℤ) ∣ z₂ :=
    fun {m} => cast_eq_cast_iff _ _
  have hpow : ∀ p, p ^ N.factorization p ∣ N := fun p => Nat.ordProj_dvd N p
  unfold IsIota
  rw [e1 hQ, e2]
  constructor
  · intro h
    constructor
    · apply dvd_of_forall_primePow_dvd hQ0
      intro p hp
      have hpQ : p ∣ Q := Nat.dvd_of_mem_primeFactors hp
      have hpN : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp, hpQ.trans hQ, hN⟩
      have := h p hpN
      rw [if_pos hpQ, e1 (hpow p)] at this
      exact (Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow p ((Nat.factorization_le_iff_dvd hQ0 hN).2 hQ p))).trans this
    · apply dvd_of_forall_primePow_dvd hK0
      intro p hp
      have hpK : p ∣ N / Q := Nat.dvd_of_mem_primeFactors hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpQ : ¬ p ∣ Q := fun h => (Nat.Prime.coprime_iff_not_dvd hpr).1
        (Nat.Coprime.coprime_dvd_left h hc) hpK
      have hpN : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hpr, hpK.trans hK, hN⟩
      have := h p hpN
      rw [if_neg hpQ, e2] at this
      exact (Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow p ((Nat.factorization_le_iff_dvd hK0 hN).2 hK p))).trans this
  · rintro ⟨h1, h2⟩ p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    split_ifs with hpQ
    · rw [e1 (hpow p)]
      have hpK : ¬ p ∣ N / Q := fun h => (Nat.Prime.coprime_iff_not_dvd hpr).1
        (Nat.Coprime.coprime_dvd_left hpQ hc) h
      have : p ^ N.factorization p ∣ Q := by
        have h3 := hpow p
        rw [hNQ] at h3
        exact (coprime_primePow hpr hpK).dvd_of_dvd_mul_right (by rwa [← hNQ] at h3 ⊢)
      exact (Int.natCast_dvd_natCast.2 this).trans h1
    · rw [e2]
      have : p ^ N.factorization p ∣ N / Q := by
        have h3 := hpow p
        rw [hNQ] at h3
        exact (coprime_primePow hpr hpQ).dvd_of_dvd_mul_left (by rwa [← hNQ] at h3 ⊢)
      exact (Int.natCast_dvd_natCast.2 this).trans h2

theorem wStar_eq_sIota' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) (h : hStar N Δ = 1) :
    wStar N Δ = sIota N Δ := by
  have hn : nStar N Δ = N := by simp [nStar, h]
  have hL : N / hStar N Δ = N := by simp [h]
  unfold wStar sIota
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun Q => ?_)
  rw [hn]
  constructor
  · rintro ⟨hQ, hc, hst⟩
    refine ⟨hQ, hc, fun u => ?_⟩
    rw [hst u]
    simp only [isIotaStar_iff_of_eq hL, forall_primePow_iff_isIota hQ hc]
  · rintro ⟨hQ, hc, hst⟩
    refine ⟨hQ, hc, fun u => ?_⟩
    rw [hst u]
    simp only [isIotaStar_iff_of_eq hL, forall_primePow_iff_isIota hQ hc]

/-! ### X_Δ(50), Δ = {±1 mod 5} -/

theorem factorization_ten_two : (10 : ℕ).factorization 2 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization, Nat.prime_five.factorization]
  simp

theorem factorization_ten_five : (10 : ℕ).factorization 5 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.prime_two.factorization, Nat.prime_five.factorization]
  simp

theorem primeFactors_ten : (10 : ℕ).primeFactors = {2, 5} := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, Nat.prime_five.primeFactors]
  rfl

theorem index_deltaPm_50 : (deltaPm 50 5 (by norm_num)).index = 2 := by
  unfold deltaPm
  rw [show (Units.map (ZMod.castHom (by norm_num : 5 ∣ 50) (ZMod 5)).toMonoidHom) =
    ZMod.unitsMap (by norm_num : 5 ∣ 50) from rfl,
    Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)]
  have h1 := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod 5)ˣ))
  rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by decide) (by decide), Nat.card_eq_fintype_card,
    show Fintype.card (ZMod 5)ˣ = 4 by rfl] at h1
  omega

theorem mem_deltaPm_50 {u : (ZMod 50)ˣ} :
    u ∈ deltaPm 50 5 (by norm_num) ↔ ((ZMod.cast (u : ZMod 50) : ZMod 5) = 1 ∨
      (ZMod.cast (u : ZMod 50) : ZMod 5) = -1) := by
  rw [mem_deltaPm, ZMod.castHom_apply]

theorem hStar_50 : hStar 50 (deltaPm 50 5 (by norm_num)) = 5 := by
  have h5 : IsHStar 50 (deltaPm 50 5 (by norm_num)) 5 := by
    refine ⟨by norm_num, by norm_num, fun d hd => ?_, fun u hu => ?_⟩
    · rcases mem_deltaPm_50.1 hd with h | h <;> rw [h] <;> ring
    · rw [show (50 : ℕ) / 5 = 10 by norm_num, cast_eq_one_iff] at hu
      apply mem_deltaPm_50.2
      left
      rw [cast_eq_one_iff]
      exact Nat.ModEq.of_dvd (by norm_num) hu
  have hd := dvd_hStar' _ h5
  have hs := hStar_sq_dvd 50 (deltaPm 50 5 (by norm_num))
  have hle := Nat.le_of_dvd (by norm_num) hs
  have hpos := hStar_pos 50 (deltaPm 50 5 (by norm_num))
  obtain ⟨k, hk⟩ := hd
  rw [hk] at hle hpos ⊢
  have : k ≤ 1 := by nlinarith
  obtain rfl : k = 1 := by omega
  rfl

theorem nStar_50 : nStar 50 (deltaPm 50 5 (by norm_num)) = 2 := by
  rw [nStar, hStar_50]; norm_num

/-- A unit mod 50 has an odd representative. -/
theorem two_dvd_one_sub_val (x : (ZMod 50)ˣ) : (2 : ℤ) ∣ ((1 : ZMod 50).val : ℤ) - ((x : ZMod 50).val : ℤ) := by
  have hc := ZMod.val_coe_unit_coprime x
  have hc2 : Nat.Coprime (x : ZMod 50).val 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have h2 : ¬ 2 ∣ (x : ZMod 50).val := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hc2.symm
  have h1 : (1 : ZMod 50).val = 1 := rfl
  rw [h1]
  omega

theorem wStar_50 : wStar 50 (deltaPm 50 5 (by norm_num)) = 2 := by
  set Δ := deltaPm 50 5 (by norm_num)
  have hL : 50 / hStar 50 Δ = 10 := by rw [hStar_50]
  have hq2 : 2 ^ (10 : ℕ).factorization 2 ∣ 2 := by
    rw [factorization_ten_two]; norm_num
  have hq5 : 5 ∣ 5 ^ (10 : ℕ).factorization 5 := by
    rw [factorization_ten_five]; norm_num
  have h2 : IsIotaStable 50 Δ 2 := by
    intro u
    rw [exists_congr fun d => and_congr_right fun _ => isIotaStar_iff_of_eq hL]
    constructor
    · intro hu
      refine ⟨u, hu, fun p hp => ?_⟩
      rw [primeFactors_ten, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · have hq50 : 2 ^ (10 : ℕ).factorization 2 ∣ 50 := hq2.trans (by norm_num)
        rw [if_pos dvd_rfl, cast_mul_cast hq50 _ _, ← cast_one' hq50, cast_eq_cast_iff]
        exact (Int.natCast_dvd_natCast.2 hq2).trans (two_dvd_one_sub_val (u * u))
      · rw [if_neg (by norm_num)]
    · rintro ⟨d, hd, hdu⟩
      have h5 := hdu 5 (by rw [primeFactors_ten]; simp)
      rw [if_neg (by norm_num), cast_eq_cast_iff] at h5
      have h5' : (ZMod.cast (u : ZMod 50) : ZMod 5) = ZMod.cast (d : ZMod 50) := by
        rw [cast_eq_cast_iff]; exact (Int.natCast_dvd_natCast.2 hq5).trans h5
      apply mem_deltaPm_50.2
      rw [h5']
      exact mem_deltaPm_50.1 hd
  unfold wStar
  rw [nStar_50]
  have : {Q : ℕ | Q ∣ 2 ∧ Nat.Coprime Q (2 / Q) ∧ IsIotaStable 50 Δ Q} = {1, 2} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQ, -, -⟩
      have := Nat.le_of_dvd (by norm_num) hQ
      interval_cases Q <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, Nat.coprime_one_left _, isIotaStable_one' 50 Δ⟩
      · exact ⟨dvd_rfl, by norm_num, h2⟩
  change Nat.card {Q : ℕ | Q ∣ 2 ∧ Nat.Coprime Q (2 / Q) ∧ IsIotaStable 50 Δ Q} = 2
  rw [this, Nat.card_coe_set_eq, Set.ncard_pair (by norm_num)]

theorem psi_50 : psi 50 = 90 := by
  rw [psi, show (50 : ℕ) = 2 * 25 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    show (25 : ℕ) = 5 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_five,
    Nat.prime_two.primeFactors]
  rw [show ({2} ∪ {5} : Finset ℕ) = {2, 5} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem psi_two : psi 2 = 3 := by
  rw [psi, Nat.prime_two.primeFactors, Finset.prod_singleton]; norm_num

theorem card_BG_GammaDeltaR_50' :
    Nat.card (BG (GammaDeltaR 50 (deltaPm 50 5 (by norm_num)))) = 120 := by
  have h := card_BG_GammaDeltaR_hStar' 50 (deltaPm 50 5 (by norm_num))
  rw [index_deltaPm_50, nStar_50, wStar_50, psi_50, psi_two] at h
  norm_num at h
  exact_mod_cast h

/-! ### Γ₁(4) = Γ_{1}(4) -/

theorem hStar_4_bot : hStar 4 ⊥ = 1 := by
  have hs := hStar_sq_dvd 4 (⊥ : Subgroup (ZMod 4)ˣ)
  have hle := Nat.le_of_dvd (by norm_num) hs
  have hpos := hStar_pos 4 (⊥ : Subgroup (ZMod 4)ˣ)
  have h2 : hStar 4 (⊥ : Subgroup (ZMod 4)ˣ) ≤ 2 := by nlinarith
  have hne : hStar 4 (⊥ : Subgroup (ZMod 4)ˣ) ≠ 2 := by
    intro h
    have hC := isHStar_iff.1 (isHStar_hStar' 4 (⊥ : Subgroup (ZMod 4)ˣ))
    rw [h] at hC
    have := hC.2.2.2 (-1) (by decide)
    rw [Subgroup.mem_bot] at this
    exact absurd this (by decide)
  omega

theorem wStar_4_bot : wStar 4 ⊥ = 2 := by
  have hn : nStar 4 (⊥ : Subgroup (ZMod 4)ˣ) = 4 := by rw [nStar, hStar_4_bot]; norm_num
  have hL : 4 / hStar 4 (⊥ : Subgroup (ZMod 4)ˣ) = 4 := by rw [hStar_4_bot]
  have hpf : (4 : ℕ).primeFactors = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  have hf : 2 ^ (4 : ℕ).factorization 2 = 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.prime_two.factorization_pow]; simp
  have h4 : IsIotaStable 4 (⊥ : Subgroup (ZMod 4)ˣ) 4 := by
    intro u
    rw [exists_congr fun d => and_congr_right fun _ => isIotaStar_iff_of_eq hL]
    constructor
    · intro hu
      rw [Subgroup.mem_bot] at hu
      subst hu
      refine ⟨1, Subgroup.one_mem _, fun p hp => ?_⟩
      rw [hpf, Finset.mem_singleton] at hp
      subst hp
      rw [if_pos (by norm_num), Units.val_one, cast_one' (Nat.ordProj_dvd 4 2), mul_one]
    · rintro ⟨d, hd, hdu⟩
      rw [Subgroup.mem_bot] at hd
      subst hd
      have h2 := hdu 2 (by rw [hpf]; simp)
      rw [if_pos (by norm_num), Units.val_one, cast_one' (Nat.ordProj_dvd 4 2), mul_one] at h2
      revert h2
      generalize 2 ^ (4 : ℕ).factorization 2 = q at hf ⊢
      subst hf
      intro h2
      rw [ZMod.cast_id', id] at h2
      exact (Subgroup.mem_bot).2 (Units.ext h2)
  unfold wStar
  rw [hn]
  have : {Q : ℕ | Q ∣ 4 ∧ Nat.Coprime Q (4 / Q) ∧ IsIotaStable 4 (⊥ : Subgroup (ZMod 4)ˣ) Q} = {1, 4} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQ, hc, -⟩
      have := Nat.le_of_dvd (by norm_num) hQ
      interval_cases Q <;> simp_all <;> norm_num at hc
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, Nat.coprime_one_left _, isIotaStable_one' 4 ⊥⟩
      · exact ⟨dvd_rfl, by norm_num, h4⟩
  change Nat.card {Q : ℕ | Q ∣ 4 ∧ Nat.Coprime Q (4 / Q) ∧ IsIotaStable 4 (⊥ : Subgroup (ZMod 4)ˣ) Q} = 2
  rw [this, Nat.card_coe_set_eq, Set.ncard_pair (by norm_num)]

theorem card_BG_GammaDeltaR_4_bot' : Nat.card (BG (GammaDeltaR 4 ⊥)) = 4 := by
  have h := card_BG_GammaDeltaR_hStar' 4 (⊥ : Subgroup (ZMod 4)ˣ)
  have hn : nStar 4 (⊥ : Subgroup (ZMod 4)ˣ) = 4 := by rw [nStar, hStar_4_bot]; norm_num
  have hidx : (⊥ : Subgroup (ZMod 4)ˣ).index = 2 := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card]; rfl
  have hψ : psi 4 ≠ 0 := by
    rw [psi, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    norm_num
  rw [hidx, hn, wStar_4_bot, div_self hψ] at h
  norm_num at h
  exact_mod_cast h

end

end NormalizerLean
