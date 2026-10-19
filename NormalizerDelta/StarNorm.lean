module

public import NormalizerDelta.StarConj

@[expose] public section

/-!
# Part 7, §N: the lower bound and the Atkin–Lehner criterion

* Elements of Γ_Δ(N) are [[a, b], [Nc, d]] with d mod N ∈ Δ and h* ∣ d − a (`exists_entries_of_mem_GammaDeltaR`).
* Conjugating by D*⁻¹ w D* (w Atkin–Lehner of level n* for Q ∥ n*) changes d into
  x₂₂ ≡ ι*_Q(d) mod N/h* (`StarConj.lean`), which gives the lower bound (Q = 1) and the criterion.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Congruences prime by prime -/

theorem cast_eq_cast_iff [NeZero N] {m : ℕ} (x y : ZMod N) :
    (ZMod.cast x : ZMod m) = ZMod.cast y ↔ (m : ℤ) ∣ (y.val : ℤ) - x.val := by
  rw [cast_val_eq, cast_val_eq, ← Int.cast_natCast, ← Int.cast_natCast (R := ZMod m),
    ZMod.intCast_eq_intCast_iff_dvd_sub]

theorem dvd_of_forall_primePow_dvd {L : ℕ} (hL : L ≠ 0) {z : ℤ}
    (h : ∀ p ∈ L.primeFactors, ((p ^ L.factorization p : ℕ) : ℤ) ∣ z) : (L : ℤ) ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero _
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hz
  rw [Int.natCast_dvd, ← Nat.factorization_prime_le_iff_dvd hL hz']
  intro p hp
  by_cases hpL : p ∣ L
  · have := h p (Nat.mem_primeFactors.2 ⟨hp, hpL, hL⟩)
    rw [Int.natCast_dvd] at this
    exact (hp.pow_dvd_iff_le_factorization hz').1 this
  · rw [Nat.factorization_eq_zero_of_not_dvd hpL]; exact Nat.zero_le _

theorem cast_eq_of_forall_primePow [NeZero N] {L : ℕ} (hL : L ≠ 0) {x y : ZMod N}
    (h : ∀ p ∈ L.primeFactors, (ZMod.cast x : ZMod (p ^ L.factorization p)) = ZMod.cast y) :
    (ZMod.cast x : ZMod L) = ZMod.cast y := by
  rw [cast_eq_cast_iff]
  exact dvd_of_forall_primePow_dvd hL fun p hp => (cast_eq_cast_iff x y).1 (h p hp)

theorem primePow_dvd {L : ℕ} (p : ℕ) : p ^ L.factorization p ∣ L := Nat.ordProj_dvd L p

/-- A prime power p^k with p ∤ Q is coprime to Q. -/
theorem coprime_primePow {p k Q : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) : Nat.Coprime (p ^ k) Q :=
  Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQ)

/-! ### Casts of integers -/

theorem cast_intCast [NeZero N] {m : ℕ} (hm : m ∣ N) (z : ℤ) :
    (ZMod.cast (z : ZMod N) : ZMod m) = (z : ZMod m) := by
  rw [← ZMod.castHom_apply (h := hm), map_intCast]

/-! ### A unit congruent to an element of Δ modulo N/h* -/

theorem exists_mem_of_dvd_sub [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {u : (ZMod N)ˣ} (hu : u ∈ Δ)
    {e : ℤ} (he : ((N / hStar N Δ : ℕ) : ℤ) ∣ e - (u : ZMod N).val) : ∃ v ∈ Δ, (v : ZMod N) = e := by
  set K := N / hStar N Δ
  obtain ⟨j, hj⟩ := he
  have hK2 : ((K : ℕ) : ZMod N) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact dvd_div_sq (hStar_pos N Δ) (hStar_sq_dvd N Δ)
  set x : ZMod N := (K : ZMod N) * j
  have hex : (e : ZMod N) = u + x := by
    have : (e : ZMod N) - ((u : ZMod N).val : ℤ) = (K : ZMod N) * j := by
      rw [← Int.cast_sub, hj]; push_cast; ring
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at this
    simp only [x]; linear_combination this
  set y : ZMod N := (u⁻¹ : (ZMod N)ˣ) * x
  have hy2 : y * y = 0 := by
    have : x * x = 0 := by
      simp only [x]
      linear_combination ((j : ZMod N) ^ 2) * hK2
    simp only [y]
    linear_combination ((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ 2 * this
  have hu1 : (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hey : (e : ZMod N) = u * (1 + y) := by
    rw [hex]; simp only [y]; linear_combination (-x) * hu1
  let v : (ZMod N)ˣ := ⟨e, (1 - y) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), by
      rw [hey]; linear_combination (1 - y * y) * hu1 - hy2, by
      rw [hey]; linear_combination (1 - y * y) * hu1 - hy2⟩
  refine ⟨v, (mem_iff_of_cast_eq ?_).1 hu, rfl⟩
  have hKN : K ∣ N := Nat.div_dvd_of_dvd (hStar_dvd N Δ)
  show (ZMod.cast (u : ZMod N) : ZMod K) = ZMod.cast (e : ZMod N)
  rw [hex, ← ZMod.castHom_apply (h := hKN), ← ZMod.castHom_apply (h := hKN), map_add]
  have : ZMod.castHom hKN (ZMod K) x = 0 := by
    simp only [x, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  rw [this, add_zero]

/-! ### Entries of elements of Γ_Δ(N) -/

theorem exists_entries_of_mem_GammaDeltaR [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {γ : SL(2, ℝ)}
    (hγ : γ ∈ GammaDeltaR N Δ) :
    ∃ a b c d : ℤ, ∃ u ∈ Δ, (u : ZMod N) = d ∧ a * d - b * (N * c) = 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (N : ℝ) * c, d] ∧ (hStar N Δ : ℤ) ∣ d - a := by
  obtain ⟨γ', ⟨h0, u, hu, hud⟩, rfl⟩ := mem_toR.1 hγ
  have hc : (N : ℤ) ∣ γ' 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 h0)
  obtain ⟨c, hcN⟩ := hc
  have hdet : γ' 0 0 * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by have := γ'.2; rwa [det_fin_two] at this
  refine ⟨γ' 0 0, γ' 0 1, c, γ' 1 1, u, hu, hud, by rw [← hcN]; exact hdet, ?_, ?_⟩
  · rw [coe_ofZ, hcN]; push_cast; rfl
  · have hN : (hStar N Δ : ℤ) ∣ N := Int.natCast_dvd_natCast.2 (hStar_dvd N Δ)
    set v : ℤ := ((u : ZMod N).val : ℤ)
    have hv : (N : ℤ) ∣ γ' 1 1 - v := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hud
    have h1 : (hStar N Δ : ℤ) ∣ γ' 1 1 ^ 2 - 1 := by
      have := hStar_dvd_sq_sub_one hu
      obtain ⟨k, hk⟩ := hN.trans hv
      have e : γ' 1 1 ^ 2 - 1 = (γ' 1 1 - v) * (γ' 1 1 + v) + (v ^ 2 - 1) := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_left (hN.trans hv) _) this
    have e : γ' 1 1 - γ' 0 0 = γ' 0 0 * (γ' 1 1 ^ 2 - 1) - γ' 1 1 * (γ' 0 0 * γ' 1 1 - 1) := by ring
    rw [e]
    refine dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right ?_ _)
    have : γ' 0 0 * γ' 1 1 - 1 = γ' 0 1 * γ' 1 0 := by linear_combination hdet
    rw [this, hcN]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hN _) _

theorem mem_GammaDeltaR_of_entries [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Y : SL(2, ℝ)} {a b c d : ℤ}
    (hdet : a * d - b * (N * c) = 1) (hY : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (N : ℝ) * c, d])
    {u : (ZMod N)ˣ} (hu : u ∈ Δ) (hud : (u : ZMod N) = d) : Y ∈ GammaDeltaR N Δ := by
  refine mem_toR.2 ⟨mkSL a b (N * c) d hdet, mkSL_mem_GammaDelta hdet (dvd_mul_right _ _) hu hud, ?_⟩
  apply Subtype.ext
  rw [coe_ofZ_mkSL, hY]
  push_cast
  rfl

theorem exists_mem_of_mem_GammaDeltaR [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Y : SL(2, ℝ)} {a b c d : ℤ}
    (hY : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d]) (hmem : Y ∈ GammaDeltaR N Δ) :
    ∃ u ∈ Δ, (u : ZMod N) = d := by
  obtain ⟨γ', ⟨-, u, hu, hud⟩, rfl⟩ := mem_toR.1 hmem
  refine ⟨u, hu, ?_⟩
  rw [hud]
  have := congrFun (congrFun hY 1) 1
  rw [coe_ofZ] at this
  simp at this
  exact_mod_cast congrArg (fun z : ℤ => (z : ZMod N)) this

/-- Every unit mod N is the lower right entry of an element of Γ₀(N). -/
theorem exists_Gamma0R_entries [NeZero N] (u : (ZMod N)ˣ) :
    ∃ a b c d : ℤ, a * d - b * (N * c) = 1 ∧ (u : ZMod N) = d := by
  obtain ⟨γ, hγ⟩ := unitMap_surjective (N := N) u
  have hc : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 γ.2)
  obtain ⟨c, hcN⟩ := hc
  refine ⟨(γ : SL(2, ℤ)) 0 0, (γ : SL(2, ℤ)) 0 1, c, (γ : SL(2, ℤ)) 1 1, ?_, ?_⟩
  · have := (γ : SL(2, ℤ)).2; rw [det_fin_two, hcN] at this; exact this
  · rw [← hγ, coe_unitMap]

/-! ### Atkin–Lehner elements in the form of `StarConj.lean` -/

theorem al_entries {n Q : ℕ} [NeZero n] (hQ : Q ∣ n) {w : SL(2, ℝ)} (hw : IsAtkinLehner n Q w) :
    ∃ m : ℕ, ∃ A B C D' : ℤ, n = Q * m ∧ (Q : ℤ) * A * D' - m * B * C = 1 ∧
      (w : Matrix (Fin 2) (Fin 2) ℝ) =
        (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * A, B; (Q : ℝ) * m * C, (Q : ℝ) * D'] := by
  obtain ⟨x, y, z, w', hdet, hwm⟩ := hw
  obtain ⟨m, rfl⟩ := hQ
  have hQ0 : (Q : ℤ) ≠ 0 := by
    have := NeZero.ne (Q * m); intro h; apply this; simp at h; simp [h]
  refine ⟨m, x, y, z, w', rfl, ?_, ?_⟩
  · apply mul_left_cancel₀ hQ0; push_cast at hdet; linear_combination hdet
  · rw [hwm]; push_cast; ring_nf

theorem Q_pos_of_dvd {n Q : ℕ} [NeZero n] (hQ : Q ∣ n) : 0 < Q :=
  Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne n))

/-! ### h* ∣ d − a -/

theorem hStar_dvd_sub [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {u : (ZMod N)ˣ} (hu : u ∈ Δ) {a b c d : ℤ}
    (hdet : a * d - b * (N * c) = 1) (hud : (u : ZMod N) = d) : (hStar N Δ : ℤ) ∣ d - a := by
  have hN : (hStar N Δ : ℤ) ∣ N := Int.natCast_dvd_natCast.2 (hStar_dvd N Δ)
  set v : ℤ := ((u : ZMod N).val : ℤ)
  have hv : (N : ℤ) ∣ d - v := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hud
  have h1 : (hStar N Δ : ℤ) ∣ d ^ 2 - 1 := by
    have e : d ^ 2 - 1 = (d - v) * (d + v) + (v ^ 2 - 1) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left (hN.trans hv) _) (hStar_dvd_sq_sub_one hu)
  have e : d - a = a * (d ^ 2 - 1) - d * (b * (N * c)) := by linear_combination (-d) * hdet
  rw [e]
  exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_left hN _) _) _)

/-! ### ι*_Q -/

theorem isIotaStar_symm [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Q : ℕ} {d u : (ZMod N)ˣ}
    (h : IsIotaStar N Δ Q d u) : IsIotaStar N Δ Q u d := by
  intro p hp
  have := h p hp
  split_ifs at this ⊢ with hpQ
  · rw [mul_comm]; exact this
  · exact this.symm

theorem cast_eq_of_isIotaStar [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Q : ℕ} {d u v : (ZMod N)ˣ}
    (hu : IsIotaStar N Δ Q d u) (hv : IsIotaStar N Δ Q d v) :
    (ZMod.cast (u : ZMod N) : ZMod (N / hStar N Δ)) = ZMod.cast (v : ZMod N) := by
  have hL : N / hStar N Δ ≠ 0 := by
    rw [div_hStar]; exact mul_ne_zero (NeZero.ne _) (hStar_pos N Δ).ne'
  apply cast_eq_of_forall_primePow hL
  intro p hp
  have h1 := hu p hp
  have h2 := hv p hp
  split_ifs at h1 h2 with hpQ
  · -- u d = 1 and v d = 1, so u = v
    linear_combination (ZMod.cast (v : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p)) * h1 -
      (ZMod.cast (u : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p)) * h2
  · rw [h1, h2]

theorem isIotaStable_one' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : IsIotaStable N Δ 1 := by
  have hne : ∀ p ∈ (N / hStar N Δ).primeFactors, ¬ p ∣ 1 := fun p hp h =>
    (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.1 h)
  intro u
  constructor
  · intro hu
    refine ⟨u, hu, fun p hp => ?_⟩
    rw [if_neg (hne p hp)]
  · rintro ⟨d, hd, hdu⟩
    have hrefl : IsIotaStar N Δ 1 d d := fun p hp => by rw [if_neg (hne p hp)]
    exact (mem_iff_of_cast_eq (cast_eq_of_isIotaStar hdu hrefl)).2 hd

/-! ### The conjugation by D*⁻¹ w D* -/

theorem coprime_nStar_div [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Q m : ℕ} (hnm : nStar N Δ = Q * m)
    (hQc : Nat.Coprime Q (nStar N Δ / Q)) (hQ : 0 < Q) : Nat.Coprime Q m := by
  rwa [hnm, Nat.mul_div_cancel_left _ hQ] at hQc

/-- The key computation: for w Atkin–Lehner of level n* for Q ∥ n* and γ = [[a, b], [Nc, d]] ∈ Γ₀(N) with
h* ∣ d − a and d ≡ u, the element D*⁻¹wD* γ (D*⁻¹wD*)⁻¹ lies in Γ₀(N), its lower right entry is a unit v with
v ≡ ι*_Q(u), and it lies in Γ_Δ(N) iff v ∈ Δ. -/
theorem conj_star_mem_iff [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Q : ℕ} (hQ : Q ∣ nStar N Δ)
    (hQc : Nat.Coprime Q (nStar N Δ / Q)) {w : SL(2, ℝ)} (hw : IsAtkinLehner (nStar N Δ) Q w)
    {γ : SL(2, ℝ)} {a b c d : ℤ} {u : (ZMod N)ˣ} (hud : (u : ZMod N) = d)
    (hdet : a * d - b * (N * c) = 1) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (N : ℝ) * c, d])
    (ht : (hStar N Δ : ℤ) ∣ d - a) :
    ∃ v : (ZMod N)ˣ, IsIotaStar N Δ Q u v ∧
      (MulAut.conj (Dstar N Δ)⁻¹ w * γ * (MulAut.conj (Dstar N Δ)⁻¹ w)⁻¹ ∈ GammaDeltaR N Δ ↔ v ∈ Δ) := by
  obtain ⟨m, A, B, C, D', hnm, hdetw, hwm⟩ := al_entries hQ hw
  obtain ⟨t, ht'⟩ := ht
  have hQ0 : 0 < Q := Q_pos_of_dvd hQ
  have hcop : Nat.Coprime Q m := coprime_nStar_div hnm hQc hQ0
  set h := hStar N Δ with hhdef
  have hh := hStar_pos N Δ
  have hNnat : N = Q * m * h ^ 2 := by rw [← nStar_mul N Δ, hnm]
  have hNR : (N : ℝ) = (Q : ℝ) * m * h ^ 2 := by exact_mod_cast hNnat
  have hNZ : (N : ℤ) = Q * m * h ^ 2 := by exact_mod_cast hNnat
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (Q : ℝ) * m * h ^ 2 * c, d] := by
    rw [hγ, hNR]
  have key := coe_conj_al_mul_conj hh hQ0 hdetw hwm hγ' ht'
  set x11 : ℤ := Q * A * D' * a + h * Q * m * B * D' * c - h * Q * m * A * C * b - m * B * C * d
  set x12 : ℤ := A * B * t + Q * A ^ 2 * b - m * B ^ 2 * c
  set x21 : ℤ := -(C * D' * t) + Q * D' ^ 2 * c - m * C ^ 2 * b
  set x22 : ℤ := d + h * (m * B * C * t + Q * m * (A * C * b - B * D' * c))
  set Y := MulAut.conj (Dstar N Δ)⁻¹ w * γ * (MulAut.conj (Dstar N Δ)⁻¹ w)⁻¹
  have hY : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![(x11 : ℝ), x12; (N : ℝ) * x21, x22] := by
    rw [hNR]; exact key
  have hdetY : x11 * x22 - x12 * (N * x21) = 1 := by
    have h1 := Y.2
    rw [hY, det_fin_two_of] at h1
    exact_mod_cast h1
  let v : (ZMod N)ˣ := Units.mkOfMulEqOne (x22 : ZMod N) (x11 : ZMod N) (by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdetY
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this)
  have hv : (v : ZMod N) = x22 := rfl
  refine ⟨v, ?_, ⟨fun hmem => ?_, fun hvΔ => mem_GammaDeltaR_of_entries hdetY hY hvΔ hv⟩⟩
  · intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    set q := p ^ (N / h).factorization p
    have hqL : q ∣ N / h := primePow_dvd p
    have hLN : N / h ∣ N := Nat.div_dvd_of_dvd (hStar_dvd N Δ)
    have hqN : q ∣ N := hqL.trans hLN
    have hL : N / h = Q * (m * h) := by rw [div_hStar, hnm]; ring
    rw [hv, cast_intCast hqN, hud, cast_intCast hqN]
    split_ifs with hpQ
    · -- q ∣ h Q, and x₂₂ = a + hQ(·), a d ≡ 1
      have hqm : Nat.Coprime q m :=
        coprime_primePow hpr (fun hpm => (Nat.Prime.coprime_iff_not_dvd hpr).1
          (Nat.Coprime.coprime_dvd_left hpQ hcop) hpm)
      have hqQh : q ∣ Q * h := by
        rw [hL, show Q * (m * h) = m * (Q * h) by ring] at hqL
        exact hqm.dvd_of_dvd_mul_left hqL
      have e : x22 * d - 1 = (Q * h : ℕ) * ((t * A * D' + m * (A * C * b - B * D' * c)) * d) +
          b * (N * c) := by
        simp only [x22]; push_cast
        linear_combination (-((h : ℤ) * t * d)) * hdetw + hdet + d * ht'
      have hdvd : (q : ℤ) ∣ x22 * d - 1 := by
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hqQh) _)
          (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hqN) _) _)
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hdvd
      push_cast at this
      linear_combination this
    · have hqQ : Nat.Coprime q Q := coprime_primePow hpr hpQ
      have hqmh : q ∣ m * h := by rw [hL] at hqL; exact hqQ.dvd_of_dvd_mul_left hqL
      have e : x22 - d = (m * h : ℕ) * (B * C * t + Q * (A * C * b - B * D' * c)) := by
        simp only [x22]; push_cast; ring
      have hdvd : (q : ℤ) ∣ x22 - d := by
        rw [e]; exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hqmh) _
      rw [(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 hdvd]
  · have hY' : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![(x11 : ℝ), x12; ((N * x21 : ℤ) : ℝ), x22] := by
      rw [hY]; push_cast; rfl
    obtain ⟨v', hv'Δ, hv'⟩ := exists_mem_of_mem_GammaDeltaR hY' hmem
    have : v' = v := Units.ext (by rw [hv', hv])
    rwa [← this]

/-- g ∈ Nor(Γ) iff g Γ g⁻¹ ⊆ Γ and g⁻¹ Γ g ⊆ Γ. -/
theorem mem_normG_of_conj {Γ : Subgroup SL(2, ℝ)} {g : SL(2, ℝ)} (h1 : ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ Γ)
    (h2 : ∀ γ ∈ Γ, g⁻¹ * γ * g⁻¹⁻¹ ∈ Γ) : g ∈ NormG Γ := by
  rw [Subgroup.mem_normalizer_iff]
  intro γ
  refine ⟨h1 γ, fun hγ => ?_⟩
  have := h2 _ hγ
  simpa [mul_assoc] using this

theorem conj_star_inv {N : ℕ} {Δ : Subgroup (ZMod N)ˣ} (w : SL(2, ℝ)) :
    (MulAut.conj (Dstar N Δ)⁻¹ w)⁻¹ = MulAut.conj (Dstar N Δ)⁻¹ w⁻¹ := (map_inv _ w).symm

/-- The criterion, direction ⇐, as an inclusion. -/
theorem conj_star_le_of_stable [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {Q : ℕ} (hQ : Q ∣ nStar N Δ)
    (hQc : Nat.Coprime Q (nStar N Δ / Q)) (hst : IsIotaStable N Δ Q) {w : SL(2, ℝ)}
    (hw : IsAtkinLehner (nStar N Δ) Q w) {γ : SL(2, ℝ)} (hγ : γ ∈ GammaDeltaR N Δ) :
    MulAut.conj (Dstar N Δ)⁻¹ w * γ * (MulAut.conj (Dstar N Δ)⁻¹ w)⁻¹ ∈ GammaDeltaR N Δ := by
  obtain ⟨a, b, c, d, u, hu, hud, hdet, hγm, ht⟩ := exists_entries_of_mem_GammaDeltaR hγ
  obtain ⟨v, hiv, hiff⟩ := conj_star_mem_iff hQ hQc hw hud hdet hγm ht
  exact hiff.2 ((hst v).2 ⟨u, hu, hiv⟩)

theorem conj_mem_normG_iff' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {Q : ℕ} (hQ : Q ∣ nStar N Δ)
    (hQc : Nat.Coprime Q (nStar N Δ / Q)) {w : SL(2, ℝ)} (hw : IsAtkinLehner (nStar N Δ) Q w) :
    (Dstar N Δ)⁻¹ * w * Dstar N Δ ∈ NormG (GammaDeltaR N Δ) ↔ IsIotaStable N Δ Q := by
  have hg : (Dstar N Δ)⁻¹ * w * Dstar N Δ = MulAut.conj (Dstar N Δ)⁻¹ w := by
    rw [MulAut.conj_apply, inv_inv]
  rw [hg]
  have hwi : IsAtkinLehner (nStar N Δ) Q w⁻¹ := isAtkinLehner_inv hw
  constructor
  · intro hN u
    have hNi := inv_mem hN
    -- a matrix of Γ₀(N) with lower right entry ≡ x
    have lift : ∀ x : (ZMod N)ˣ, x ∈ Δ → ∃ γ : SL(2, ℝ), ∃ a b c d : ℤ, (x : ZMod N) = d ∧
        a * d - b * (N * c) = 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; (N : ℝ) * c, d] ∧
        (hStar N Δ : ℤ) ∣ d - a ∧ γ ∈ GammaDeltaR N Δ := by
      intro x hx
      obtain ⟨a, b, c, d, hdet, hxd⟩ := exists_Gamma0R_entries x
      let γ : SL(2, ℝ) := ⟨!![(a : ℝ), b; (N : ℝ) * c, d], by
        rw [det_fin_two_of]; exact_mod_cast hdet⟩
      exact ⟨γ, a, b, c, d, hxd, hdet, rfl, hStar_dvd_sub hx hdet hxd,
        mem_GammaDeltaR_of_entries hdet rfl hx hxd⟩
    constructor
    · intro hu
      obtain ⟨γ, a, b, c, d, hud, hdet, hγm, ht, hγ⟩ := lift u hu
      obtain ⟨v, hiv, hiff⟩ := conj_star_mem_iff hQ hQc hwi hud hdet hγm ht
      have hmem : MulAut.conj (Dstar N Δ)⁻¹ w⁻¹ * γ * (MulAut.conj (Dstar N Δ)⁻¹ w⁻¹)⁻¹ ∈
          GammaDeltaR N Δ := by
        rw [← conj_star_inv]
        exact (Subgroup.mem_normalizer_iff.1 hNi γ).1 hγ
      exact ⟨v, hiff.1 hmem, isIotaStar_symm hiv⟩
    · rintro ⟨d', hd', hdu⟩
      obtain ⟨γ, a, b, c, d, hud, hdet, hγm, ht, hγ⟩ := lift d' hd'
      obtain ⟨v, hiv, hiff⟩ := conj_star_mem_iff hQ hQc hw hud hdet hγm ht
      have hvΔ := hiff.1 ((Subgroup.mem_normalizer_iff.1 hN γ).1 hγ)
      exact (mem_iff_of_cast_eq (cast_eq_of_isIotaStar hdu hiv)).2 hvΔ
  · intro hst
    refine mem_normG_of_conj (fun γ hγ => conj_star_le_of_stable hQ hQc hst hw hγ) (fun γ hγ => ?_)
    rw [conj_star_inv]
    exact conj_star_le_of_stable hQ hQc hst hwi hγ

/-! ### The lower bound -/

theorem Gamma0Star_le_normG' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0Star N Δ ≤ NormG (GammaDeltaR N Δ) := by
  rintro _ ⟨w, hw, rfl⟩
  have h1 : IsAtkinLehner (nStar N Δ) 1 w := (isAtkinLehner_one_iff' _ w).2 hw
  have := (conj_mem_normG_iff' Δ (one_dvd _) (Nat.coprime_one_left _) h1).2 (isIotaStable_one' N Δ)
  simpa [MulAut.conj_apply] using this

end

end NormalizerLean
