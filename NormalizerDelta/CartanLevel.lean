module

public import NormalizerDelta.XNGLQ
public import NormalizerDelta.DefsCartan

@[expose] public section

/-!
# §L: normalizers of groups of level N (DLM26, Prop. 4.3(2) and Prop. 4.5(1))

Let Γ(N) ≤ Γ ≤ SL₂(ℤ) and g = [[x, y], [z, w]] ∈ Nor_{SL₂(ℝ)}(Γ).
* Conjugating [[1, N], [0, 1]], [[1, 0], [N, 1]] and their product into Γ ⊆ SL₂(ℤ): N x², N xz, N z², N y², N yw,
  N w² ∈ ℤ and N² xw, N² xy, N² zw, N² yz ∈ ℤ.  So N²e·g is integral for a non-zero entry e, and g = κ·m with m
  primitive integral (`exists_prim_of_int_multiple`).
* det g = 1 gives κ² det m = 1, and N x² ∈ ℤ etc. give det m ∣ N m_ij² for all i, j, hence det m ∣ N (the squares of
  a primitive matrix have gcd 1).  The sign of κ is absorbed in m.
* If p ∣ det m, the columns of m span a Γ-stable lattice which is a line mod p (`invariant_line_of_dvd_det`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- No prime divides all the entries. -/
def IsPrimM (m : Matrix (Fin 2) (Fin 2) ℤ) : Prop := ∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ m i j

theorem isIntR_of_mem_toR {Γ : Subgroup SL(2, ℤ)} {Y : SL(2, ℝ)} (hY : Y ∈ toR Γ) (i j : Fin 2) :
    IsIntR ((Y : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain ⟨γ, -, rfl⟩ := hY
  exact ⟨γ i j, by simp [Matrix.SpecialLinearGroup.map_apply_coe]⟩

/-! ### Rationality -/

/-- Four reals with an integral non-zero common multiple are a real multiple of four integers without a common prime
factor. -/
theorem exists_prim_of_int_multiple {x y z w κ' : ℝ} (hκ' : κ' ≠ 0) (h00 : IsIntR (κ' * x))
    (h01 : IsIntR (κ' * y)) (h10 : IsIntR (κ' * z)) (h11 : IsIntR (κ' * w))
    (h0 : ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0)) :
    ∃ (κ : ℝ) (m : Matrix (Fin 2) (Fin 2) ℤ), κ ≠ 0 ∧ IsPrimM m ∧
      x = κ * m 0 0 ∧ y = κ * m 0 1 ∧ z = κ * m 1 0 ∧ w = κ * m 1 1 := by
  obtain ⟨n00, e00⟩ := h00
  obtain ⟨n01, e01⟩ := h01
  obtain ⟨n10, e10⟩ := h10
  obtain ⟨n11, e11⟩ := h11
  set c : ℕ := Nat.gcd (Int.gcd n00 n01) (Int.gcd n10 n11) with hc
  have d00 : (c : ℤ) ∣ n00 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_left _ _)
  have d01 : (c : ℤ) ∣ n01 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_right _ _)
  have d10 : (c : ℤ) ∣ n10 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans (Int.gcd_dvd_left _ _)
  have d11 : (c : ℤ) ∣ n11 :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans (Int.gcd_dvd_right _ _)
  have hc0 : c ≠ 0 := by
    intro hc00
    rw [hc00, Nat.cast_zero, zero_dvd_iff] at d00 d01 d10 d11
    apply h0
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := e00; rw [d00, Int.cast_zero] at this; exact (mul_eq_zero.1 this).resolve_left hκ'
    · have := e01; rw [d01, Int.cast_zero] at this; exact (mul_eq_zero.1 this).resolve_left hκ'
    · have := e10; rw [d10, Int.cast_zero] at this; exact (mul_eq_zero.1 this).resolve_left hκ'
    · have := e11; rw [d11, Int.cast_zero] at this; exact (mul_eq_zero.1 this).resolve_left hκ'
  obtain ⟨a, ha⟩ := d00
  obtain ⟨b, hb⟩ := d01
  obtain ⟨cc, hcc⟩ := d10
  obtain ⟨d, hd⟩ := d11
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨c / κ', !![a, b; cc, d], div_ne_zero hcr hκ', ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_contra h
    push_neg at h
    have hpa := h 0 0
    have hpb := h 0 1
    have hpc := h 1 0
    have hpd := h 1 1
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      head_cons] at hpa hpb hpc hpd
    have hpc' : ∀ {n e : ℤ}, n = c * e → (p : ℤ) ∣ e → ((p * c : ℕ) : ℤ) ∣ n := by
      rintro n e rfl ⟨k, rfl⟩
      exact ⟨k, by push_cast; ring⟩
    have h1 : p * c ∣ c := by
      rw [hc]
      exact Nat.dvd_gcd (Int.dvd_gcd (hpc' ha hpa) (hpc' hb hpb))
        (Int.dvd_gcd (hpc' hcc hpc) (hpc' hd hpd))
    have h2 : p * c ∣ 1 * c := by rwa [one_mul]
    have := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hc0) h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  all_goals simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    head_cons]
  · rw [ha] at e00; push_cast at e00; field_simp; linarith
  · rw [hb] at e01; push_cast at e01; field_simp; linarith
  · rw [hcc] at e10; push_cast at e10; field_simp; linarith
  · rw [hd] at e11; push_cast at e11; field_simp; linarith

/-! ### Bézout for the squares of a primitive matrix -/

theorem dvd_of_dvd_mul_sq {D N : ℤ} {m : Matrix (Fin 2) (Fin 2) ℤ} (hprim : IsPrimM m)
    (h : ∀ i j, D ∣ N * m i j ^ 2) : D ∣ N := by
  set s := Int.gcd (m 0 0 ^ 2) (m 0 1 ^ 2)
  set t := Int.gcd (m 1 0 ^ 2) (m 1 1 ^ 2)
  have hG : Nat.gcd s t = 1 := by
    by_contra hG
    obtain ⟨p, hp, hpG⟩ := Nat.exists_prime_and_dvd hG
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hps : (p : ℤ) ∣ s := Int.natCast_dvd_natCast.2 (hpG.trans (Nat.gcd_dvd_left _ _))
    have hpt : (p : ℤ) ∣ t := Int.natCast_dvd_natCast.2 (hpG.trans (Nat.gcd_dvd_right _ _))
    obtain ⟨i, j, hij⟩ := hprim p hp
    apply hij
    fin_cases i <;> fin_cases j
    · exact hpZ.dvd_of_dvd_pow (hps.trans (Int.gcd_dvd_left _ _))
    · exact hpZ.dvd_of_dvd_pow (hps.trans (Int.gcd_dvd_right _ _))
    · exact hpZ.dvd_of_dvd_pow (hpt.trans (Int.gcd_dvd_left _ _))
    · exact hpZ.dvd_of_dvd_pow (hpt.trans (Int.gcd_dvd_right _ _))
  have e1 := Int.gcd_eq_gcd_ab (m 0 0 ^ 2) (m 0 1 ^ 2)
  have e2 := Int.gcd_eq_gcd_ab (m 1 0 ^ 2) (m 1 1 ^ 2)
  have e3 := Nat.gcd_eq_gcd_ab s t
  rw [hG] at e3
  have key : N = (N * m 0 0 ^ 2) * (Int.gcdA (m 0 0 ^ 2) (m 0 1 ^ 2) * Nat.gcdA s t) +
      (N * m 0 1 ^ 2) * (Int.gcdB (m 0 0 ^ 2) (m 0 1 ^ 2) * Nat.gcdA s t) +
      (N * m 1 0 ^ 2) * (Int.gcdA (m 1 0 ^ 2) (m 1 1 ^ 2) * Nat.gcdB s t) +
      (N * m 1 1 ^ 2) * (Int.gcdB (m 1 0 ^ 2) (m 1 1 ^ 2) * Nat.gcdB s t) := by
    have : (1 : ℤ) = (s : ℤ) * Nat.gcdA s t + (t : ℤ) * Nat.gcdB s t := by exact_mod_cast e3
    rw [e1, e2] at this
    linear_combination N * this
  rw [key]
  exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_left (h 0 0) _) (dvd_mul_of_dvd_left (h 0 1) _))
    (dvd_mul_of_dvd_left (h 1 0) _)) (dvd_mul_of_dvd_left (h 1 1) _)

/-! ### The form of the normalizer -/

/-- [[1, N], [0, 1]] and [[1, 0], [N, 1]]. -/
def tN (N : ℕ) : SL(2, ℤ) := mkSL 1 N 0 1 (by ring)
def uN (N : ℕ) : SL(2, ℤ) := mkSL 1 0 N 1 (by ring)

theorem tN_mem (N : ℕ) : tN N ∈ CongruenceSubgroup.Gamma N :=
  CongruenceSubgroup.Gamma_mem.2 ⟨by simp [tN, mkSL], by simp [tN, mkSL], by simp [tN, mkSL],
    by simp [tN, mkSL]⟩

theorem uN_mem (N : ℕ) : uN N ∈ CongruenceSubgroup.Gamma N :=
  CongruenceSubgroup.Gamma_mem.2 ⟨by simp [uN, mkSL], by simp [uN, mkSL], by simp [uN, mkSL],
    by simp [uN, mkSL]⟩

/-- [[1 + N², N], [N, 1]] = [[1, N], [0, 1]]·[[1, 0], [N, 1]]. -/
def vN (N : ℕ) : SL(2, ℤ) := mkSL (1 + N * N) N N 1 (by ring)

theorem vN_mem (N : ℕ) : vN N ∈ CongruenceSubgroup.Gamma N :=
  CongruenceSubgroup.Gamma_mem.2 ⟨by simp [vN, mkSL], by simp [vN, mkSL], by simp [vN, mkSL],
    by simp [vN, mkSL]⟩

theorem normG_level_form' {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) {g : SL(2, ℝ)} (hg : g ∈ NormG (toR Γ)) :
    ∃ m : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det ∧ m.det ∣ N ∧
      (∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ m i j) ∧
      g = projSL (m.map (Int.cast : ℤ → ℝ)) := by
  have hconj : ∀ γ ∈ Γ, IsIntR (((g * ofZ γ * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ∧
      IsIntR (((g * ofZ γ * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ∧
      IsIntR (((g * ofZ γ * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ∧
      IsIntR (((g * ofZ γ * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
    intro γ hγ
    have h := (Subgroup.mem_normalizer_iff.1 hg (ofZ γ)).1 (ofZ_mem_toR hγ)
    exact ⟨isIntR_of_mem_toR h 0 0, isIntR_of_mem_toR h 0 1, isIntR_of_mem_toR h 1 0,
      isIntR_of_mem_toR h 1 1⟩
  set x := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with hx
  set y := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hy
  set z := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hz
  set w := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hw
  have hdet : x * w - y * z = 1 := by
    have := g.2; rw [det_fin_two] at this; exact this
  have hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![x, y; z, w] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hginv : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![w, -y; -z, x] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hgm, adjugate_fin_two_of]
  have conjE : ∀ γ : SL(2, ℤ), ∀ i j, ((g * ofZ γ * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (!![x, y; z, w] * !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] * !![w, -y; -z, x]) i j := by
    intro γ i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hgm, hginv, coe_ofZ]
  obtain ⟨t00, t01, t10, t11⟩ := hconj _ (hΓ (tN_mem N))
  obtain ⟨u00, u01, u10, u11⟩ := hconj _ (hΓ (uN_mem N))
  obtain ⟨v00, v01, v10, v11⟩ := hconj _ (hΓ (vN_mem N))
  rw [conjE] at t00 t01 t10 t11 u00 u01 u10 u11 v00 v01 v10 v11
  simp [tN, uN, mkSL, Matrix.mul_apply, Fin.sum_univ_two] at t00 t01 t10 t11 u00 u01 u10 u11
  simp [vN, mkSL, Matrix.mul_apply, Fin.sum_univ_two] at v00 v01 v10 v11
  -- the products
  have F1 : IsIntR (N * (x * x)) := by convert t01 using 1; ring
  have F2 : IsIntR (N * (x * z)) := by
    convert (IsIntR.one.sub t00) using 1; linear_combination hdet
  have F3 : IsIntR (N * (z * z)) := by convert t10.neg using 1; ring
  have F4 : IsIntR (N * (y * y)) := by convert u01.neg using 1; ring
  have F5 : IsIntR (N * (y * w)) := by
    convert (u00.sub IsIntR.one) using 1; linear_combination (-1 : ℝ) * hdet
  have F6 : IsIntR (N * (w * w)) := by convert u10 using 1; ring
  have G1 : IsIntR ((N : ℝ) ^ 2 * (x * w)) := by
    convert ((v00.sub IsIntR.one).sub F5).add F2 using 1; linear_combination (-1 : ℝ) * hdet
  have G2 : IsIntR ((N : ℝ) ^ 2 * (x * y)) := by
    convert (F1.sub F4).sub v01 using 1; ring
  have G3 : IsIntR ((N : ℝ) ^ 2 * (z * w)) := by
    convert (v10.sub F6).add F3 using 1; ring
  have G4 : IsIntR ((N : ℝ) ^ 2 * (y * z)) := by
    convert ((IsIntR.one.sub v11).sub F5).add F2 using 1; linear_combination hdet
  have sq : ∀ {r : ℝ}, IsIntR (N * r) → IsIntR ((N : ℝ) ^ 2 * r) := fun h => by
    convert (IsIntR.nat N).mul h using 1; ring
  have h0 : ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) := by
    rintro ⟨h1, h2, h3, h4⟩
    rw [h1, h2, h3, h4] at hdet; norm_num at hdet
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN2 : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hN0
  -- an integral non-zero multiple of g: N² e g for a non-zero entry e
  have key : ∃ κ' : ℝ, κ' ≠ 0 ∧ IsIntR (κ' * x) ∧ IsIntR (κ' * y) ∧ IsIntR (κ' * z) ∧ IsIntR (κ' * w) := by
    by_cases hx0 : x ≠ 0
    · exact ⟨(N : ℝ) ^ 2 * x, mul_ne_zero hN2 hx0, by convert sq F1 using 1; ring,
        by convert G2 using 1; ring, by convert sq F2 using 1; ring, by convert G1 using 1; ring⟩
    by_cases hy0 : y ≠ 0
    · exact ⟨(N : ℝ) ^ 2 * y, mul_ne_zero hN2 hy0, by convert G2 using 1; ring,
        by convert sq F4 using 1; ring, by convert G4 using 1; ring, by convert sq F5 using 1; ring⟩
    by_cases hz0 : z ≠ 0
    · exact ⟨(N : ℝ) ^ 2 * z, mul_ne_zero hN2 hz0, by convert sq F2 using 1; ring,
        by convert G4 using 1; ring, by convert sq F3 using 1; ring, by convert G3 using 1; ring⟩
    by_cases hw0 : w ≠ 0
    · exact ⟨(N : ℝ) ^ 2 * w, mul_ne_zero hN2 hw0, by convert G1 using 1; ring,
        by convert sq F5 using 1; ring, by convert G3 using 1; ring, by convert sq F6 using 1; ring⟩
    push_neg at hx0 hy0 hz0 hw0
    exact absurd ⟨hx0, hy0, hz0, hw0⟩ h0
  obtain ⟨κ', hκ', i00, i01, i10, i11⟩ := key
  obtain ⟨κ, m, hκ0, hprim, ex, ey, ez, ew⟩ := exists_prim_of_int_multiple hκ' i00 i01 i10 i11 h0
  have hgκ : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • m.map (Int.cast : ℤ → ℝ) := by
    rw [hgm, ex, ey, ez, ew]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  -- κ² det m = 1
  have hdetm : κ ^ 2 * (m.det : ℝ) = 1 := by
    have h1 := g.2
    rw [hgκ, det_smul, Fintype.card_fin] at h1
    have h2 : (m.map (Int.cast : ℤ → ℝ)).det = (m.det : ℝ) := by
      have := RingHom.map_det (Int.castRingHom ℝ) m
      simpa using this.symm
    rw [h2] at h1
    exact h1
  have hDpos : 0 < m.det := by
    have : (0 : ℝ) < m.det := by
      by_contra h
      push_neg at h
      have : κ ^ 2 * (m.det : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) h
      linarith
    exact_mod_cast this
  -- det m ∣ N m_ij²
  have hdvd : ∀ {a : ℤ}, IsIntR (N * ((κ * a) * (κ * a))) → m.det ∣ N * a ^ 2 := by
    intro a h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [← hk]
    linear_combination (-(N : ℝ) * (a : ℝ) ^ 2) * hdetm
  have hDN : m.det ∣ N := by
    refine dvd_of_dvd_mul_sq hprim ?_
    simp only [Fin.forall_fin_two]
    exact ⟨⟨hdvd (by rw [← ex]; exact F1), hdvd (by rw [← ey]; exact F4)⟩,
      ⟨hdvd (by rw [← ez]; exact F3), hdvd (by rw [← ew]; exact F6)⟩⟩
  -- the sign
  have hDr : (0 : ℝ) < m.det := by exact_mod_cast hDpos
  have hs : Real.sqrt m.det ≠ 0 := (Real.sqrt_pos.2 hDr).ne'
  have habs : |κ| = (Real.sqrt m.det)⁻¹ := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_inv]
    congr 1
    field_simp
    linarith
  rcases lt_or_gt_of_ne hκ0 with hneg | hpos
  · refine ⟨-m, by rw [det_neg, Fintype.card_fin]; simpa using hDpos, by
      rw [det_neg, Fintype.card_fin]; simpa using hDN, fun p hp => ?_, ?_⟩
    · obtain ⟨i, j, hij⟩ := hprim p hp
      exact ⟨i, j, by simpa using hij⟩
    · apply Subtype.ext
      have hd' : ((-m).map (Int.cast : ℤ → ℝ)).det = (m.det : ℝ) := by
        have := RingHom.map_det (Int.castRingHom ℝ) (-m)
        rw [det_neg, Fintype.card_fin] at this
        simpa using this.symm
      rw [coe_projSL _ (by rw [hd']; exact hDr), hd', hgκ, abs_of_neg hneg] at *
      rw [← habs]
      ext i j; simp
  · refine ⟨m, hDpos, hDN, hprim, ?_⟩
    apply Subtype.ext
    have hd' : (m.map (Int.cast : ℤ → ℝ)).det = (m.det : ℝ) := by
      have := RingHom.map_det (Int.castRingHom ℝ) m
      simpa using this.symm
    rw [coe_projSL _ (by rw [hd']; exact hDr), hd', hgκ, ← habs, abs_of_pos hpos]

/-! ### The lattice argument -/

theorem exists_smul_of_det_zero {F : Type*} [Field F] {v w : Fin 2 → F} (hv : v ≠ 0)
    (h : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : F, w = c • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; ext i; fin_cases i
      · exact h0
      · exact h1
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_left h1
    refine ⟨w 1 / v 1, ?_⟩
    ext i; fin_cases i
    · simp [hw0, h0]
    · simp; field_simp
  · refine ⟨w 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp; field_simp
    · simp; field_simp; linear_combination h

/-- DLM26, Prop. 4.5(1), k = 1: if m is primitive and p ∣ det m, there is a line F_p v in F_p² with
γ̄ v ∈ F_p v whenever γ m = m γ' for integral γ, γ'. -/
theorem invariant_line_of_dvd_det {p : ℕ} [Fact p.Prime] {m : Matrix (Fin 2) (Fin 2) ℤ}
    (hprim : IsPrimM m) (hdet : (p : ℤ) ∣ m.det) :
    ∃ v : Fin 2 → ZMod p, v ≠ 0 ∧ ∀ γ γ' : Matrix (Fin 2) (Fin 2) ℤ, γ * m = m * γ' →
      ∃ c : ZMod p, (γ.map (Int.cast : ℤ → ZMod p)) *ᵥ v = c • v := by
  obtain ⟨i, j, hij⟩ := hprim p (Fact.out)
  have hij' : ((m i j : ℤ) : ZMod p) ≠ 0 := fun h => hij ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  have hdet' : ((m 0 0 : ℤ) : ZMod p) * (m 1 1 : ℤ) - (m 0 1 : ℤ) * (m 1 0 : ℤ) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdet
    rw [det_fin_two] at this; push_cast at this; exact this
  -- entries of γ m = m γ'
  have rel : ∀ γ γ' : Matrix (Fin 2) (Fin 2) ℤ, γ * m = m * γ' → ∀ r k,
      ((γ r 0 : ℤ) : ZMod p) * (m 0 k : ℤ) + (γ r 1 : ℤ) * (m 1 k : ℤ) =
        (m r 0 : ℤ) * (γ' 0 k : ℤ) + (m r 1 : ℤ) * (γ' 1 k : ℤ) := by
    intro γ γ' h r k
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => ((M r k : ℤ) : ZMod p)) h
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
    push_cast at this
    exact this
  fin_cases j
  · -- v = first column, w = second column
    set v : Fin 2 → ZMod p := fun r => ((m r 0 : ℤ) : ZMod p) with hvdef
    have hv : v ≠ 0 := fun h => hij' (by simpa using congrFun h i)
    obtain ⟨c₀, hc₀⟩ := exists_smul_of_det_zero (w := fun r => ((m r 1 : ℤ) : ZMod p)) hv
      (by simp only [hvdef]; linear_combination hdet')
    refine ⟨v, hv, fun γ γ' h => ⟨(γ' 0 0 : ZMod p) + c₀ * (γ' 1 0 : ZMod p), ?_⟩⟩
    ext r
    have e := rel γ γ' h r 0
    have hw := congrFun hc₀ r
    simp only [Pi.smul_apply, smul_eq_mul] at hw
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul, hvdef]
    rw [e, hw]; ring
  · set v : Fin 2 → ZMod p := fun r => ((m r 1 : ℤ) : ZMod p) with hvdef
    have hv : v ≠ 0 := fun h => hij' (by simpa using congrFun h i)
    obtain ⟨c₀, hc₀⟩ := exists_smul_of_det_zero (w := fun r => ((m r 0 : ℤ) : ZMod p)) hv
      (by simp only [hvdef]; linear_combination -hdet')
    refine ⟨v, hv, fun γ γ' h => ⟨c₀ * (γ' 0 1 : ZMod p) + (γ' 1 1 : ZMod p), ?_⟩⟩
    ext r
    have e := rel γ γ' h r 1
    have hw := congrFun hc₀ r
    simp only [Pi.smul_apply, smul_eq_mul] at hw
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Pi.smul_apply,
      smul_eq_mul, hvdef]
    rw [e, hw]; ring

theorem normG_level_le_SL2ZR' {N : ℕ} (hN0 : NeZero N) {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (hirr : ∀ p : ℕ, p.Prime → p ∣ N → ∀ v : Fin 2 → ZMod p, v ≠ 0 →
      ∃ γ ∈ Γ, ∀ c : ZMod p, (redSL p γ : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v ≠ c • v) :
    NormG (toR Γ) ≤ SL2ZR := by
  intro g hg
  obtain ⟨m, hD, hDN, hprim, rfl⟩ := normG_level_form' hΓ hg
  have hd' : (m.map (Int.cast : ℤ → ℝ)).det = (m.det : ℝ) := by
    have := RingHom.map_det (Int.castRingHom ℝ) m
    simpa using this.symm
  have hDr : (0 : ℝ) < m.det := by exact_mod_cast hD
  by_cases hD1 : m.det = 1
  · refine ⟨⟨m, hD1⟩, Subgroup.mem_top _, ?_⟩
    apply Subtype.ext
    rw [coe_projSL _ (by rw [hd']; exact hDr), hd', hD1, Int.cast_one, Real.sqrt_one, inv_one,
      one_smul]
    ext i j; rfl
  · exfalso
    have hD1' : m.det.natAbs ≠ 1 := by omega
    obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD1'
    have hpD' : (p : ℤ) ∣ m.det := Int.natCast_dvd.2 hpD
    have hpN : p ∣ N := Int.natCast_dvd_natCast.1 (hpD'.trans hDN)
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨v, hv, hinv⟩ := invariant_line_of_dvd_det hprim hpD'
    obtain ⟨γ, hγ, hno⟩ := hirr p hp hpN v hv
    set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hPdef
    have hmem : P⁻¹ * ofZ γ * P ∈ toR Γ := by
      apply ((Subgroup.mem_normalizer_iff.1 hg) (P⁻¹ * ofZ γ * P)).2
      rw [show P * (P⁻¹ * ofZ γ * P) * P⁻¹ = ofZ γ by group]
      exact ofZ_mem_toR hγ
    obtain ⟨γ', -, hγ'⟩ := hmem
    have hPm : (P : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt m.det)⁻¹ • m.map (Int.cast : ℤ → ℝ) := by
      rw [hPdef, coe_projSL _ (by rw [hd']; exact hDr), hd']
    have hs : (Real.sqrt m.det)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hDr).ne'
    have hrel : (γ : Matrix (Fin 2) (Fin 2) ℤ) * m = m * (γ' : Matrix (Fin 2) (Fin 2) ℤ) := by
      have h1 : P * ofZ γ' = ofZ γ * P := by
        have h1' := congrArg (fun X => P * X) hγ'
        rw [show P * (P⁻¹ * ofZ γ * P) = ofZ γ * P by group] at h1'
        exact h1'
      have h2 := congrArg (fun X : SL(2, ℝ) => (X : Matrix (Fin 2) (Fin 2) ℝ)) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, hPm, Matrix.smul_mul, Matrix.mul_smul] at h2
      have h3 := smul_right_injective _ hs h2
      ext i j
      have := congrFun (congrFun h3 i) j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.map_apply, eq_intCast] at this
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact_mod_cast this.symm
    obtain ⟨c, hc⟩ := hinv _ _ hrel
    apply hno c
    have e3 : ((redSL p γ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) := by
      ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [e3]; exact hc

end

end NormalizerLean
