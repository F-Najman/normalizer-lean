module

public import NormalizerDelta.MDelta

@[expose] public section

/-!
# §M: the σH coset description, finiteness, and the count of `aut_orders.py`

* `exists_hermite`: an integer matrix W of positive determinant is σ·[[a, b], [0, d]] with σ ∈ SL₂(ℤ),
  a d = det W, 0 ≤ b < d (a = gcd of the first column, Bézout, then b reduced mod d).
* `exists_sigmaH'`: for g ∈ M_Δ, h√e·g is an integer matrix of determinant h²e ∣ N; dividing its Hermite form
  by gcd(a, b, d) gives a primitive Hermite form, and σ = γ₀ r with r ∈ R, γ₀ ∈ Γ₀(N).
* `sigmaH_unique'`: if c σH = γ c' σ'H', then M = σ'⁻¹γ⁻¹σ ∈ SL₂(ℤ) is upper triangular with M H ∝ H';
  primitivity gives a = a', d = d', b' ≡ b mod d, so M = ±1 and σ = σ'.
* The map (σ, H) ↦ (σH)⁻¹ Γ₀(N) is a bijection onto K/Γ₀(N) for Γ₀(N) ≤ K ≤ M_Δ (`relIndex_eq_card_sigmaH`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Hermite normal form of a 2×2 integer matrix -/

theorem exists_hermite_aux (w00 w01 w10 w11 p q A B : ℤ) (g₁ : ℕ) (hg0 : 0 < g₁)
    (hp : w00 = g₁ * p) (hq : w10 = g₁ * q) (hbez : p * A + q * B = 1)
    (hW : 0 < w00 * w11 - w01 * w10) :
    ∃ σ : SL(2, ℤ), ∃ a b d : ℕ, 0 < a ∧ 0 < d ∧ (a : ℤ) * d = w00 * w11 - w01 * w10 ∧ b < d ∧
      w00 = σ 0 0 * a ∧ w01 = σ 0 0 * b + σ 0 1 * d ∧ w10 = σ 1 0 * a ∧
      w11 = σ 1 0 * b + σ 1 1 * d := by
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = p * w11 - q * w01 := ⟨_, rfl⟩
  have hdetW : w00 * w11 - w01 * w10 = g₁ * δ := by rw [hp, hq, hδdef]; ring
  have hδ : 0 < δ := by
    have h1 : 0 < (g₁ : ℤ) * δ := hdetW ▸ hW
    exact pos_of_mul_pos_right h1 (by positivity)
  obtain ⟨β, hβdef⟩ : ∃ β, β = A * w01 + B * w11 := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = β / δ := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = β % δ := ⟨_, rfl⟩
  have hβ : δ * k + r = β := by rw [hkdef, hrdef]; exact Int.mul_ediv_add_emod β δ
  have hr0 : 0 ≤ r := hrdef ▸ Int.emod_nonneg β hδ.ne'
  have hrδ : r < δ := hrdef ▸ Int.emod_lt_of_pos β hδ
  have hr' : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  have hδ' : ((δ.toNat : ℕ) : ℤ) = δ := Int.toNat_of_nonneg hδ.le
  refine ⟨mkSL p (p * k - B) q (q * k + A) (by linear_combination hbez), g₁, r.toNat, δ.toNat,
    hg0, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hδ', hdetW]
  · change w00 = p * g₁; rw [hp]; ring
  · change w01 = p * ((r.toNat : ℕ) : ℤ) + (p * k - B) * ((δ.toNat : ℕ) : ℤ)
    rw [hr', hδ']
    linear_combination (-w01) * hbez + (-p) * hβ + (-p) * hβdef + B * hδdef
  · change w10 = q * g₁; rw [hq]; ring
  · change w11 = q * ((r.toNat : ℕ) : ℤ) + (q * k + A) * ((δ.toNat : ℕ) : ℤ)
    rw [hr', hδ']
    linear_combination (-w11) * hbez + (-q) * hβ + (-q) * hβdef - A * hδdef

theorem exists_hermite (w00 w01 w10 w11 : ℤ) (hW : 0 < w00 * w11 - w01 * w10) :
    ∃ σ : SL(2, ℤ), ∃ a b d : ℕ, 0 < a ∧ 0 < d ∧ (a : ℤ) * d = w00 * w11 - w01 * w10 ∧ b < d ∧
      w00 = σ 0 0 * a ∧ w01 = σ 0 0 * b + σ 0 1 * d ∧ w10 = σ 1 0 * a ∧
      w11 = σ 1 0 * b + σ 1 1 * d := by
  have hg0 : 0 < Int.gcd w00 w10 := by
    apply Int.gcd_pos_iff.2
    by_contra h
    push_neg at h
    rw [h.1, h.2] at hW; simp at hW
  have hg0z : ((Int.gcd w00 w10 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  obtain ⟨p, hp⟩ := Int.gcd_dvd_left w00 w10
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right w00 w10
  have hbez0 := Int.gcd_eq_gcd_ab w00 w10
  generalize Int.gcdA w00 w10 = A at hbez0
  generalize Int.gcdB w00 w10 = B at hbez0
  generalize Int.gcd w00 w10 = G at hbez0 hp hq hg0 hg0z
  have hbez : p * A + q * B = 1 := by
    apply mul_left_cancel₀ hg0z
    linear_combination (-1 : ℤ) * hbez0 + (-A) * hp + (-B) * hq
  exact exists_hermite_aux w00 w01 w10 w11 p q A B G hg0 hp hq hbez hW

/-! ### Existence of σH -/

theorem exists_sigmaH' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {g : SL(2, ℝ)} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := mem_MDelta_iff.1 hg
  have hh := hDelta_pos N Δ
  set h := hDelta N Δ with hhdef
  have hn : N / h ^ 2 = nDelta N Δ := rfl
  rw [hn] at he hdet
  have hNz : (N : ℤ) = nDelta N Δ * (h : ℤ) ^ 2 := by exact_mod_cast (nDelta_mul N Δ).symm
  have hWdet : (a * e * h) * (d * e * h) - b * (N * c) = (h : ℤ) ^ 2 * e := by
    rw [hNz]; linear_combination (h : ℤ) ^ 2 * hdet
  have hWpos : 0 < (a * e * h : ℤ) * (d * e * h) - b * (N * c) := by rw [hWdet]; positivity
  obtain ⟨σ, A, B, D, hA, hD, hAD, hBD, h00, h01, h10, h11⟩ := exists_hermite _ _ _ _ hWpos
  set t := Nat.gcd (Nat.gcd A B) D with htdef
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hD
  obtain ⟨A', hA'⟩ : t ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B', hB'⟩ : t ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨D', hD'⟩ : t ∣ D := Nat.gcd_dvd_right _ _
  have hADn : A * D = h ^ 2 * e := by
    have : (A : ℤ) * D = (h : ℤ) ^ 2 * e := hAD.trans hWdet
    exact_mod_cast this
  have hHerm : IsHermiteN N A' B' D' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hA'] at hA; exact Nat.pos_of_mul_pos_left hA
    · rw [hD'] at hD; exact Nat.pos_of_mul_pos_left hD
    · have h1 : A' * D' ∣ A * D := ⟨t * t, by rw [hA', hD']; ring⟩
      have h2 : A * D ∣ N := by
        rw [hADn, ← nDelta_mul N Δ, mul_comm (nDelta N Δ)]
        exact mul_dvd_mul_left _ he
      exact h1.trans h2
    · rw [hB', hD'] at hBD; exact Nat.lt_of_mul_lt_mul_left hBD
    · have h1 : t = t * Nat.gcd (Nat.gcd A' B') D' := by
        conv_lhs => rw [htdef, hA', hB', hD', Nat.gcd_mul_left, Nat.gcd_mul_left]
      have h2 : t * Nat.gcd (Nat.gcd A' B') D' = t * 1 := by rw [← h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left ht0 h2
  obtain ⟨r, ⟨hrR, hσr⟩, -⟩ := hR σ
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hse : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast he0)).ne'
  have hεr : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht0.ne'
  set κ := ε / (Real.sqrt e * h)
  refine ⟨ofZ (r * σ⁻¹), ?_, r, hrR, A', B', D', hHerm, κ * t, ?_, ?_⟩
  · have : r * σ⁻¹ = (σ * r⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.mem_map_of_mem _ (inv_mem hσr)
  · exact mul_ne_zero (div_ne_zero hεr (mul_ne_zero hse hhr)) htr
  · have step1 : (g : Matrix (Fin 2) (Fin 2) ℝ) =
        κ • !![(a : ℝ) * e * h, b; N * c, d * e * h] := by
      rw [hgm]; ext i j; fin_cases i <;> fin_cases j <;> simp [κ] <;> field_simp
    have R00 : (a : ℝ) * e * h = σ 0 0 * (t * A') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h00; push_cast at this; rw [this, hA']; push_cast; ring
    have R01 : (b : ℝ) = σ 0 0 * (t * B') + σ 0 1 * (t * D') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h01; push_cast at this; rw [this, hB', hD']; push_cast
      ring
    have R10 : (N : ℝ) * c = σ 1 0 * (t * A') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h10; push_cast at this; rw [this, hA']; push_cast; ring
    have R11 : (d : ℝ) * e * h = σ 1 0 * (t * B') + σ 1 1 * (t * D') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h11; push_cast at this; rw [this, hB', hD']; push_cast
      ring
    have step2 : !![(a : ℝ) * e * h, b; N * c, d * e * h] =
        (t : ℝ) • ((ofZ σ : Matrix (Fin 2) (Fin 2) ℝ) * hermMat A' B' D') := by
      rw [coe_ofZ σ, hermMat]
      ext i j; fin_cases i <;> fin_cases j <;> simp
      · linear_combination R00
      · linear_combination R01
      · linear_combination R10
      · linear_combination R11
    calc ((ofZ (r * σ⁻¹) * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        = (ofZ (r * σ⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
            ((κ * t) • ((ofZ σ : Matrix (Fin 2) (Fin 2) ℝ) * hermMat A' B' D')) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, step1, step2, smul_smul]
      _ = (κ * t) • ((ofZ (r * σ⁻¹ * σ) : Matrix (Fin 2) (Fin 2) ℝ) * hermMat A' B' D') := by
          rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
      _ = (κ * t) • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat A' B' D') := by
          rw [show r * σ⁻¹ * σ = r by group]

/-! ### Uniqueness of σH -/

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N :=
  CongruenceSubgroup.Gamma0_mem.2 (by simp)

/-- Bézout for gcd(x, y, z) = 1. -/
theorem bezout3 {x y z : ℕ} (h : Nat.gcd (Nat.gcd x y) z = 1) :
    ∃ u v w : ℤ, u * x + v * y + w * z = 1 := by
  have h1 := Nat.gcd_eq_gcd_ab (Nat.gcd x y) z
  have h2 := Nat.gcd_eq_gcd_ab x y
  rw [h, h2] at h1
  exact ⟨Nat.gcdA x y * Nat.gcdA (Nat.gcd x y) z, Nat.gcdB x y * Nat.gcdA (Nat.gcd x y) z,
    Nat.gcdB (Nat.gcd x y) z, by push_cast at h1 ⊢; linear_combination -h1⟩

/-- The integer core of the uniqueness: if M = [[s, m], [0, s]] (s = ±1) and M H ∝ H' for primitive
Hermite forms H, H', then H = H' and m = 0. -/
theorem hermite_unique_int {a b d a' b' d' : ℕ} {s m : ℤ} (ha : 0 < a) (hd : 0 < d)
    (hbd : b < d) (hbd' : b' < d') (hprim : Nat.gcd (Nat.gcd a b) d = 1)
    (hprim' : Nat.gcd (Nat.gcd a' b') d' = 1) (hs : s * s = 1)
    (X1 : s * a * b' = (s * b + m * d) * a') (X2 : s * a * d' = s * d * a') :
    a = a' ∧ b = b' ∧ d = d' ∧ m = 0 := by
  obtain ⟨u, v, w, huvw⟩ := bezout3 hprim
  obtain ⟨u', v', w', huvw'⟩ := bezout3 hprim'
  set k := s * m with hk
  have Y1 : (a : ℤ) * b' = (b + k * d) * a' := by
    linear_combination s * X1 - ((a : ℤ) * b' - b * a') * hs
  have Y2 : (a : ℤ) * d' = d * a' := by
    linear_combination s * X2 - ((a : ℤ) * d' - d * a') * hs
  have hdiv1 : (a : ℤ) = a' * (u' * a + v' * (b + k * d) + w' * d) := by
    linear_combination (-(a : ℤ)) * huvw' + v' * Y1 + w' * Y2
  have hdiv2 : (a' : ℤ) = a * (u * a' + v * (b' - k * d') + w * d') := by
    linear_combination (-(a' : ℤ)) * huvw - v * Y1 + v * k * Y2 - w * Y2
  have haa : a = a' := by
    have h1 : (a' : ℤ) ∣ a := ⟨_, hdiv1⟩
    have h2 : (a : ℤ) ∣ a' := ⟨_, hdiv2⟩
    exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h2) (Int.natCast_dvd_natCast.1 h1)
  subst haa
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdd : d = d' := by
    have : (a : ℤ) * d' = a * d := by linear_combination Y2
    exact_mod_cast (mul_left_cancel₀ haz this).symm
  subst hdd
  have hbk : (b' : ℤ) - b = k * d := by
    have : (a : ℤ) * b' = a * (b + k * d) := by linear_combination Y1
    linear_combination mul_left_cancel₀ haz this
  have hdvd : (d : ℤ) ∣ (b' : ℤ) - b := ⟨k, by rw [hbk]; ring⟩
  have habs : |(b' : ℤ) - b| < d := by rw [abs_lt]; constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hbb : b = b' := by omega
  subst hbb
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk0 : k = 0 := by
    have : k * d = 0 := by rw [← hbk, h0]
    exact (mul_eq_zero.1 this).resolve_right hdz
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact (mul_eq_zero.1 (hk ▸ hk0)).resolve_left hs0

theorem sigmaH_unique' {N : ℕ} {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R)
    {r r' : SL(2, ℤ)} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d' : ℕ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} {γ : SL(2, ℝ)}
    (h : c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) =
      (γ : Matrix (Fin 2) (Fin 2) ℝ) * (c' • ((ofZ r' : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a' b' d')))
    (hc : c ≠ 0) (_hc' : c' ≠ 0) (hγ : γ ∈ Gamma0R N) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  obtain ⟨M, hMdef⟩ : ∃ M : SL(2, ℤ), M = r'⁻¹ * γ₀⁻¹ * r := ⟨_, rfl⟩
  have key : c • ((ofZ M : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) = c' • hermMat a' b' d' := by
    calc c • ((ofZ M : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d)
        = (ofZ (r'⁻¹ * γ₀⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
            (c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d)) := by
          rw [hMdef, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
            ← map_mul]
      _ = (ofZ (r'⁻¹ * γ₀⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) *
            ((ofZ γ₀ : Matrix (Fin 2) (Fin 2) ℝ) *
              (c' • ((ofZ r' : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a' b' d'))) := by rw [h]
      _ = c' • hermMat a' b' d' := by
          rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
            ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
            ← map_mul, show r'⁻¹ * γ₀⁻¹ * γ₀ * r' = 1 by group, map_one,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have entry : ∀ i j, c * ((ofZ M : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) i j =
      c' * hermMat a' b' d' i j := fun i j => by
    have := congrFun (congrFun key i) j
    simpa using this
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [coe_ofZ, hermMat, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one] at e00 e01 e10 e11
  simp only [mul_zero, add_zero] at e00 e01 e10 e11
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hM10 : M 1 0 = 0 := by
    have h1 : (M 1 0 : ℝ) * a = 0 := (mul_eq_zero.1 e10).resolve_left hc
    exact_mod_cast (mul_eq_zero.1 h1).resolve_right har
  rw [hM10] at e11
  simp only [Int.cast_zero, zero_mul, zero_add] at e11
  have hdetM : M 0 0 * M 1 1 = 1 := by
    have := M.2; rw [det_fin_two, hM10, mul_zero, sub_zero] at this; exact this
  have X1 : (M 0 0 * a) * b' = (M 0 0 * b + M 0 1 * d) * a' := by
    have := cross_of_prop hc (κ' := c') (x := M 0 0 * a) (y := M 0 0 * b + M 0 1 * d) (x' := a')
      (y' := b') (by push_cast; exact e00) (by push_cast; exact e01)
    exact_mod_cast this
  have X2 : (M 0 0 * a) * d' = (M 1 1 * d) * a' := by
    have := cross_of_prop hc (κ' := c') (x := M 0 0 * a) (y := M 1 1 * d) (x' := a') (y' := d')
      (by push_cast; exact e00) (by push_cast; exact e11)
    exact_mod_cast this
  have hss : M 1 1 = M 0 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  rw [hss] at X2 hdetM
  obtain ⟨haa, hbb, hdd, hM01⟩ :=
    hermite_unique_int (s := M 0 0) (m := M 0 1) ha hd hbd hbd' hprim hprim' hdetM X1 X2
  refine ⟨?_, haa, hbb, hdd⟩
  have hr_eq : r = γ₀ * r' * M := by rw [hMdef]; group
  have hrr : r * r'⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hM1 : M = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [h1, hss, hM01, hM10]
      rw [hr_eq, hM1, mul_one, mul_inv_cancel_right]; exact hγ₀
    · have hM1 : M = -1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [h1, hss, hM01, hM10]
      have : γ₀ * r' * M * r'⁻¹ = γ₀ * -1 := by
        rw [hM1, mul_neg_one, neg_mul, mul_neg_one, mul_inv_cancel_right]
      rw [hr_eq, this]
      exact mul_mem hγ₀ (neg_one_mem_Gamma0 N)
  exact (hR r).unique ⟨hr, by rw [mul_inv_cancel]; exact one_mem _⟩ ⟨hr', hrr⟩

end

end NormalizerLean
