module

public import NormalizerDelta.GenMain

@[expose] public section

/-!
# General modular curves: §P, prime level

H ≤ SL₂(F_p).
* (`fixesUniqueLine_iff'`) If H fixes the line through (1, 0), H is upper triangular.  Γ₁(p) ≤ Γ_H iff
  T = [[1, 1], [0, 1]] ∈ H.  If T ∈ H, only (1, 0) is fixed (T has no other eigenline).  If T ∉ H, H has no
  non-trivial unipotent element; then either some h = [[α, β], [0, δ]] ∈ H has α ≠ δ, H is abelian (commutators are
  unipotent) and (β, δ − α) spans a second fixed line, or every h has α = δ = ±1 and h² unipotent forces β = 0, so
  (0, 1) is fixed.
* If T ∈ H, the Fricke element W_p normalizes Γ_H: W₀ γ = γ' W₀ with γ' = [[d, −c/p], [−pb, a]] and
  γ' mod p = (γ mod p)⁻¹·[[1, t], [0, 1]] ∈ H; and W_p² = −1.
* For g = projSL m ∈ Nor(Γ_H) with det m = p, Prop. 4.5(2) gives m ≡ [[0, *], [0, 0]] mod p, so g W_p⁻¹ ∈ SL₂(ℤ).
  Hence Nor(Γ_H) = Γ_{N(H)} ⊔ ⟨W_p⟩ with [Nor : Γ_{N(H)}] = 2 (W_p is irrational).
* A unique fixed line is moved to the line through (1, 0) by conjugation (`card_BG_map_conj`).  If H does not fix
  exactly one line, it fixes none or two independent ones, which is the hypothesis of §G.
-/

open Matrix MatrixGroups

-- As in `CartanNonsplit.lean`: Mathlib v4.35.0-rc3's instance making `ZMod p` an `AddCommGroup` breaks rewriting
-- with `sub_zero`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace NormalizerLean

noncomputable section

variable {p : ℕ}

theorem fixesLine_iff_self {H : Subgroup SL(2, ZMod p)} {v : Fin 2 → ZMod p} :
    FixesLine H p v ↔ ∀ h ∈ H, ∃ c : ZMod p, (h : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = c • v := by
  simp only [FixesLine, ZMod.cast_id', Matrix.map_id]

/-- [[1, b], [0, 1]] ∈ SL₂(ℤ/p). -/
def uMat (b : ZMod p) : SL(2, ZMod p) := ⟨!![1, b; 0, 1], by simp [det_fin_two_of]⟩

theorem uMat_mul (a b : ZMod p) : uMat a * uMat b = uMat (a + b) := by
  apply Subtype.ext
  show !![(1 : ZMod p), a; 0, 1] * !![1, b; 0, 1] = !![1, a + b; 0, 1]
  rw [Matrix.mul_fin_two]; simp [add_comm]

theorem uMat_zero : uMat (0 : ZMod p) = 1 := by
  apply Subtype.ext
  show !![(1 : ZMod p), 0; 0, 1] = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem uMat_pow (b : ZMod p) (n : ℕ) : uMat b ^ n = uMat ((n : ZMod p) * b) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uMat_zero]
  | succ n ih => rw [pow_succ, ih, uMat_mul]; congr 1; push_cast; ring

theorem uMat_mem [NeZero p] {H : Subgroup SL(2, ZMod p)} (hT : uMat (1 : ZMod p) ∈ H) (b : ZMod p) :
    uMat b ∈ H := by
  have : uMat b = uMat (1 : ZMod p) ^ b.val := by rw [uMat_pow, mul_one, ZMod.natCast_zmod_val]
  rw [this]; exact pow_mem hT _

theorem Gamma1_le_GammaH_iff [NeZero p] {H : Subgroup SL(2, ZMod p)} :
    CongruenceSubgroup.Gamma1 p ≤ GammaH p H ↔ uMat 1 ∈ H := by
  constructor
  · intro h
    have hm : mkSL 1 1 0 1 (by ring) ∈ CongruenceSubgroup.Gamma1 p := by
      rw [CongruenceSubgroup.Gamma1_mem]; simp [mkSL]
    have := h hm
    rw [mem_GammaH] at this
    convert this using 1
    ext i j
    rw [redSL_apply]
    fin_cases i <;> fin_cases j <;> simp [uMat, mkSL]
  · intro hT γ hγ
    rw [CongruenceSubgroup.Gamma1_mem] at hγ
    obtain ⟨h00, h11, h10⟩ := hγ
    rw [mem_GammaH]
    convert uMat_mem hT ((γ 0 1 : ℤ) : ZMod p) using 1
    ext i j
    rw [redSL_apply]
    fin_cases i <;> fin_cases j <;> simp [uMat, h00, h11, h10]

/-! ### The unique fixed line -/

theorem upper_of_fixes {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0]) {h : SL(2, ZMod p)}
    (hh : h ∈ H) : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
  obtain ⟨c, hc⟩ := fixesLine_iff_self.1 hB h hh
  have := congrFun hc 1
  simpa [Matrix.mulVec, dotProduct] using this

theorem T_mem_of_unique (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0])
    (huniq : ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) : uMat (1 : ZMod p) ∈ H := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hT
  have hdet : ∀ h ∈ H, (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * h 1 1 = 1 := by
    intro h hh
    have := h.2
    rw [det_fin_two, upper_of_fixes hB hh, mul_zero, sub_zero] at this
    exact this
  -- no non-trivial unipotent element
  have hU : ∀ h ∈ H, (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 → (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
    intro h hh h00
    by_contra hb
    apply hT
    have h11 : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by
      have := hdet h hh; rwa [h00, one_mul] at this
    have hhu : h = uMat ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [uMat, h00]
      · simp [uMat]
      · simp [uMat, upper_of_fixes hB hh]
      · simp [uMat, h11]
    have : uMat (1 : ZMod p) = h ^ (((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1)⁻¹).val := by
      rw [hhu, uMat_pow, ZMod.natCast_zmod_val]
      congr 1
      simp [uMat, inv_mul_cancel₀ hb]
    rw [this]; exact pow_mem hh _
  by_cases hex : ∃ h ∈ H, (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ h 1 1
  · obtain ⟨h, hh, hne⟩ := hex
    set α := (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0
    set β := (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
    set δ := (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1
    have hαδ : α * δ = 1 := hdet h hh
    -- every h' ∈ H commutes with h: β (α' − δ') = β' (α − δ)
    have hcomm : ∀ h' ∈ H, β * ((h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 - h' 1 1) =
        (h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 * (α - δ) := by
      intro h' hh'
      set k := h * h' * h⁻¹ * h'⁻¹ with hk
      have hkH : k ∈ H := mul_mem (mul_mem (mul_mem hh hh') (inv_mem hh)) (inv_mem hh')
      have hα'δ' := hdet h' hh'
      have h10 := upper_of_fixes hB hh
      have h'10 := upper_of_fixes hB hh'
      have k00 : (k : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
        simp only [hk, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10, h'10]
        simp
        linear_combination ((h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 *
          (h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1) * hαδ + hα'δ'
      have k01 := hU k hkH k00
      simp only [hk, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h10, h'10] at k01
      simp at k01
      have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hαδ
      have hα'0 : (h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hα'δ'
      have : α * (h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 *
          ((h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 * (α - δ) -
            β * ((h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 - h' 1 1)) = 0 := by
        linear_combination k01
      have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero hα0 hα'0)
      linear_combination -this
    -- the line through (β, δ − α) is fixed
    have hfix : FixesLine H p ![β, δ - α] := by
      rw [fixesLine_iff_self]
      intro h' hh'
      refine ⟨(h' : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1, ?_⟩
      have hc := hcomm h' hh'
      have h'10 := upper_of_fixes hB hh'
      ext i; fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination hc
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h'10]
    obtain ⟨c, hc⟩ := huniq _ hfix
    have := congrFun hc 1
    simp at this
    exact hne (by linear_combination -this)
  · push Not at hex
    -- every h ∈ H is ±1, so (0, 1) is fixed
    have hfix : FixesLine H p ![0, 1] := by
      rw [fixesLine_iff_self]
      intro h hh
      have h10 := upper_of_fixes hB hh
      have hd := hex h hh
      have hsq : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ^ 2 = 1 := by
        have := hdet h hh; rw [← hd] at this; linear_combination this
      have h01 : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
        have hh2 : h * h ∈ H := mul_mem hh hh
        have e00 : ((h * h : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
          simp [Matrix.mul_apply, Fin.sum_univ_two, h10]; linear_combination hsq
        have e01 := hU _ hh2 e00
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← hd] at e01
        -- e01 : h00 * h01 + h01 * h00 = 0
        by_cases h2 : (2 : ZMod p) = 0
        · -- p = 2: h00 = 1
          have h00 : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
            have : ((h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 - 1) ^ 2 = 0 := by
              linear_combination hsq - (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * h2 + h2
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
            linear_combination this
          exact hU h hh h00
        · have h00 : (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 ≠ 0 := by
            intro h0; rw [h0] at hsq; simp at hsq
          have : 2 * (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * (h : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
            linear_combination e01
          exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 h00)
      refine ⟨(h : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1, ?_⟩
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h01]
    obtain ⟨c, hc⟩ := huniq _ hfix
    have := congrFun hc 1
    simp at this

theorem fixesUniqueLine_iff' {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)}
    (hB : FixesLine H p ![1, 0]) :
    (∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) ↔ CongruenceSubgroup.Gamma1 p ≤ GammaH p H := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Gamma1_le_GammaH_iff]
  constructor
  · exact T_mem_of_unique hp hB
  · intro hT w hw
    obtain ⟨c, hc⟩ := fixesLine_iff_self.1 hw _ hT
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    have hw1 : w 1 = 0 := by
      by_contra hne
      have hc1 : c = 1 := by
        have : (c - 1) * w 1 = 0 := by linear_combination -e1
        have := (mul_eq_zero.1 this).resolve_right hne
        linear_combination this
      rw [hc1] at e0
      exact hne (by linear_combination e0)
    refine ⟨w 0, ?_⟩
    ext i; fin_cases i <;> simp [hw1]

/-! ### The Fricke element -/

/-- W₀ = [[0, −1], [p, 0]]. -/
def frickeZ (p : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; (p : ℤ), 0]

theorem det_frickeZ (p : ℕ) : (frickeZ p).det = p := by simp [frickeZ, det_fin_two_of]

theorem frickeP_eq (p : ℕ) : frickeP p = projSL ((frickeZ p).map (Int.cast : ℤ → ℝ)) := by
  unfold frickeP frickeZ
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem frickeP_mul_self {p : ℕ} (hp : 0 < p) : frickeP p * frickeP p = -1 := by
  have hD : 0 < (frickeZ p).det := by rw [det_frickeZ]; exact_mod_cast hp
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hpr.le
  have hs0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hpr).ne'
  apply Subtype.ext
  rw [frickeP_eq, Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hD, det_frickeZ,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Int.cast_natCast]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeZ, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    linarith

theorem frickeP_not_mem_SL2ZR (hp : p.Prime) : frickeP p ∉ SL2ZR := by
  rintro ⟨γ, -, hγ⟩
  have hD : 0 < (frickeZ p).det := by rw [det_frickeZ]; exact_mod_cast hp.pos
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hγ
  simp only [frickeP_eq, coe_projSL_int hD, det_frickeZ, Int.cast_natCast] at this
  rw [coe_ofZ_eq_map] at this
  simp [frickeZ] at this
  have hsq : (Real.sqrt p)⁻¹ * p = Real.sqrt p := by
    have hs0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hpr).ne'
    field_simp
    exact (Real.sq_sqrt hpr.le).symm
  rw [hsq] at this
  exact hp.irrational_sqrt ⟨(γ 1 0 : ℚ), by push_cast; exact this⟩

theorem neg_one_mem_toR_GammaH_normH (p : ℕ) (H : Subgroup SL(2, ZMod p)) :
    (-1 : SL(2, ℝ)) ∈ toR (GammaH p (NormH H)) := by
  have h1 : ofZ (-1) = -1 := by
    rw [ofZ_neg]
    exact congrArg Neg.neg (map_one (SpecialLinearGroup.map (Int.castRingHom ℝ)))
  rw [← h1]
  refine ofZ_mem_toR ?_
  rw [mem_GammaH, Subgroup.mem_normalizer_iff]
  intro h
  simp

theorem frickeP_conj_mem (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0])
    (hT : uMat (1 : ZMod p) ∈ H) {γ : SL(2, ℤ)} (hγ : γ ∈ GammaH p H) :
    frickeP p * ofZ γ * (frickeP p)⁻¹ ∈ toR (GammaH p H) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h10 : (p : ℤ) ∣ γ 1 0 := by
    have := upper_of_fixes hB (show redSL p γ ∈ H from hγ)
    rw [redSL_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  obtain ⟨c', hc'⟩ := h10
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by have := γ.2; rwa [det_fin_two] at this
  set γ' := mkSL (γ 1 1) (-c') (-(p : ℤ) * γ 0 1) (γ 0 0)
    (by rw [hc'] at hdetγ; linear_combination hdetγ) with hγ'
  have hD : 0 < (frickeZ p).det := by rw [det_frickeZ]; exact_mod_cast hp.pos
  have hrel : frickeZ p * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * frickeZ p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frickeZ, γ', mkSL, Matrix.mul_apply, Fin.sum_univ_two, hc'] <;> ring
  have h1 := (projSL_mul_ofZ_eq_iff hD γ γ').2 hrel
  have e : frickeP p * ofZ γ * (frickeP p)⁻¹ = ofZ γ' := by rw [frickeP_eq, h1]; group
  rw [e]
  refine ofZ_mem_toR ?_
  rw [mem_GammaH]
  have hp0 : ((p : ℤ) : ZMod p) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
  have hdetZ : ((γ 0 0 : ℤ) : ZMod p) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hdetγ
    rw [hc'] at this; push_cast at this; rw [ZMod.natCast_self] at this
    linear_combination this
  set t : ZMod p := ((γ 0 0 : ℤ) : ZMod p) * (-(c' : ZMod p) + (γ 0 1 : ℤ)) with ht
  have key : redSL p γ' = (redSL p γ)⁻¹ * uMat t := by
    ext i j
    rw [redSL_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [γ', mkSL, uMat, Matrix.mul_apply, Fin.sum_univ_two, hc', ht, ZMod.natCast_self]
    · linear_combination ((c' : ZMod p) - (γ 0 1 : ℤ)) * hdetZ
  rw [key]
  exact mul_mem (inv_mem hγ) (uMat_mem hT t)

theorem frickeP_mem_normG (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0])
    (hT : uMat (1 : ZMod p) ∈ H) : frickeP p ∈ NormG (toR (GammaH p H)) := by
  rw [Subgroup.mem_normalizer_iff]
  have hW2 := frickeP_mul_self hp.pos
  have fwd : ∀ y ∈ toR (GammaH p H), frickeP p * y * (frickeP p)⁻¹ ∈ toR (GammaH p H) := by
    rintro y ⟨γ, hγ, rfl⟩
    exact frickeP_conj_mem hp hB hT hγ
  intro y
  refine ⟨fwd y, fun hy => ?_⟩
  have := fwd _ hy
  rwa [show frickeP p * (frickeP p * y * (frickeP p)⁻¹) * (frickeP p)⁻¹ =
      (frickeP p * frickeP p) * y * (frickeP p * frickeP p)⁻¹ by group, hW2, inv_neg, inv_one, neg_mul, one_mul,
      mul_neg, mul_one, neg_neg] at this

/-! ### The normalizer in the standard position -/

theorem mem_normG_prime_unique (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0])
    (huniq : ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) {g : SL(2, ℝ)}
    (hg : g ∈ NormG (toR (GammaH p H))) :
    g ∈ toR (GammaH p (NormH H)) ∨ g * (frickeP p)⁻¹ ∈ toR (GammaH p (NormH H)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hW := frickeP_mem_normG hp hB (T_mem_of_unique hp hB huniq)
  obtain ⟨m, hD, hDN, hprim, rfl⟩ := normG_level_form' (Gamma_le_GammaH p H) hg
  have hdet : m.det = 1 ∨ m.det = p := by
    have h1 : m.det.natAbs ∣ p := by
      have := Int.natAbs_dvd_natAbs.2 hDN; simpa using this
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · left; omega
    · right; omega
  rcases hdet with hD1 | hDp
  · left
    rw [← normG_GammaH_inf_SL2ZR']
    exact ⟨hg, (⟨m, hD1⟩ : SL(2, ℤ)), Subgroup.mem_top _, ofZ_eq_projSL hD hD1⟩
  · right
    have hns : ¬ IsSplitMod H p := by
      rintro ⟨v, w, hv, hw, hu⟩
      obtain ⟨c, rfl⟩ := huniq v hv
      obtain ⟨c', rfl⟩ := huniq w hw
      have := Fact.mk hp
      simp at hu
    obtain ⟨⟨a', ha'⟩, ⟨c', hc'⟩, -⟩ := borel_shape' inferInstance hD hg hp (hprim p hp) hB hns (by rw [hDp])
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hdet0 : (-m 0 1) * c' - a' * (-m 1 1) = 1 := by
      have h := hDp
      rw [det_fin_two, ha', hc'] at h
      apply mul_left_cancel₀ hp0
      linear_combination h
    set γ₀ := mkSL (-m 0 1) a' (-m 1 1) c' hdet0 with hγ₀
    have hW0 : 0 < (frickeZ p).det := by rw [det_frickeZ]; exact_mod_cast hp.pos
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hpr.le
    have hs0 : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hpr).ne'
    have key : projSL (m.map (Int.cast : ℤ → ℝ)) * (frickeP p)⁻¹ = ofZ γ₀ := by
      rw [frickeP_eq, ← projSL_adjugate hW0]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hD, coe_projSL_int (by rwa [det_adjugate_two]),
        det_adjugate_two, det_frickeZ, hDp, coe_ofZ_eq_map, Int.cast_natCast]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hinv : (Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹ = (p : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hpr.le]
      rw [hinv]
      have hpr0 : (p : ℝ) ≠ 0 := hpr.ne'
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [frickeZ, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, γ₀, mkSL, ha', hc'] <;>
        field_simp
    rw [← normG_GammaH_inf_SL2ZR']
    refine ⟨Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hW), ?_⟩
    rw [key]
    exact ofZ_mem_toR (Subgroup.mem_top _)

theorem normG_GammaH_prime_unique' {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)}
    (hB : FixesLine H p ![1, 0]) (huniq : ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) :
    NormG (toR (GammaH p H)) = toR (GammaH p (NormH H)) ⊔ Subgroup.zpowers (frickeP p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hW := frickeP_mem_normG hp hB (T_mem_of_unique hp hB huniq)
  apply le_antisymm
  · intro g hg
    rcases mem_normG_prime_unique hp hB huniq hg with h | h
    · exact Subgroup.mem_sup_left h
    · have e : g = (g * (frickeP p)⁻¹) * frickeP p := by group
      rw [e]
      exact Subgroup.mul_mem_sup h (Subgroup.mem_zpowers _)
  · exact sup_le (GammaH_normH_le_normG p H) ((Subgroup.zpowers_le).2 hW)

theorem card_BG_prime_std (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (hB : FixesLine H p ![1, 0])
    (huniq : ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • ![1, 0]) :
    Nat.card (BG (toR (GammaH p H))) = 2 * H.relIndex (NormH H) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hW := frickeP_mem_normG hp hB (T_mem_of_unique hp hB huniq)
  have hBA : toR (GammaH p H) ≤ toR (GammaH p (NormH H)) :=
    Subgroup.map_mono (GammaH_mono Subgroup.le_normalizer)
  have hANor : toR (GammaH p (NormH H)) ≤ NormG (toR (GammaH p H)) := GammaH_normH_le_normG p H
  have hWA : frickeP p ∉ toR (GammaH p (NormH H)) := fun h =>
    frickeP_not_mem_SL2ZR hp (Subgroup.map_mono le_top h)
  have hneg := neg_one_mem_toR_GammaH_normH p H
  have hidx : (toR (GammaH p (NormH H))).relIndex (NormG (toR (GammaH p H))) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨frickeP p, hW⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases mem_normG_prime_unique hp hB huniq b.2 with h | h
    · right
      refine ⟨h, fun h' => hWA ?_⟩
      have := mul_mem (inv_mem h) h'
      rwa [inv_mul_cancel_left] at this
    · left
      refine ⟨?_, fun h' => hWA ?_⟩
      · have e : (b : SL(2, ℝ)) * frickeP p = ((b : SL(2, ℝ)) * (frickeP p)⁻¹) * (frickeP p * frickeP p) := by
          group
        rw [e, frickeP_mul_self hp.pos]
        exact mul_mem h hneg
      · have e : frickeP p = ((b : SL(2, ℝ)) * (frickeP p)⁻¹)⁻¹ * b := by group
        rw [e]
        exact mul_mem (inv_mem h) h'
  show (toR (GammaH p H)).relIndex (NormG (toR (GammaH p H))) = _
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hBA hANor, hidx, relIndex_toR, relIndex_GammaH_GammaH_normH,
    mul_comm]

/-! ### Conjugation to the standard position, and the two cases -/

theorem card_BG_GammaH_prime_unique' {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)}
    (h : FixesUniqueLine H) :
    Nat.card (BG (toR (GammaH p H))) = 2 * H.relIndex (NormH H) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨v, hv0, hv, huniq⟩ := h
  obtain ⟨P, hP0, hP1⟩ : ∃ P : SL(2, ZMod p), (P : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = v 0 ∧
      (P : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = v 1 := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])
      exact ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by rw [det_fin_two_of]; field_simp; ring⟩, by simp [h0], by simp⟩
    · exact ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by rw [det_fin_two_of]; field_simp; ring⟩, by simp, by simp⟩
  have hPe : (P : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ ![1, 0] = v := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, hP0, hP1]
  obtain ⟨σ, hσ⟩ := redSL_surjective p P
  set H' := H.map (MulAut.conj P⁻¹).toMonoidHom with hH'
  have hmemH' : ∀ x : SL(2, ZMod p), x ∈ H' ↔ P * x * P⁻¹ ∈ H := by
    intro x
    rw [hH', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rwa [show P * (P⁻¹ * y * P) * P⁻¹ = y by group]
    · intro hx
      refine ⟨P * x * P⁻¹, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  -- the groups
  have hΓ : toR (GammaH p H') = (toR (GammaH p H)).map (MulAut.conj (ofZ σ)⁻¹).toMonoidHom := by
    ext g
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨ofZ (σ * γ * σ⁻¹), ofZ_mem_toR ?_, ?_⟩
      · rw [mem_GammaH, map_mul, map_mul, map_inv, hσ]
        exact (hmemH' _).1 hγ
      · show (ofZ σ)⁻¹ * ofZ (σ * γ * σ⁻¹) * ((ofZ σ)⁻¹)⁻¹ = ofZ γ
        have e : ofZ (σ * γ * σ⁻¹) = ofZ σ * ofZ γ * (ofZ σ)⁻¹ := by simp [map_mul, map_inv]
        rw [e]
        group
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
      refine ⟨σ⁻¹ * γ * σ, ?_, ?_⟩
      · show σ⁻¹ * γ * σ ∈ GammaH p H'
        rw [mem_GammaH, hmemH', map_mul, map_mul, map_inv, hσ]
        rwa [show P * (P⁻¹ * redSL p γ * P) * P⁻¹ = redSL p γ by group]
      · show ofZ (σ⁻¹ * γ * σ) = (ofZ σ)⁻¹ * ofZ γ * ((ofZ σ)⁻¹)⁻¹
        simp [map_mul, map_inv]
  have hcard : Nat.card (BG (toR (GammaH p H'))) = Nat.card (BG (toR (GammaH p H))) := by
    rw [hΓ, card_BG_map_conj]
  have hrel : H'.relIndex (NormH H') = H.relIndex (NormH H) := by
    simp only [hH', NormH]
    rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj P⁻¹)]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj P⁻¹).injective
  -- the lines
  have hPP : (P : Matrix (Fin 2) (Fin 2) (ZMod p)) * ((P⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hPP' : ((P⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (P : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hfix : ∀ w, FixesLine H' p w ↔ FixesLine H p ((P : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w) := by
    intro w
    rw [fixesLine_iff_self, fixesLine_iff_self]
    set Pm := (P : Matrix (Fin 2) (Fin 2) (ZMod p))
    set Pi := ((P⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
    constructor
    · intro hw x hx
      obtain ⟨c, hc⟩ := hw (P⁻¹ * x * P) ((hmemH' _).2 (by rwa [show P * (P⁻¹ * x * P) * P⁻¹ = x by group]))
      simp only [Matrix.SpecialLinearGroup.coe_mul] at hc
      refine ⟨c, ?_⟩
      have e : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) * Pm = Pm * (Pi * x * Pm) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
    · intro hw x hx
      obtain ⟨c, hc⟩ := hw (P * x * P⁻¹) ((hmemH' x).1 hx)
      simp only [Matrix.SpecialLinearGroup.coe_mul] at hc
      refine ⟨c, ?_⟩
      have e : Pm * x * Pi * Pm = Pm * x := by
        rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
      have h1 : Pm *ᵥ ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w) = c • (Pm *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec, hc]
      have h2 := congrArg (fun u => Pi *ᵥ u) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul, hPP', Matrix.one_mulVec] at h2
      rwa [← Matrix.mul_assoc, hPP', Matrix.one_mul] at h2
  have hB' : FixesLine H' p ![1, 0] := by rw [hfix, hPe]; exact hv
  have huniq' : ∀ w, FixesLine H' p w → ∃ c : ZMod p, w = c • ![1, 0] := by
    intro w hw
    obtain ⟨c, hc⟩ := huniq _ ((hfix w).1 hw)
    refine ⟨c, ?_⟩
    have := congrArg (fun u => ((P⁻¹ : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ u) hc
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul, hPP', Matrix.one_mulVec] at this
    rw [this, ← hPe, Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]
  rw [← hcard, ← hrel]
  exact card_BG_prime_std hp hB' huniq'

theorem card_BG_GammaH_prime' {p : ℕ} (hp : p.Prime) {H : Subgroup SL(2, ZMod p)} (h : ¬ FixesUniqueLine H) :
    Nat.card (BG (toR (GammaH p H))) = H.relIndex (NormH H) := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  apply card_BG_GammaH'
  intro q hq hqp
  obtain rfl : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
  rw [Nat.Prime.factorization_self hq, pow_one]
  by_cases hex : ∃ v : Fin 2 → ZMod q, v ≠ 0 ∧ FixesLine H q v
  · right
    obtain ⟨v, hv0, hv⟩ := hex
    have : ∃ w, FixesLine H q w ∧ ∀ c : ZMod q, w ≠ c • v := by
      by_contra hcon
      push Not at hcon
      exact h ⟨v, hv0, hv, hcon⟩
    obtain ⟨w, hw, hwv⟩ := this
    refine ⟨v, w, hv, hw, Ne.isUnit ?_⟩
    intro hdet
    obtain ⟨c, hc⟩ := exists_smul_of_det_zero hv0 hdet
    exact hwv c hc
  · left
    rintro ⟨v, ⟨a, b, hab⟩, hv⟩
    apply hex
    refine ⟨v, ?_, hv⟩
    rintro rfl
    simp at hab

end

end NormalizerLean
