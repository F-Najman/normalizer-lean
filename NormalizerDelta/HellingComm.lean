module

public import NormalizerDelta.HellingCore
public import NormalizerDelta.CartanSplit
public import NormalizerDelta.IndexDelta

@[expose] public section

/-!
# Part 9: the commensurator of SL₂(ℤ), and finiteness

* `exists_pow_mem`: if H ∩ L has finite index in L, every x ∈ L has a power xⁿ ∈ H, n ≥ 1 (pigeonhole).
* `exists_isRep_of_conj`: if g·Tᵏ·g⁻¹ and g·Lᵏ·g⁻¹ are integral (T, L the unipotent generators), then g is a real
  multiple of an integral matrix.  The entries give k·a², k·ac, …, and with det g = 1 all ten products k²·uv of
  entries are integers; then g = (k²x)⁻¹·(k²x·g) for a nonzero entry x.
* `commensurable_conj_SL2ZR`: conjugation by projSL(A), A integral with det A = D > 0, maps Γ(D) into SL₂(ℤ) in both
  directions, so it preserves commensurability with SL₂(ℤ).
* `rep_bounds`: for K ⊇ K ∩ SL₂(ℤ) of finite index, d_p of the representatives of K is bounded, and 0 for almost all p.
-/

open Matrix MatrixGroups

namespace NormalizerLean.Helling

/-! ### Powers in subgroups of finite index -/

theorem exists_pow_mem {G : Type*} [Group G] {H L : Subgroup G} (h : H.relIndex L ≠ 0) {x : G} (hx : x ∈ L) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ H := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have hfin : Finite (L ⧸ H.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (QuotientGroup.mk (⟨x, hx⟩ ^ n : L) : L ⧸ H.subgroupOf L))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, ?_⟩
    have := QuotientGroup.eq.1 he
    rw [Subgroup.mem_subgroupOf] at this
    have e : ((⟨x, hx⟩ ^ i : L)⁻¹ * ⟨x, hx⟩ ^ j : L) = ⟨x, hx⟩ ^ (j - i) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e] at this
    simpa using this
  · refine ⟨i - j, by omega, ?_⟩
    have := QuotientGroup.eq.1 he.symm
    rw [Subgroup.mem_subgroupOf] at this
    have e : ((⟨x, hx⟩ ^ j : L)⁻¹ * ⟨x, hx⟩ ^ i : L) = ⟨x, hx⟩ ^ (i - j) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e] at this
    simpa using this

/-- [[1, k], [0, 1]] ∈ SL₂(ℤ). -/
def upZ (k : ℤ) : SL(2, ℤ) := ⟨upM k, det_upT k⟩

/-- [[1, 0], [k, 1]] ∈ SL₂(ℤ). -/
def loZ (k : ℤ) : SL(2, ℤ) := ⟨loM k, det_loT k⟩

@[simp] theorem coe_upZ (k : ℤ) : ((upZ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = upM k := rfl

@[simp] theorem coe_loZ (k : ℤ) : ((loZ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = loM k := rfl

theorem upZ_pow (k : ℤ) (n : ℕ) : upZ k ^ n = upZ (n * k) := by
  induction n with
  | zero => rw [pow_zero]; ext i j; fin_cases i <;> fin_cases j <;> simp [upZ, upM]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [upZ, upM, mul_apply, Fin.sum_univ_two] <;> ring

theorem loZ_pow (k : ℤ) (n : ℕ) : loZ k ^ n = loZ (n * k) := by
  induction n with
  | zero => rw [pow_zero]; ext i j; fin_cases i <;> fin_cases j <;> simp [loZ, loM]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [loZ, loM, mul_apply, Fin.sum_univ_two] <;> ring

theorem ofZ_mem_SL2ZR (γ : SL(2, ℤ)) : ofZ γ ∈ SL2ZR := ⟨γ, trivial, rfl⟩

theorem mem_SL2ZR_iff {x : SL(2, ℝ)} : x ∈ SL2ZR ↔ ∃ γ : SL(2, ℤ), ofZ γ = x := by
  constructor
  · rintro ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
  · rintro ⟨γ, rfl⟩; exact ofZ_mem_SL2ZR γ

/-- An element of SL₂(ℝ) with integral entries lies in SL₂(ℤ). -/
theorem mem_SL2ZR_of_eq_map {x : SL(2, ℝ)} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (h : (x : Matrix (Fin 2) (Fin 2) ℝ) = M.map (Int.cast : ℤ → ℝ)) : x ∈ SL2ZR := by
  have hM : M.det = 1 := by
    have := congrArg Matrix.det h
    rw [Matrix.SpecialLinearGroup.det_coe, det_map_intCast] at this
    exact_mod_cast this.symm
  let γ : SL(2, ℤ) := ⟨M, hM⟩
  refine mem_SL2ZR_iff.2 ⟨γ, Subtype.ext ?_⟩
  rw [coe_ofZ_eq_map, h]

theorem exists_unipotent_pow_mem {H : Subgroup SL(2, ℝ)} (h : H.relIndex SL2ZR ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ofZ (upZ k) ∈ H ∧ ofZ (loZ k) ∈ H := by
  obtain ⟨m, hm, hm'⟩ := exists_pow_mem h (ofZ_mem_SL2ZR (upZ 1))
  obtain ⟨n, hn, hn'⟩ := exists_pow_mem h (ofZ_mem_SL2ZR (loZ 1))
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have := H.pow_mem hm' n
    rwa [← pow_mul, ← map_pow, upZ_pow, mul_one] at this
  · have := H.pow_mem hn' m
    rwa [← pow_mul, ← map_pow, loZ_pow, mul_one, mul_comm] at this

/-! ### The commensurator lemma -/

/-- From the integrality of k·a², k·ac, k·c², k·b², k·bd, k·d² and det = 1, g is a real multiple of an integral
matrix. -/
theorem exists_int_of_products {a b c d : ℝ} (K : ℤ) (hK : K ≠ 0) (hdet : a * d - b * c = 1)
    {n₁ n₂ n₃ n₄ n₅ n₆ : ℤ} (E₁ : (K : ℝ) * a * c = n₁) (E₂ : (K : ℝ) * a ^ 2 = n₂) (E₃ : (K : ℝ) * c ^ 2 = n₃)
    (E₄ : (K : ℝ) * b * d = n₄) (E₅ : (K : ℝ) * b ^ 2 = n₅) (E₆ : (K : ℝ) * d ^ 2 = n₆) :
    ∃ (R : Matrix (Fin 2) (Fin 2) ℤ) (t : ℝ), t ≠ 0 ∧ !![a, b; c, d] = t • R.map (Int.cast : ℤ → ℝ) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  -- the ten products
  have Pab : ((n₂ * n₄ - n₁ * n₅ : ℤ) : ℝ) = (K : ℝ) ^ 2 * a * b := by
    push_cast; rw [← E₁, ← E₂, ← E₄, ← E₅]; linear_combination ((K : ℝ) ^ 2 * a * b) * hdet
  have Pad : ((n₂ * n₆ - n₁ * n₄ : ℤ) : ℝ) = (K : ℝ) ^ 2 * a * d := by
    push_cast; rw [← E₁, ← E₂, ← E₄, ← E₆]; linear_combination ((K : ℝ) ^ 2 * a * d) * hdet
  have Pcd : ((n₁ * n₆ - n₃ * n₄ : ℤ) : ℝ) = (K : ℝ) ^ 2 * c * d := by
    push_cast; rw [← E₁, ← E₃, ← E₄, ← E₆]; linear_combination ((K : ℝ) ^ 2 * c * d) * hdet
  have Pbc : ((n₁ * n₄ - n₅ * n₃ : ℤ) : ℝ) = (K : ℝ) ^ 2 * b * c := by
    push_cast; rw [← E₁, ← E₃, ← E₄, ← E₅]; linear_combination ((K : ℝ) ^ 2 * b * c) * hdet
  have Paa : ((K * n₂ : ℤ) : ℝ) = (K : ℝ) ^ 2 * a * a := by push_cast; rw [← E₂]; ring
  have Pac : ((K * n₁ : ℤ) : ℝ) = (K : ℝ) ^ 2 * a * c := by push_cast; rw [← E₁]; ring
  have Pcc : ((K * n₃ : ℤ) : ℝ) = (K : ℝ) ^ 2 * c * c := by push_cast; rw [← E₃]; ring
  have Pbd : ((K * n₄ : ℤ) : ℝ) = (K : ℝ) ^ 2 * b * d := by push_cast; rw [← E₄]; ring
  have Pbb : ((K * n₅ : ℤ) : ℝ) = (K : ℝ) ^ 2 * b * b := by push_cast; rw [← E₅]; ring
  have Pdd : ((K * n₆ : ℤ) : ℝ) = (K : ℝ) ^ 2 * d * d := by push_cast; rw [← E₆]; ring
  -- a generic finishing step
  have fin : ∀ (x : ℝ) (R : Matrix (Fin 2) (Fin 2) ℤ), x ≠ 0 →
      R.map (Int.cast : ℤ → ℝ) = ((K : ℝ) ^ 2 * x) • !![a, b; c, d] →
      ∃ (R : Matrix (Fin 2) (Fin 2) ℤ) (t : ℝ), t ≠ 0 ∧ !![a, b; c, d] = t • R.map (Int.cast : ℤ → ℝ) := by
    intro x R hx hR
    have hkx : (K : ℝ) ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hK') hx
    refine ⟨R, ((K : ℝ) ^ 2 * x)⁻¹, inv_ne_zero hkx, ?_⟩
    rw [hR, smul_smul, inv_mul_cancel₀ hkx, one_smul]
  by_cases ha : a ≠ 0
  · refine fin a !![K * n₂, n₂ * n₄ - n₁ * n₅; K * n₁, n₂ * n₆ - n₁ * n₄] ha ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Paa, Pab, Pac, Pad] <;> ring
  by_cases hb : b ≠ 0
  · refine fin b !![n₂ * n₄ - n₁ * n₅, K * n₅; n₁ * n₄ - n₅ * n₃, K * n₄] hb ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Pab, Pbb, Pbc, Pbd] <;> ring
  by_cases hc : c ≠ 0
  · refine fin c !![K * n₁, n₁ * n₄ - n₅ * n₃; K * n₃, n₁ * n₆ - n₃ * n₄] hc ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Pac, Pbc, Pcc, Pcd] <;> ring
  push Not at ha hb hc
  exfalso
  rw [ha, hb] at hdet
  simp at hdet

/-- If g·Tᵏ·g⁻¹ and g·Lᵏ·g⁻¹ lie in SL₂(ℤ) for some k ≥ 1, then g is a real multiple of an integral matrix. -/
theorem exists_isRep_of_conj {g : SL(2, ℝ)} {k : ℕ} (hk : 0 < k) (h₁ : g * ofZ (upZ k) * g⁻¹ ∈ SL2ZR)
    (h₂ : g * ofZ (loZ k) * g⁻¹ ∈ SL2ZR) : ∃ R, IsRep g R := by
  obtain ⟨γ₁, hγ₁⟩ := mem_SL2ZR_iff.1 h₁
  obtain ⟨γ₂, hγ₂⟩ := mem_SL2ZR_iff.1 h₂
  set a := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  have hdet : a * d - b * c = 1 := by
    have := g.2
    rw [det_fin_two] at this
    exact this
  have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] := eta_fin_two _
  have e₁ := congrArg (fun x : SL(2, ℝ) => (x : Matrix (Fin 2) (Fin 2) ℝ)) hγ₁
  have e₂ := congrArg (fun x : SL(2, ℝ) => (x : Matrix (Fin 2) (Fin 2) ℝ)) hγ₂
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_ofZ_eq_map, hg,
    adjugate_fin_two_of, coe_upZ, coe_loZ, upM, loM] at e₁ e₂
  have f : ∀ (γ : SL(2, ℤ)) (M : Matrix (Fin 2) (Fin 2) ℝ), (γ : Matrix (Fin 2) (Fin 2) ℤ).map Int.cast = M →
      ∀ i j, ((γ i j : ℤ) : ℝ) = M i j := fun γ M h i j => by rw [← h]; rfl
  have a00 := f _ _ e₁ 0 0
  have a01 := f _ _ e₁ 0 1
  have a10 := f _ _ e₁ 1 0
  have b00 := f _ _ e₂ 0 0
  have b01 := f _ _ e₂ 0 1
  have b10 := f _ _ e₂ 1 0
  simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct] at a00 a01 a10 b00 b01 b10
  have hK : ((k : ℤ) : ℝ) = (k : ℝ) := by push_cast; rfl
  obtain ⟨R, t, ht, hR⟩ := exists_int_of_products (k : ℤ) (by exact_mod_cast hk.ne') hdet
    (n₁ := 1 - γ₁ 0 0) (n₂ := γ₁ 0 1) (n₃ := -γ₁ 1 0) (n₄ := γ₂ 0 0 - 1) (n₅ := -γ₂ 0 1) (n₆ := γ₂ 1 0)
    (by push_cast; rw [a00]; linear_combination hdet) (by push_cast; rw [a01]; ring)
    (by push_cast; rw [a10]; ring) (by push_cast; rw [b00]; linear_combination -hdet)
    (by push_cast; rw [b01]; ring) (by push_cast; rw [b10]; ring)
  have hR0 : R.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR
    rw [det_smul, det_map_intCast, h0, Int.cast_zero, mul_zero, det_fin_two_of, hdet] at this
    exact one_ne_zero this
  exact ⟨R, hR0, t, by rw [hg, hR]⟩

/-- If H ∩ SL₂(ℤ) has finite index in both, every g normalizing H is a real multiple of an integral matrix. -/
theorem exists_isRep_of_normalizes {H : Subgroup SL(2, ℝ)} (h₁ : H.relIndex SL2ZR ≠ 0)
    (h₂ : SL2ZR.relIndex H ≠ 0) {g : SL(2, ℝ)} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : ∃ R, IsRep g R := by
  obtain ⟨k, hk, hT, hL⟩ := exists_unipotent_pow_mem h₁
  obtain ⟨m, hm, hm'⟩ := exists_pow_mem h₂ (hg _ hT)
  obtain ⟨n, hn, hn'⟩ := exists_pow_mem h₂ (hg _ hL)
  apply exists_isRep_of_conj (k := k * (m * n)) (Nat.mul_pos hk (Nat.mul_pos hm hn))
  · have := SL2ZR.pow_mem hm' n
    rw [← pow_mul, conj_pow, ← map_pow, upZ_pow] at this
    rw [show ((k * (m * n) : ℕ) : ℤ) = ((m * n : ℕ) : ℤ) * (k : ℤ) by push_cast; ring]
    exact this
  · have := SL2ZR.pow_mem hn' m
    rw [← pow_mul, conj_pow, ← map_pow, loZ_pow] at this
    rw [show ((k * (m * n) : ℕ) : ℤ) = ((n * m : ℕ) : ℤ) * (k : ℤ) by push_cast; ring]
    exact this

/-! ### Conjugation by integral matrices -/

theorem conj_mem_SL2ZR_of_Gamma {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma A.det.natAbs) :
    projSL (A.map (Int.cast : ℤ → ℝ)) * ofZ γ * (projSL (A.map (Int.cast : ℤ → ℝ)))⁻¹ ∈ SL2ZR ∧
      (projSL (A.map (Int.cast : ℤ → ℝ)))⁻¹ * ofZ γ * projSL (A.map (Int.cast : ℤ → ℝ)) ∈ SL2ZR := by
  set D := A.det
  have hDnat : ((A.det.natAbs : ℕ) : ℤ) = D := Int.natAbs_of_nonneg hA.le
  -- γ = 1 + D·t
  have hdvd : ∀ i j, D ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    rw [← hDnat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun (congrFun (congrArg (fun x : SL(2, ZMod A.det.natAbs) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod A.det.natAbs))) (CongruenceSubgroup.Gamma_mem'.1 hγ)) i) j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply, eq_intCast,
      Matrix.SpecialLinearGroup.coe_one] at this
    rw [Int.cast_sub, this]
    fin_cases i <;> fin_cases j <;> simp
  set t : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j => ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j -
    (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) / D
  have hγt : (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + D • t := by
    ext i j
    simp only [t, Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul, Int.mul_ediv_cancel' (hdvd i j)]
    ring
  have hDr : (0 : ℝ) < D := by exact_mod_cast hA
  have hs : Real.sqrt D ≠ 0 := (Real.sqrt_pos.2 hDr).ne'
  have hsq : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDr.le
  have hP : ((projSL (A.map (Int.cast : ℤ → ℝ)) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt D)⁻¹ • A.map (Int.cast : ℤ → ℝ) := coe_projSL_int hA
  have hPi : (((projSL (A.map (Int.cast : ℤ → ℝ)))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt D)⁻¹ • A.adjugate.map (Int.cast : ℤ → ℝ) := by
    rw [← projSL_adjugate hA, coe_projSL_int (by rwa [det_adjugate']), det_adjugate']
  have hAA : A * A.adjugate = D • (1 : Matrix (Fin 2) (Fin 2) ℤ) := mul_adjugate A
  have hAA' : A.adjugate * A = D • (1 : Matrix (Fin 2) (Fin 2) ℤ) := adjugate_mul A
  have hc : (Real.sqrt D)⁻¹ * (Real.sqrt D)⁻¹ * (D : ℝ) = 1 := by
    rw [← mul_inv, hsq, inv_mul_cancel₀ hDr.ne']
  constructor
  · apply mem_SL2ZR_of_eq_map (M := 1 + A * t * A.adjugate)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP, hPi, coe_ofZ_eq_map, hγt,
      Matrix.smul_mul, smul_mul_smul_comm, ← map_intCast_mul, ← map_intCast_mul]
    have : A * (1 + D • t) * A.adjugate = D • (1 + A * t * A.adjugate) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAA, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        Matrix.mul_assoc]
    rw [this, map_intCast_smul, smul_smul, hc, one_smul]
  · apply mem_SL2ZR_of_eq_map (M := 1 + A.adjugate * t * A)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP, hPi, coe_ofZ_eq_map, hγt,
      Matrix.smul_mul, smul_mul_smul_comm, ← map_intCast_mul, ← map_intCast_mul]
    have : A.adjugate * (1 + D • t) * A = D • (1 + A.adjugate * t * A) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAA', Matrix.mul_smul, Matrix.smul_mul, smul_add,
        Matrix.mul_assoc]
    rw [this, map_intCast_smul, smul_smul, hc, one_smul]

/-- Conjugation by projSL(A), A integral with det A > 0, preserves SL₂(ℤ) up to commensurability. -/
theorem commensurable_conj_SL2ZR {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) :
    (SL2ZR.map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))).toMonoidHom).Commensurable SL2ZR := by
  set g := projSL (A.map (Int.cast : ℤ → ℝ))
  have : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.2 hA.ne'⟩
  set Γ := toR (CongruenceSubgroup.Gamma A.det.natAbs)
  have hΓ : Γ.relIndex SL2ZR ≠ 0 := by
    rw [SL2ZR, relIndex_toR, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hΓ1 : Γ ≤ SL2ZR.map (MulAut.conj g).toMonoidHom ⊓ SL2ZR := by
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨⟨g⁻¹ * ofZ γ * g, (conj_mem_SL2ZR_of_Gamma hA hγ).2, ?_⟩, ofZ_mem_SL2ZR γ⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hΓ2 : Γ.map (MulAut.conj g).toMonoidHom ≤ SL2ZR.map (MulAut.conj g).toMonoidHom ⊓ SL2ZR := by
    rintro _ ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨⟨ofZ γ, ofZ_mem_SL2ZR γ, rfl⟩, (conj_mem_SL2ZR_of_Gamma hA hγ).1⟩
  constructor
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    intro h
    have := Subgroup.relIndex_dvd_of_le_left SL2ZR (hΓ1.trans inf_le_left)
    rw [h] at this
    exact hΓ (Nat.eq_zero_of_zero_dvd this)
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    have h1 : (Γ.map (MulAut.conj g).toMonoidHom).relIndex (SL2ZR.map (MulAut.conj g).toMonoidHom) ≠ 0 := by
      rw [Subgroup.relIndex_map_map_of_injective _ _ (fun x y h => (MulAut.conj g).injective h)]
      exact hΓ
    intro h
    have := Subgroup.relIndex_dvd_of_le_left (SL2ZR.map (MulAut.conj g).toMonoidHom) (hΓ2.trans inf_le_right)
    rw [h] at this
    exact h1 (Nat.eq_zero_of_zero_dvd this)

end NormalizerLean.Helling
