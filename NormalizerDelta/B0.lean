module

public import NormalizerDelta.SigmaHCount

@[expose] public section

/-!
# §B: B₀(N) of the sporadic-points paper

g ↦ normSL g = (det g)^{-1/2} g is a homomorphism GL₂⁺(ℚ) → SL₂(ℝ), equal to the inclusion on SL₂(ℤ).
* g ∈ Γ₀(N) ≤ GL₂⁺(ℚ) iff det g = 1 and normSL g ∈ Γ₀(N) (`mem_Gamma0Q_iff`); hence g normalizes Γ₀(N) in
  GL₂⁺(ℚ) iff normSL g normalizes Γ₀(N) in SL₂(ℝ) (`mem_Norm0Q_iff`).
* Onto B(N): by Newman, g ∈ Nor_{SL₂(ℝ)}(Γ₀(N)) is normSL of the rational matrix ε[[aeh, b], [Nc, deh]].
* Kernel: normSL g ∈ Γ₀(N) iff g = γ·q with γ ∈ Γ₀(N), q ∈ ℚ^× (q = g₀₀γ₁₁ − g₀₁γ₁₀ = √det g is rational).
* The centre of GL₂⁺(ℚ) is ℚ^× (commute with [[1, 1], [0, 1]] and [[1, 0], [1, 1]]).
* The literal quotient by Γ₀(N) is infinite: det(2ᵏ) = 4ᵏ separates the classes of the scalars 2ᵏ.
-/

open Matrix MatrixGroups Pointwise

namespace NormalizerLean

noncomputable section

/-- The rational matrix of g ∈ GL₂⁺(ℚ). -/
abbrev matQ (g : GLPos (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ := ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)

/-- The real matrix of g ∈ GL₂⁺(ℚ). -/
abbrev matR (g : GLPos (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℝ := (matQ g).map (Rat.cast : ℚ → ℝ)

theorem det_matQ_pos (g : GLPos (Fin 2) ℚ) : 0 < (matQ g).det := by
  have := (mem_glpos (g : GL (Fin 2) ℚ)).1 g.2
  simpa using this

theorem matQ_mul (g h : GLPos (Fin 2) ℚ) : matQ (g * h) = matQ g * matQ h := rfl

theorem matQ_one : matQ 1 = 1 := rfl

theorem det_matR (g : GLPos (Fin 2) ℚ) : (matR g).det = ((matQ g).det : ℝ) := by
  have := RingHom.map_det (Rat.castHom ℝ) (matQ g)
  simpa using this.symm

theorem det_matR_pos (g : GLPos (Fin 2) ℚ) : 0 < (matR g).det := by
  rw [det_matR]; exact_mod_cast det_matQ_pos g

theorem matR_mul (g h : GLPos (Fin 2) ℚ) : matR (g * h) = matR g * matR h := by
  show (matQ (g * h)).map _ = (matQ g).map _ * (matQ h).map _
  rw [matQ_mul]
  exact Matrix.map_mul (f := Rat.castHom ℝ)

theorem coe_normSL (g : GLPos (Fin 2) ℚ) :
    ((normSL g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt ((matQ g).det : ℝ))⁻¹ • matR g := by
  rw [normSL, coe_projSL _ (det_matR_pos g), det_matR]

theorem normSL_mul (g h : GLPos (Fin 2) ℚ) : normSL (g * h) = normSL g * normSL h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_normSL, coe_normSL, coe_normSL, matR_mul, matQ_mul,
    Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  push_cast
  rw [Real.sqrt_mul (by exact_mod_cast (det_matQ_pos g).le), mul_inv]

theorem normSL_one : normSL 1 = 1 := by
  apply Subtype.ext
  rw [coe_normSL, matQ_one]
  show _ • (1 : Matrix (Fin 2) (Fin 2) ℚ).map _ = _
  simp

/-- normSL as a homomorphism. -/
def normSLHom : GLPos (Fin 2) ℚ →* SL(2, ℝ) where
  toFun := normSL
  map_one' := normSL_one
  map_mul' := normSL_mul

theorem matQ_toGLPosQ (γ : SL(2, ℤ)) :
    matQ (toGLPosQ γ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  simp

theorem det_toGLPosQ (γ : SL(2, ℤ)) : (matQ (toGLPosQ γ)).det = 1 := by
  rw [matQ_toGLPosQ]
  have := RingHom.map_det (Int.castRingHom ℚ) (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Matrix.SpecialLinearGroup.det_coe, map_one] at this
  exact this.symm

theorem normSL_toGLPosQ (γ : SL(2, ℤ)) : normSL (toGLPosQ γ) = ofZ γ := by
  apply Subtype.ext
  rw [coe_normSL, det_toGLPosQ]
  simp only [Rat.cast_one, Real.sqrt_one, inv_one, one_smul]
  ext i j
  simp [matR, Matrix.SpecialLinearGroup.map_apply_coe]

theorem toGLPosQ_injective : Function.Injective toGLPosQ := by
  intro a b h
  ext i j
  have := congrArg (fun g => matQ g i j) h
  simp only [matQ_toGLPosQ, map_apply] at this
  exact_mod_cast this

/-! ### Γ₀(N) and its normalizer in GL₂⁺(ℚ) -/

theorem mem_Gamma0Q_iff {N : ℕ} {X : GLPos (Fin 2) ℚ} :
    X ∈ Gamma0Q N ↔ (matQ X).det = 1 ∧ normSL X ∈ Gamma0R N := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨det_toGLPosQ γ, by rw [normSL_toGLPosQ]; exact Subgroup.mem_map_of_mem _ hγ⟩
  · rintro ⟨hdet, γ, hγ, hXγ⟩
    refine ⟨γ, hγ, ?_⟩
    have hm := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) hXγ
    simp only [coe_normSL, hdet, Rat.cast_one, Real.sqrt_one, inv_one, one_smul] at hm
    apply Subtype.ext; apply Units.ext
    ext i j
    have := congrFun (congrFun hm i) j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
      eq_intCast] at this
    have h2 : ((matQ (toGLPosQ γ) i j : ℚ) : ℝ) = ((matQ X i j : ℚ) : ℝ) := by
      rw [matQ_toGLPosQ, map_apply]; push_cast; exact this
    exact Rat.cast_injective h2

theorem det_conj (g X : GLPos (Fin 2) ℚ) : (matQ (g * X * g⁻¹)).det = (matQ X).det := by
  have h1 : (matQ g⁻¹).det * (matQ g).det = 1 := by
    rw [← Matrix.det_mul, ← matQ_mul, inv_mul_cancel, matQ_one, Matrix.det_one]
  rw [matQ_mul, matQ_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (matQ X).det * h1

theorem normSL_inv (g : GLPos (Fin 2) ℚ) : normSL g⁻¹ = (normSL g)⁻¹ :=
  map_inv normSLHom g

theorem mem_Norm0Q_iff {N : ℕ} {g : GLPos (Fin 2) ℚ} : g ∈ Norm0Q N ↔ normSL g ∈ Norm0 N := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg Y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have hX : toGLPosQ γ ∈ Gamma0Q N := ⟨γ, hγ, rfl⟩
      have h1 := (mem_Gamma0Q_iff.1 ((hg _).1 hX)).2
      rwa [normSL_mul, normSL_mul, normSL_inv, normSL_toGLPosQ] at h1
    · intro hY
      obtain ⟨γ, hγ, hγY⟩ := hY
      have hX : toGLPosQ γ ∈ Gamma0Q N := ⟨γ, hγ, rfl⟩
      have h2 : g⁻¹ * toGLPosQ γ * g ∈ Gamma0Q N := by
        apply (hg _).2
        rw [show g * (g⁻¹ * toGLPosQ γ * g) * g⁻¹ = toGLPosQ γ by group]
        exact hX
      have h3 := (mem_Gamma0Q_iff.1 h2).2
      rw [normSL_mul, normSL_mul, normSL_inv, normSL_toGLPosQ] at h3
      have hγY' : ofZ γ = normSL g * Y * (normSL g)⁻¹ := hγY
      rw [hγY'] at h3
      simpa [mul_assoc] using h3
  · intro hg X
    rw [mem_Gamma0Q_iff, mem_Gamma0Q_iff, det_conj, normSL_mul, normSL_mul, normSL_inv]
    exact and_congr_right fun _ => hg _

/-! ### Scalars and the centre -/

theorem det_smul_one_ne_zero {q : ℚ} (hq : q ≠ 0) : (q • (1 : Matrix (Fin 2) (Fin 2) ℚ)).det ≠ 0 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]; simpa using hq

/-- The scalar q ∈ GL₂⁺(ℚ). -/
def scalQ (q : ℚ) (hq : q ≠ 0) : GLPos (Fin 2) ℚ :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (q • (1 : Matrix (Fin 2) (Fin 2) ℚ)) (det_smul_one_ne_zero hq), by
    rw [mem_glpos, GeneralLinearGroup.val_det_apply]
    change 0 < (q • (1 : Matrix (Fin 2) (Fin 2) ℚ)).det
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    positivity⟩

theorem matQ_scalQ {q : ℚ} (hq : q ≠ 0) : matQ (scalQ q hq) = q • (1 : Matrix (Fin 2) (Fin 2) ℚ) := rfl

theorem GLPos_ext {g h : GLPos (Fin 2) ℚ} (H : matQ g = matQ h) : g = h :=
  Subtype.ext (Units.ext H)

theorem mem_center_of_smul {z : GLPos (Fin 2) ℚ} {c : ℚ} (hz : matQ z = c • 1) :
    z ∈ Subgroup.center (GLPos (Fin 2) ℚ) :=
  Subgroup.mem_center_iff.2 fun g => GLPos_ext (by rw [matQ_mul, matQ_mul, hz]; simp)

theorem scalQ_mem_center {q : ℚ} (hq : q ≠ 0) : scalQ q hq ∈ Subgroup.center (GLPos (Fin 2) ℚ) :=
  mem_center_of_smul (matQ_scalQ hq)

theorem mem_center_GLPos_iff' (g : GLPos (Fin 2) ℚ) :
    g ∈ Subgroup.center (GLPos (Fin 2) ℚ) ↔
      ∃ c : ℚ, c ≠ 0 ∧ ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = c • 1 := by
  constructor
  · intro hg
    have hT := Subgroup.mem_center_iff.1 hg (toGLPosQ (mkSL 1 1 0 1 (by norm_num)))
    have hU := Subgroup.mem_center_iff.1 hg (toGLPosQ (mkSL 1 0 1 1 (by norm_num)))
    have hT' := congrArg matQ hT
    have hU' := congrArg matQ hU
    rw [matQ_mul, matQ_mul, matQ_toGLPosQ] at hT' hU'
    have t00 := congrFun (congrFun hT' 0) 0
    have t01 := congrFun (congrFun hT' 0) 1
    have u00 := congrFun (congrFun hU' 0) 0
    simp [mkSL, Matrix.mul_apply, Fin.sum_univ_two] at t00 t01 u00
    have hdet := det_matQ_pos g
    refine ⟨matQ g 0 0, ?_, ?_⟩
    · intro h0
      rw [det_fin_two, h0] at hdet
      simp_all
    · ext i j; fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨c, -, hc⟩
    exact mem_center_of_smul hc

theorem matR_of_smul {z : GLPos (Fin 2) ℚ} {c : ℚ} (hc : matQ z = c • 1) :
    matR z = (c : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [matR, hc]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem normSL_of_smul {z : GLPos (Fin 2) ℚ} {c : ℚ} (hc0 : c ≠ 0) (hc : matQ z = c • 1) :
    normSL z = 1 ∨ normSL z = -1 := by
  have hdet : (matQ z).det = c ^ 2 := by
    rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · right
    apply Subtype.ext
    rw [coe_normSL, hdet, matR_of_smul hc, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, smul_smul]
    push_cast
    rw [Real.sqrt_sq_eq_abs, abs_of_neg (by exact_mod_cast hneg), inv_neg, neg_mul,
      inv_mul_cancel₀ hcr, neg_one_smul]
  · left
    apply Subtype.ext
    rw [coe_normSL, hdet, matR_of_smul hc, Matrix.SpecialLinearGroup.coe_one, smul_smul]
    push_cast
    rw [Real.sqrt_sq (by exact_mod_cast hpos.le), inv_mul_cancel₀ hcr, one_smul]

theorem normSL_mem_of_center {N : ℕ} {z : GLPos (Fin 2) ℚ}
    (hz : z ∈ Subgroup.center (GLPos (Fin 2) ℚ)) : normSL z ∈ Gamma0R N := by
  obtain ⟨c, hc0, hc⟩ := (mem_center_GLPos_iff' z).1 hz
  rcases normSL_of_smul hc0 hc with h | h <;> rw [h]
  · exact one_mem _
  · exact neg_one_mem_Gamma0R N

/-! ### The kernel: Γ₀(N) · ℚ^× -/

theorem normSL_mem_Gamma0R_iff {N : ℕ} {g : GLPos (Fin 2) ℚ} :
    normSL g ∈ Gamma0R N ↔ g ∈ Gamma0Q N ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by
  constructor
  · rintro ⟨γ, hγ, hγg⟩
    have hd := det_matQ_pos g
    set s := Real.sqrt ((matQ g).det : ℝ) with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hm := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ)) hγg
    simp only [coe_normSL] at hm
    have hent : ∀ i j, ((matQ g i j : ℚ) : ℝ) = s * (γ i j : ℝ) := by
      intro i j
      have := congrFun (congrFun hm i) j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply,
        eq_intCast, Matrix.smul_apply, smul_eq_mul] at this
      rw [← hsdef] at this
      field_simp at this
      linarith
    set q : ℚ := matQ g 0 0 * γ 1 1 - matQ g 0 1 * γ 1 0 with hqdef
    have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rwa [det_fin_two] at this
    have hq : (q : ℝ) = s := by
      rw [hqdef]; push_cast; rw [hent 0 0, hent 0 1]
      have : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ℝ) = 1 := by exact_mod_cast hdetγ
      push_cast at this
      linear_combination s * this
    have hq0 : q ≠ 0 := by
      intro h0; rw [h0, Rat.cast_zero] at hq; exact hs.ne' hq.symm
    have hg : g = toGLPosQ γ * scalQ q hq0 := by
      apply GLPos_ext
      rw [matQ_mul, matQ_toGLPosQ, matQ_scalQ]
      ext i j
      have h1 := hent i j
      rw [← hq] at h1
      have h2 : matQ g i j = q * γ i j := by exact_mod_cast h1
      simp [h2, mul_comm]
    rw [hg]
    exact Subgroup.mul_mem_sup ⟨γ, hγ, rfl⟩ (scalQ_mem_center hq0)
  · intro hg
    have : g ∈ (Gamma0Q N : Set (GLPos (Fin 2) ℚ)) *
        ((Subgroup.center (GLPos (Fin 2) ℚ) : Subgroup (GLPos (Fin 2) ℚ)) : Set (GLPos (Fin 2) ℚ)) := by
      rw [← Subgroup.mul_normal]; exact hg
    obtain ⟨y, hy, z, hz, rfl⟩ := this
    rw [normSL_mul]
    exact mul_mem (mem_Gamma0Q_iff.1 hy).2 (normSL_mem_of_center hz)

/-! ### The map to B(N) -/

/-- g ↦ normSL g, Nor_{GL₂⁺(ℚ)}(Γ₀(N)) → Nor_{SL₂(ℝ)}(Γ₀(N)). -/
def psi0 (N : ℕ) : Norm0Q N →* Norm0 N where
  toFun g := ⟨normSL g, mem_Norm0Q_iff.1 g.2⟩
  map_one' := Subtype.ext normSL_one
  map_mul' x y := Subtype.ext (normSL_mul x y)

/-- Nor_{GL₂⁺(ℚ)}(Γ₀(N)) → B(N). -/
def phi0 (N : ℕ) : Norm0Q N →* B N :=
  (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N))).comp (psi0 N)

theorem phi0_surjective (N : ℕ) [NeZero N] : Function.Surjective (phi0 N) := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := newman' hg
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hh := hPart_pos N
  set h := hPart N with hhdef
  have hNq : (N : ℚ) = nPart N * (h : ℚ) ^ 2 := by exact_mod_cast hNnh.symm
  obtain ⟨ε', hε'r, hε'2⟩ : ∃ ε' : ℚ, (ε' : ℝ) = ε ∧ ε' ^ 2 = 1 := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩
  set W : Matrix (Fin 2) (Fin 2) ℚ := ε' • !![(a : ℚ) * e * h, b; N * c, d * e * h] with hWdef
  have hWdet : W.det = (h : ℚ) ^ 2 * e := by
    rw [hWdef, Matrix.det_smul, Fintype.card_fin, det_fin_two_of, hε'2, one_mul, hNq]
    have : ((a * d * (e : ℤ) ^ 2 - b * c * (nPart N : ℤ) : ℤ) : ℚ) = (e : ℚ) := by exact_mod_cast hdet
    push_cast at this
    linear_combination (h : ℚ) ^ 2 * this
  have hWpos : 0 < W.det := by
    rw [hWdet]
    have : (0 : ℚ) < e := by exact_mod_cast he0
    positivity
  let G : GLPos (Fin 2) ℚ := ⟨GeneralLinearGroup.mkOfDetNeZero W hWpos.ne', by
    rw [mem_glpos, GeneralLinearGroup.val_det_apply]; exact hWpos⟩
  have hGW : matQ G = W := rfl
  have hGg : normSL G = g := by
    apply Subtype.ext
    rw [coe_normSL, hgm]
    unfold matR
    rw [hGW, hWdet]
    push_cast
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have her : (0 : ℝ) < e := by exact_mod_cast he0
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hhr.le]
    have hse : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 her).ne'
    ext i j; fin_cases i <;> fin_cases j <;> simp [hWdef, ← hε'r] <;> field_simp <;> ring
  have hG : G ∈ Norm0Q N := mem_Norm0Q_iff.2 (hGg ▸ hg)
  refine ⟨⟨G, hG⟩, ?_⟩
  show (QuotientGroup.mk (psi0 N ⟨G, hG⟩) : B N) = QuotientGroup.mk ⟨g, hg⟩
  congr 1
  exact Subtype.ext hGg

theorem B0_equiv' (N : ℕ) [NeZero N] :
    ∃ φ : Norm0Q N →* B N, Function.Surjective φ ∧
      φ.ker = (Gamma0Q N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (Norm0Q N) ∧
      ∀ g : Norm0Q N, (φ g).IsClassOf (normSL g) := by
  refine ⟨phi0 N, phi0_surjective N, ?_, fun g => ⟨mem_Norm0Q_iff.1 g.2, rfl⟩⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← normSL_mem_Gamma0R_iff]
  show (QuotientGroup.mk (psi0 N g) : B N) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

/-! ### The literal quotient is infinite -/

theorem infinite_B0lit' (N : ℕ) [NeZero N] : Infinite (B0lit N) := by
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  set s := scalQ 2 h2
  have hs : s ∈ Norm0Q N := Subgroup.center_le_normalizer _ (scalQ_mem_center h2)
  have hdet : ∀ k : ℕ, (matQ (s ^ k)).det = 4 ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, matQ_one, Matrix.det_one, pow_zero]
    | succ k ih =>
      rw [pow_succ, matQ_mul, Matrix.det_mul, ih, matQ_scalQ, Matrix.det_smul, Matrix.det_one,
        Fintype.card_fin, pow_succ]
      norm_num [pow_succ]
  refine Infinite.of_injective
    (fun k : ℕ => (QuotientGroup.mk (⟨s ^ k, pow_mem hs k⟩ : Norm0Q N) : B0lit N)) ?_
  intro k l hkl
  have h1 := QuotientGroup.eq.1 hkl
  rw [Subgroup.mem_subgroupOf] at h1
  have h3 := (mem_Gamma0Q_iff.1 h1).1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  have hinv : (matQ (s ^ k)⁻¹).det * (matQ (s ^ k)).det = 1 := by
    rw [← Matrix.det_mul, ← matQ_mul, inv_mul_cancel, matQ_one, Matrix.det_one]
  rw [matQ_mul, Matrix.det_mul, hdet] at h3
  rw [hdet] at hinv
  have h4 : (4 : ℚ) ^ k = 4 ^ l := by
    have h5 : (matQ (s ^ k)⁻¹).det ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    exact mul_left_cancel₀ h5 (hinv.trans h3.symm)
  exact pow_right_injective₀ (by norm_num) (by norm_num) h4

end

end NormalizerLean
