module

public import NormalizerDelta.GenLocal

@[expose] public section

/-!
# General modular curves: §F, finiteness (DLM26, Prop. 4.3(3), (4))

* Prop. 4.3(4): if m' ≡ m mod N·D and det m' = det m = D, then m' = m X with X = 1 − N·adj(m)E integral of
  determinant 1, X ≡ 1 mod N; so projSL(m)⁻¹ projSL(m') = X ∈ Γ(N).
* Prop. 4.3(3): if γ ≡ s mod N² and m s = s' m, then m γ = Y m with Y = s' + (N²/D)·m F adj(m) ≡ s' mod N
  (D ∣ N), so Y ∈ Γ(N) s' ⊆ Γ; apply this to m and to adj m.
* Finiteness and the bound: every element of Nor(Γ) is projSL m with m primitive of determinant D ∣ N, and
  m = σ diag(1, D) τ (Smith form, `exists_smith`).  Normalizing σ in its coset σΓ₀(D) changes τ by an element of
  SL₂(ℤ) (δ⁻¹Γ₀(D)δ ⊆ SL₂(ℤ)).  The class of m modulo Γ(N) is then determined by (D, σΓ₀(D), τ mod N), so
  [Nor(Γ) : Γ(N)] ≤ Σ_{D ∣ N} [SL₂(ℤ) : Γ₀(D)]·|SL₂(ℤ/N)| = Σ_{D ∣ N} ψ(D)·[SL₂(ℤ) : Γ(N)].
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem projSL_mul_ofZ {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) (τ : SL(2, ℤ)) :
    projSL ((A * (τ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℝ)) =
      projSL (A.map (Int.cast : ℤ → ℝ)) * ofZ τ := by
  have hAτ : (A * (τ : Matrix (Fin 2) (Fin 2) ℤ)).det = A.det := by rw [det_mul, τ.2, mul_one]
  apply Subtype.ext
  rw [coe_projSL_int (hAτ ▸ hA), hAτ, Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hA, coe_ofZ_eq_map,
    Matrix.smul_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_Gamma_of_eq {N : ℕ} {X : SL(2, ℤ)} {Z : Matrix (Fin 2) (Fin 2) ℤ}
    (h : (X : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • Z) : X ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem, h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero] <;> simp

/-! ### Prop. 4.3(4) -/

theorem projSL_inv_mul_mem_GammaR' {N : ℕ} {m m' : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det)
    (hdet' : m'.det = m.det) (hcong : ∀ i j, (N : ℤ) * m.det ∣ m i j - m' i j) :
    (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * projSL (m'.map (Int.cast : ℤ → ℝ)) ∈ GammaR N := by
  choose e he using hcong
  set E : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of e with hE
  set X : Matrix (Fin 2) (Fin 2) ℤ := 1 + (N : ℤ) • (-(adjugate m * E)) with hX
  have hmX : m * X = m' := by
    rw [hX, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    simp [hE]
    linear_combination he i j
  have hXdet : X.det = 1 := by
    have := congrArg Matrix.det hmX
    rw [det_mul, hdet'] at this
    exact mul_left_cancel₀ hdet.ne' (by linarith)
  set σ : SL(2, ℤ) := ⟨X, hXdet⟩
  have e1 : projSL (m'.map (Int.cast : ℤ → ℝ)) = projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ σ := by
    rw [← projSL_mul_ofZ hdet σ]
    congr 2
    exact hmX.symm
  rw [e1, inv_mul_cancel_left]
  exact ofZ_mem_toR (mem_Gamma_of_eq (Z := -(adjugate m * E)) rfl)

/-! ### Prop. 4.3(3) -/

theorem conj_mem_of_reps {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (S : Finset SL(2, ℤ)) (hS : ∀ γ ∈ Γ, ∃ s ∈ S, redSL (N ^ 2) γ = redSL (N ^ 2) s)
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hdvd : m.det ∣ N)
    (h : ∀ s ∈ S, projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ s * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈ toR Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ γ * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈ toR Γ := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hP
  obtain ⟨s, hsS, hs⟩ := hS γ hγ
  obtain ⟨s', hs'Γ, hs'⟩ := mem_toR.1 (h s hsS)
  have hrel_s : m * (s : Matrix (Fin 2) (Fin 2) ℤ) = (s' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    (projSL_mul_ofZ_eq_iff hdet s s').1 (by rw [hs', ← hP]; group)
  have hcong : ∀ i j, ((N : ℤ) ^ 2) ∣ γ i j - s i j := by
    intro i j
    have := congrArg (fun A : SL(2, ZMod (N ^ 2)) => (A : Matrix (Fin 2) (Fin 2) (ZMod (N ^ 2))) i j) hs
    simp only [redSL_apply] at this
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this.symm
    exact_mod_cast this
  choose F hF using hcong
  obtain ⟨k, hk⟩ := hdvd
  set Fm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of F with hFm
  set M : Matrix (Fin 2) (Fin 2) ℤ := m * Fm * adjugate m with hM
  set Y : Matrix (Fin 2) (Fin 2) ℤ := (s' : Matrix (Fin 2) (Fin 2) ℤ) + ((N : ℤ) * k) • M with hY
  have hγs : (γ : Matrix (Fin 2) (Fin 2) ℤ) = s + ((N : ℤ) ^ 2) • Fm := by
    ext i j; simp [hFm]; linear_combination hF i j
  have hYm : m * (γ : Matrix (Fin 2) (Fin 2) ℤ) = Y * m := by
    rw [hγs, Matrix.mul_add, hrel_s, Matrix.mul_smul, hY, Matrix.add_mul, Matrix.smul_mul, hM,
      Matrix.mul_assoc (m * Fm), Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 2
    rw [show ((N : ℤ) * k * m.det) = (N : ℤ) * (m.det * k) by ring, ← hk]
    ring
  have hYdet : Y.det = 1 := by
    have := congrArg Matrix.det hYm
    rw [det_mul, det_mul, γ.2, mul_one] at this
    exact (mul_right_cancel₀ hdet.ne' (by linarith : Y.det * m.det = 1 * m.det))
  set σY : SL(2, ℤ) := ⟨Y, hYdet⟩
  have hσY : σY ∈ Γ := by
    have hss : (s' : Matrix (Fin 2) (Fin 2) ℤ) * ((s'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h1 : σY * s'⁻¹ ∈ CongruenceSubgroup.Gamma N := by
      apply mem_Gamma_of_eq (Z := (k : ℤ) • (M * ((s'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
      rw [Matrix.SpecialLinearGroup.coe_mul]
      show Y * _ = _
      rw [hY, Matrix.add_mul, hss, Matrix.smul_mul, smul_smul]
    have := Subgroup.mul_mem _ (hΓ h1) hs'Γ
    rwa [inv_mul_cancel_right] at this
  have e : P * ofZ γ * P⁻¹ = ofZ σY := by
    have := (projSL_mul_ofZ_eq_iff hdet γ σY).2 hYm
    rw [hP, this]; group
  rw [e]
  exact ofZ_mem_toR hσY

theorem mem_normG_iff_of_reps' {N : ℕ} (hN0 : NeZero N) {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (S : Finset SL(2, ℤ)) (hSΓ : ∀ s ∈ S, s ∈ Γ)
    (hS : ∀ γ ∈ Γ, ∃ s ∈ S, redSL (N ^ 2) γ = redSL (N ^ 2) s)
    {m : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < m.det) (hdvd : m.det ∣ N) :
    projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR Γ) ↔
      ∀ s ∈ S, projSL (m.map (Int.cast : ℤ → ℝ)) * ofZ s * (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ ∈ toR Γ ∧
        (projSL (m.map (Int.cast : ℤ → ℝ)))⁻¹ * ofZ s * projSL (m.map (Int.cast : ℤ → ℝ)) ∈ toR Γ := by
  set P := projSL (m.map (Int.cast : ℤ → ℝ)) with hP
  constructor
  · intro hPn s hs
    have hsΓ := ofZ_mem_toR (hSΓ s hs)
    refine ⟨(Subgroup.mem_normalizer_iff.1 hPn _).1 hsΓ, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hPn) _).1 hsΓ
    rwa [inv_inv] at this
  · intro h
    have fwd : ∀ γ ∈ Γ, P * ofZ γ * P⁻¹ ∈ toR Γ := fun γ hγ =>
      conj_mem_of_reps hΓ S hS hdet hdvd (fun s hs => (h s hs).1) hγ
    have hadj : 0 < (adjugate m).det := by rwa [det_adjugate_two]
    have bwd : ∀ γ ∈ Γ, P⁻¹ * ofZ γ * P ∈ toR Γ := by
      intro γ hγ
      have := conj_mem_of_reps hΓ S hS hadj (by rwa [det_adjugate_two])
        (fun s hs => by rw [projSL_adjugate hdet, inv_inv]; exact (h s hs).2) hγ
      rwa [projSL_adjugate hdet, inv_inv] at this
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact fwd γ hγ
    · intro hy
      obtain ⟨γ₁, hγ₁, he⟩ := mem_toR.1 hy
      have := bwd γ₁ hγ₁
      rwa [he, show P⁻¹ * (P * y * P⁻¹) * P = y by group] at this

/-! ### Smith form of a primitive matrix -/

theorem exists_coprime_add_mul {a b d : ℤ} (hd : d ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → (p : ℤ) ∣ d → False) :
    ∃ t : ℤ, IsCoprime (a * t + b) d := by
  classical
  set S : Finset ℕ := d.natAbs.primeFactors.filter (fun q : ℕ => ¬ ((q : ℤ) ∣ a) ∧ ¬ ((q : ℤ) ∣ b)) with hS
  set t : ℤ := ∏ q ∈ S, (q : ℤ) with ht
  refine ⟨t, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  apply Nat.coprime_of_dvd
  intro q hq hq1 hq2
  have hq1' : (q : ℤ) ∣ a * t + b := Int.natCast_dvd.2 hq1
  have hq2' : (q : ℤ) ∣ d := Int.natCast_dvd.2 hq2
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hqt_iff : (q : ℤ) ∣ t ↔ q ∈ S := by
    constructor
    · intro hqt
      obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finset_prod_iff hqZ _).1 hqt
      have hr' := Finset.mem_filter.1 hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr'.1
      have : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).1 (Int.natCast_dvd_natCast.1 hqr)
      subst this
      exact hr
    · intro hqS
      exact Finset.dvd_prod_of_mem _ hqS
  by_cases hqa : (q : ℤ) ∣ a
  · exact h q hq hqa (by have := dvd_sub hq1' (dvd_mul_of_dvd_left hqa t); simpa using this) hq2'
  · by_cases hqb : (q : ℤ) ∣ b
    · have hqat : (q : ℤ) ∣ a * t := by have := dvd_sub hq1' hqb; simpa using this
      have hqt : (q : ℤ) ∣ t := (hqZ.dvd_or_dvd hqat).resolve_left hqa
      exact (Finset.mem_filter.1 (hqt_iff.1 hqt)).2.2 hqb
    · have hqS : q ∈ S :=
        Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hq, hq2, Int.natAbs_ne_zero.2 hd⟩, hqa, hqb⟩
      have hqt := hqt_iff.2 hqS
      exact hqb (by have := dvd_sub hq1' (dvd_mul_of_dvd_right hqt a); simpa using this)

/-- A primitive integer matrix of determinant D > 0 is σ·diag(1, D)·τ with σ, τ ∈ SL₂(ℤ). -/
theorem exists_smith {m : Matrix (Fin 2) (Fin 2) ℤ} (hD : 0 < m.det)
    (hprim : ∀ p : ℕ, p.Prime → ∃ i j, ¬ (p : ℤ) ∣ m i j) :
    ∃ σ τ : SL(2, ℤ), m = (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, m.det] * (τ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hW : 0 < m 0 0 * m 1 1 - m 0 1 * m 1 0 := by rwa [← det_fin_two]
  obtain ⟨σ₀, a, b, d, ha, hd, had, -, e00, e01, e10, e11⟩ :=
    exists_hermite (m 0 0) (m 0 1) (m 1 0) (m 1 1) hW
  have hdet : m.det = (a : ℤ) * d := by rw [det_fin_two]; exact had.symm
  have hm : m = (σ₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  have hprimH : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → (p : ℤ) ∣ d → False := by
    intro p hp hpa hpb hpd
    obtain ⟨i, j, hij⟩ := hprim p hp
    apply hij
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
    · rw [e00]; exact dvd_mul_of_dvd_right hpa _
    · rw [e01]; exact dvd_add (dvd_mul_of_dvd_right hpb _) (dvd_mul_of_dvd_right hpd _)
    · rw [e10]; exact dvd_mul_of_dvd_right hpa _
    · rw [e11]; exact dvd_add (dvd_mul_of_dvd_right hpb _) (dvd_mul_of_dvd_right hpd _)
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨t, u, v, huv⟩ := exists_coprime_add_mul (a := (a : ℤ)) (b := b) (d := d) hd0 hprimH
  set τ₀ := mkSL t (-1) 1 0 (by ring) with hτ₀
  set σ₁ := mkSL ((a : ℤ) * t + b) (-v) d u (by linear_combination huv) with hσ₁
  set τ₁ := mkSL 1 (u * a) 0 1 (by ring) with hτ₁
  have key : !![(a : ℤ), b; 0, d] * (τ₀ : Matrix (Fin 2) (Fin 2) ℤ) * (τ₁ : Matrix (Fin 2) (Fin 2) ℤ) =
      (σ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (a : ℤ) * d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hτ₀, hσ₁, hτ₁, mkSL, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (a : ℤ) * huv
    · ring
  have hττ : ((τ₀ * τ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((τ₀ * τ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key' := key
  simp only [Matrix.mul_assoc] at key'
  have h1 : m * ((τ₀ * τ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((σ₀ * σ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (a : ℤ) * d] := by
    rw [hm]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, key']
  refine ⟨σ₀ * σ₁, (τ₀ * τ₁)⁻¹, ?_⟩
  rw [hdet]
  calc m = m * ((τ₀ * τ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((τ₀ * τ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [Matrix.mul_assoc, hττ, Matrix.mul_one]
    _ = _ := by rw [h1]

/-- Moving σ to the chosen representative of σΓ₀(D) changes τ by an element of SL₂(ℤ). -/
theorem smith_coset (D : ℕ) (σ τ : SL(2, ℤ)) :
    ∃ τ' : SL(2, ℤ), (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (D : ℤ)] * (τ : Matrix (Fin 2) (Fin 2) ℤ) =
      (((QuotientGroup.mk σ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 D).out : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (D : ℤ)] * (τ' : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨⟨h, hh⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 D) σ
  set σs := (QuotientGroup.mk σ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 D).out with hσs
  -- σ = σs h⁻¹, and κ = h⁻¹ ∈ Γ₀(D)
  have hκ : h⁻¹ ∈ CongruenceSubgroup.Gamma0 D := Subgroup.inv_mem _ hh
  rw [CongruenceSubgroup.Gamma0_mem] at hκ
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hκ
  have hdetκ : (h⁻¹ : SL(2, ℤ)) 0 0 * (h⁻¹ : SL(2, ℤ)) 1 1 - (h⁻¹ : SL(2, ℤ)) 0 1 * (h⁻¹ : SL(2, ℤ)) 1 0 = 1 := by
    have := (h⁻¹).2; rwa [det_fin_two] at this
  set ρ := mkSL ((h⁻¹ : SL(2, ℤ)) 0 0) ((h⁻¹ : SL(2, ℤ)) 0 1 * D) z ((h⁻¹ : SL(2, ℤ)) 1 1)
    (by rw [hz] at hdetκ; linear_combination hdetκ) with hρ
  refine ⟨ρ * τ, ?_⟩
  have hσ : σ = σs * h⁻¹ := by rw [show σs = σ * h from hout]; group
  have hz' : (adjugate (h : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = D * z := by
    rw [← Matrix.SpecialLinearGroup.coe_inv]; exact hz
  have hκδ : ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (D : ℤ)] =
      !![1, 0; 0, (D : ℤ)] * (ρ : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hρ, mkSL, Matrix.mul_apply, Fin.sum_univ_two, hz'] <;> ring
  rw [hσ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc
    (σs : Matrix (Fin 2) (Fin 2) ℤ), hκδ]
  simp only [Matrix.mul_assoc]

theorem exists_key {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (g : NormG (toR Γ)) :
    ∃ D ∈ N.divisors, ∃ c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 D, ∃ τ : SL(2, ℤ),
      (g : SL(2, ℝ)) = projSL ((((c.out : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (D : ℤ)]).map
        (Int.cast : ℤ → ℝ)) * ofZ τ := by
  obtain ⟨m, hD, hDN, hprim, hg⟩ := normG_level_form' hΓ g.2
  obtain ⟨σ, τ, hm⟩ := exists_smith hD hprim
  set D := m.det.toNat with hDdef
  have hDD : (D : ℤ) = m.det := Int.toNat_of_nonneg hD.le
  have hDmem : D ∈ N.divisors := by
    rw [Nat.mem_divisors]
    refine ⟨?_, NeZero.ne N⟩
    have : (D : ℤ) ∣ N := by rw [hDD]; exact hDN
    exact_mod_cast this
  obtain ⟨τ', hτ'⟩ := smith_coset D σ τ
  refine ⟨D, hDmem, QuotientGroup.mk σ, τ', ?_⟩
  have hpos : 0 < ((((QuotientGroup.mk σ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 D).out : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (D : ℤ)]).det := by
    rw [det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, det_fin_two_of, hDD]; simpa using hD
  rw [hg, ← projSL_mul_ofZ hpos τ', ← hτ', hDD, ← hm]

/-! ### Finiteness and the bound -/

theorem sigma_key_inj {N : ℕ} {d₁ d₂ : N.divisors} {a₁ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d₁ : ℕ)}
    {a₂ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d₂ : ℕ)} {r₁ r₂ : SL(2, ZMod N)}
    (h : (⟨d₁, (a₁, r₁)⟩ : Σ d : N.divisors, (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d : ℕ)) × SL(2, ZMod N)) =
      ⟨d₂, (a₂, r₂)⟩) :
    (d₁ : ℕ) = d₂ ∧ (a₁.out : SL(2, ℤ)) = a₂.out ∧ r₁ = r₂ := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem relIndex_GammaR_normG_bound {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    (GammaR N).relIndex (NormG (toR Γ)) ≠ 0 ∧
      ((GammaR N).relIndex (NormG (toR Γ)) : ℚ) ≤ (∑ D ∈ N.divisors, psi D) * Nat.card SL(2, ZMod N) := by
  classical
  choose D hD c τ hspec using exists_key hΓ
  have hfinq : ∀ d : N.divisors, Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d : ℕ)) := by
    intro d
    have : NeZero (d : ℕ) := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩
    have h1 := Gamma0_index' (d : ℕ)
    have h2 := psi_pos (NeZero.ne (d : ℕ))
    apply Nat.finite_of_card_ne_zero
    intro h0
    have : ((CongruenceSubgroup.Gamma0 (d : ℕ)).index : ℚ) = 0 := by exact_mod_cast h0
    linarith
  set K := (GammaR N).subgroupOf (NormG (toR Γ)) with hK
  let T := Σ d : N.divisors, (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d : ℕ)) × SL(2, ZMod N)
  let f : NormG (toR Γ) ⧸ K → T := fun x => ⟨⟨D x.out, hD x.out⟩, (c x.out, redSL N (τ x.out))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨h1, h2, h3⟩ := sigma_key_inj (N := N) (d₁ := ⟨D x.out, hD x.out⟩) (d₂ := ⟨D y.out, hD y.out⟩)
      (a₁ := c x.out) (a₂ := c y.out) hxy
    simp only at h1
    have ex := hspec x.out
    have ey := hspec y.out
    generalize hσx : ((c x.out).out : SL(2, ℤ)) = σx at ex
    generalize hσy : ((c y.out).out : SL(2, ℤ)) = σy at ey
    have hσ : σx = σy := by rw [← hσx, ← hσy]; exact h2
    rw [h1, hσ] at ex
    have hmem : ((x.out : SL(2, ℝ)))⁻¹ * (y.out : SL(2, ℝ)) ∈ GammaR N := by
      rw [ex, ey]
      have e : (projSL (((σy : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, ((D y.out : ℕ) : ℤ)]).map
          (Int.cast : ℤ → ℝ)) * ofZ (τ x.out))⁻¹ *
          (projSL (((σy : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, ((D y.out : ℕ) : ℤ)]).map
          (Int.cast : ℤ → ℝ)) * ofZ (τ y.out)) = ofZ ((τ x.out)⁻¹ * τ y.out) := by
        simp only [map_mul, map_inv]; group
      rw [e]
      apply ofZ_mem_toR
      rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, h3, inv_mul_cancel]
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]
    exact QuotientGroup.eq.2 hmem
  have hfinQ : Finite (NormG (toR Γ) ⧸ K) := Finite.of_injective f hf
  have hcard : Nat.card (NormG (toR Γ) ⧸ K) ≤ Nat.card T := Nat.card_le_card_of_injective f hf
  refine ⟨?_, ?_⟩
  · show Nat.card (NormG (toR Γ) ⧸ K) ≠ 0
    exact Nat.card_ne_zero.2 ⟨inferInstance, hfinQ⟩
  · have hT : Nat.card T = ∑ d : N.divisors,
        Nat.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d : ℕ)) * Nat.card SL(2, ZMod N) := by
      rw [Nat.card_sigma]
      congr 1
      ext d
      rw [Nat.card_prod]
    have h1 : ((GammaR N).relIndex (NormG (toR Γ)) : ℚ) ≤ Nat.card T := by exact_mod_cast hcard
    rw [hT] at h1
    push_cast at h1
    calc ((GammaR N).relIndex (NormG (toR Γ)) : ℚ)
        ≤ ∑ d : N.divisors, (Nat.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (d : ℕ)) : ℚ) *
            Nat.card SL(2, ZMod N) := h1
      _ = ∑ D ∈ N.divisors, psi D * Nat.card SL(2, ZMod N) := by
          rw [← Finset.sum_coe_sort N.divisors]
          congr 1
          ext d
          have : NeZero (d : ℕ) := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩
          rw [← Gamma0_index' (d : ℕ)]
          rfl
      _ = (∑ D ∈ N.divisors, psi D) * Nat.card SL(2, ZMod N) := by rw [Finset.sum_mul]

theorem card_BG_mul_relIndex {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    Nat.card (BG (toR Γ)) * (CongruenceSubgroup.Gamma N).relIndex Γ = (GammaR N).relIndex (NormG (toR Γ)) := by
  have h1 : GammaR N ≤ toR Γ := Subgroup.map_mono hΓ
  have h2 : toR Γ ≤ NormG (toR Γ) := Subgroup.le_normalizer
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2, mul_comm, GammaR, relIndex_toR]
  rfl

theorem finite_BG' {N : ℕ} (hN0 : NeZero N) {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    Finite (BG (toR Γ)) := by
  apply Nat.finite_of_card_ne_zero
  intro h0
  have := card_BG_mul_relIndex hΓ
  rw [h0, zero_mul] at this
  exact (relIndex_GammaR_normG_bound hΓ).1 this.symm

theorem card_BG_le' {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) :
    (Nat.card (BG (toR Γ)) : ℚ) ≤ Γ.index * ∑ D ∈ N.divisors, psi D := by
  have hrel := card_BG_mul_relIndex hΓ
  have hidx := Subgroup.relIndex_mul_index hΓ
  rw [index_Gamma_eq_card] at hidx
  have hr0 : (CongruenceSubgroup.Gamma N).relIndex Γ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hidx
    exact Nat.card_pos.ne' hidx.symm
  have hb := (relIndex_GammaR_normG_bound hΓ).2
  rw [← hrel, ← hidx] at hb
  push_cast at hb
  have hr : (0 : ℚ) < (CongruenceSubgroup.Gamma N).relIndex Γ := by exact_mod_cast Nat.pos_of_ne_zero hr0
  have : (Nat.card (BG (toR Γ)) : ℚ) * (CongruenceSubgroup.Gamma N).relIndex Γ ≤
      (Γ.index * ∑ D ∈ N.divisors, psi D) * (CongruenceSubgroup.Gamma N).relIndex Γ := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hr

end

end NormalizerLean
