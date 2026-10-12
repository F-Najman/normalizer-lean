import NormalizerLean.T1General
import NormalizerLean.Index

/-!
# |C(N)| = ψ(N)/ψ(n)

C(N) = D⁻¹Γ₀(n)D / Γ₀(N).  Conjugation by D = diag(h, 1) identifies [D⁻¹Γ₀(n)D : Γ₀(N)] with
[Γ₀(n) : H], H = {A ∈ SL₂(ℤ) : h ∣ A₀₁, nh ∣ A₁₀}; and [Γ₀(nh) : H] = h (representatives
[[1, j], [0, 1]], 0 ≤ j < h), [Γ₀(n) : Γ₀(nh)] = ψ(nh)/ψ(n), h·ψ(nh) = ψ(nh²) = ψ(N).
-/

open Matrix MatrixGroups CongruenceSubgroup

namespace NormalizerLean

noncomputable section

/-! ### Cardinality of the image of a subgroup in a quotient -/

theorem card_map_mk' {G : Type*} [Group G] (N' : Subgroup G) [N'.Normal] (K : Subgroup G) :
    Nat.card (K.map (QuotientGroup.mk' N')) = N'.relIndex K := by
  let φ := (QuotientGroup.mk' N').comp K.subtype
  have hrange : φ.range = K.map (QuotientGroup.mk' N') := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = N'.subgroupOf K := by
    ext x
    simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Subgroup.relIndex, Subgroup.index_eq_card]

/-! ### The subgroup H -/

/-- H = {A ∈ SL₂(ℤ) : h ∣ A₀₁, M ∣ A₁₀}. -/
def GammaUp (M h : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {A | (h : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
    (M : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    exact ⟨dvd_add (dvd_mul_of_dvd_right hB1 _) (dvd_mul_of_dvd_left hA1 _),
      dvd_add (dvd_mul_of_dvd_left hA2 _) (dvd_mul_of_dvd_right hB2 _)⟩
  one_mem' := by simp
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    simp [hA1, hA2]

theorem mem_GammaUp {M h : ℕ} {A : SL(2, ℤ)} :
    A ∈ GammaUp M h ↔ (h : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
      (M : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := Iff.rfl

theorem Gamma0_le_of_dvd {a b : ℕ} (hab : a ∣ b) : Gamma0 b ≤ Gamma0 a := fun _ hA =>
  mem_Gamma0_iff_dvd.2 (dvd_trans (Int.natCast_dvd_natCast.2 hab) (mem_Gamma0_iff_dvd.1 hA))

theorem GammaUp_le (M h : ℕ) : GammaUp M h ≤ Gamma0 M :=
  fun _ hA => mem_Gamma0_iff_dvd.2 hA.2

/-- [[1, j], [0, 1]]. -/
def upU (j : ℤ) : SL(2, ℤ) := ⟨!![1, j; 0, 1], by rw [det_fin_two_of]; ring⟩

theorem inv_mul_apply_01 (r γ : SL(2, ℤ)) :
    ((r⁻¹ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      (r : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 -
        (r : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two,
    Matrix.mul_apply]
  simp [Fin.sum_univ_two]
  ring

/-- [Γ₀(M) : H] = h when h ∣ M. -/
theorem relIndex_GammaUp {M h : ℕ} (hh : h ≠ 0) (hhM : h ∣ M) :
    (GammaUp M h).relIndex (Gamma0 M) = h := by
  have : NeZero h := ⟨hh⟩
  let U : ℕ → Gamma0 M := fun j => ⟨upU j, mem_Gamma0_iff_dvd.2 ⟨0, by simp [upU]⟩⟩
  have hUmat : ∀ j : ℕ, ((U j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (j : ℤ); 0, 1] :=
    fun j => rfl
  have hmk : ∀ x y : Gamma0 M,
      (QuotientGroup.mk x : Gamma0 M ⧸ (GammaUp M h).subgroupOf (Gamma0 M)) = QuotientGroup.mk y ↔
        (h : ℤ) ∣ ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
            ((y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 -
          ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
            ((y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      mem_GammaUp, inv_mul_apply_01, inv_mul_apply_10]
    constructor
    · exact fun h' => h'.1
    · intro h'
      refine ⟨h', ?_⟩
      exact dvd_sub (dvd_mul_of_dvd_right (mem_Gamma0_iff_dvd.1 y.2) _)
        (dvd_mul_of_dvd_left (mem_Gamma0_iff_dvd.1 x.2) _)
  let F : Fin h → Gamma0 M ⧸ (GammaUp M h).subgroupOf (Gamma0 M) :=
    fun j => QuotientGroup.mk (U j)
  have hbij : Function.Bijective F := by
    refine ⟨fun i j hij => ?_, fun q => ?_⟩
    · have := (hmk _ _).1 hij
      rw [hUmat, hUmat] at this
      simp only [of_apply, cons_val', cons_val_one, head_cons, cons_val_zero, empty_val',
        cons_val_fin_one, one_mul, mul_one] at this
      exact Fin.ext (eq_of_dvd_sub i.2 j.2 this)
    · induction q using QuotientGroup.induction_on with
      | H γ =>
        set a := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        set b := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        set c := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
        set d := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        have hdet : a * d - b * c = 1 := by
          have := (γ : SL(2, ℤ)).2
          rwa [det_fin_two] at this
        have hc : (h : ℤ) ∣ c := dvd_trans (Int.natCast_dvd_natCast.2 hhM) (mem_Gamma0_iff_dvd.1 γ.2)
        let j := ((b : ZMod h) * (a : ZMod h)).val
        refine ⟨⟨j, ZMod.val_lt _⟩, ?_⟩
        show QuotientGroup.mk (U j) = _
        rw [hmk, hUmat]
        simp only [of_apply, cons_val', cons_val_one, head_cons, cons_val_zero, empty_val',
          cons_val_fin_one, one_mul]
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        obtain ⟨c', hc'⟩ := hc
        have hdet' : ((a * d : ℤ) : ZMod h) = 1 := by
          rw [show a * d = 1 + b * c by linarith, hc']
          push_cast
          rw [ZMod.natCast_self]
          ring
        push_cast at hdet' ⊢
        rw [ZMod.natCast_zmod_val]
        linear_combination (-b) * hdet'
  rw [Subgroup.relIndex, Subgroup.index_eq_card, ← Nat.card_eq_of_bijective F hbij,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### ψ(n h²) = h ψ(n h) -/

theorem psi_mul_of_primeFactors_subset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : b.primeFactors ⊆ a.primeFactors) : psi (a * b) = b * psi a := by
  unfold psi
  rw [Nat.primeFactors_mul ha hb, Finset.union_eq_left.2 h]
  push_cast
  ring

/-! ### Conjugation by D -/

theorem Gamma0R_map_conj (N : ℕ) [NeZero N] :
    (Gamma0R N).map (MulAut.conj (Dsl N)).toMonoidHom =
      (GammaUp (nPart N * hPart N) (hPart N)).map
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) := by
  have hNnh := hPart_sq_mul_nPart N (NeZero.ne N)
  have hh0 : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  have hNr : (N : ℝ) = nPart N * (hPart N) ^ 2 := by exact_mod_cast hNnh.symm
  have hD := coe_Dsl N
  have hDinv := coe_inv_of_coe_eq_smul hD
  have hs : Real.sqrt (hPart N) * Real.sqrt (hPart N) = hPart N :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hsq : (Real.sqrt (hPart N))⁻¹ * (Real.sqrt (hPart N))⁻¹ * (hPart N : ℝ) = 1 := by
    rw [← mul_inv, hs, inv_mul_cancel₀ hh0]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨a, b, c', d, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
    let A : SL(2, ℤ) := ⟨!![a, hPart N * b; nPart N * hPart N * z, d], by
      rw [det_fin_two_of]
      have : (N : ℤ) = nPart N * hPart N ^ 2 := by exact_mod_cast hNnh.symm
      rw [this] at hdet
      linear_combination hdet⟩
    refine ⟨A, ⟨⟨b, by simp [A]⟩, ⟨z, by simp [A]⟩⟩, ?_⟩
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hD, hγm, hDinv]
    rw [smul_mul_mul_smul_eq_of hsq (X := !![(a : ℝ), hPart N * b; nPart N * hPart N * z, d])]
    · fin_cases i <;> fin_cases j <;> simp [A]
    · rw [mul_fin_two, mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> ring
  · rintro ⟨A, ⟨⟨b, hb⟩, ⟨z, hz⟩⟩, rfl⟩
    set a := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    set d := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
    have hdet : a * d - (hPart N * b) * (nPart N * hPart N * z) = 1 := by
      have := A.2
      rw [det_fin_two, hb, hz] at this
      push_cast at this
      linear_combination this
    let γ : SL(2, ℝ) := ⟨!![(a : ℝ), b; N * z, d], by
      rw [det_fin_two_of, hNr]
      have : ((a * d - hPart N * b * (nPart N * hPart N * z) : ℤ) : ℝ) = 1 := by
        exact_mod_cast hdet
      push_cast at this
      linear_combination this⟩
    have hγ : γ ∈ Gamma0R N := mem_Gamma0R_of_entries a b (N * z) d (by simp [γ]) (dvd_mul_right _ _)
    refine ⟨γ, hγ, ?_⟩
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hD, hDinv]
    rw [smul_mul_mul_smul_eq_of hsq (X := !![(a : ℝ), hPart N * b; nPart N * hPart N * z, d])]
    · fin_cases i <;> fin_cases j <;> simp [a, d, hb, hz]
    · show !![(hPart N : ℝ), 0; 0, 1] * !![(a : ℝ), b; N * z, d] * !![1, -0; -0, (hPart N : ℝ)] = _
      rw [mul_fin_two, mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNr] <;> ring

theorem conjGamma0n_map_conj (N : ℕ) :
    (conjGamma0n N).map (MulAut.conj (Dsl N)).toMonoidHom = Gamma0R (nPart N) := by
  unfold conjGamma0n
  rw [Subgroup.map_map]
  have : (MulAut.conj (Dsl N)).toMonoidHom.comp (MulAut.conj (Dsl N)⁻¹).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp [mul_assoc]
  rw [this, Subgroup.map_id]

/-! ### |C(N)| -/

theorem SLmap_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) :
      SL(2, ℤ) →* SL(2, ℝ)) := by
  intro A B h
  ext i j
  have := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem relIndex_Gamma0R_conjGamma0n (N : ℕ) [NeZero N] :
    (Gamma0R N).relIndex (conjGamma0n N) =
      (GammaUp (nPart N * hPart N) (hPart N)).relIndex (Gamma0 (nPart N)) := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (Dsl N)).toMonoidHom) _ _
      (MulEquiv.injective _), Gamma0R_map_conj, conjGamma0n_map_conj, Gamma0R,
    Subgroup.relIndex_map_map_of_injective]
  exact SLmap_injective

theorem card_CN' (N : ℕ) [NeZero N] : (Nat.card (CN N) : ℚ) = psi N / psi (nPart N) := by
  have hN0 := NeZero.ne N
  have hNnh := hPart_sq_mul_nPart N hN0
  set h := hPart N
  set n := nPart N
  have hh0 : h ≠ 0 := (hPart_pos N).ne'
  have hn0 : n ≠ 0 := by rintro h0; rw [h0, zero_mul] at hNnh; exact hN0 hNnh.symm
  unfold CN
  rw [card_map_mk', Subgroup.relIndex_subgroupOf (conjGamma0n_le_normalizer' N),
    relIndex_Gamma0R_conjGamma0n]
  -- [Γ₀(n) : H] = [Γ₀(nh) : H] · [Γ₀(n) : Γ₀(nh)]
  have hLe : Gamma0 (n * h) ≤ Gamma0 n := Gamma0_le_of_dvd (dvd_mul_right n h)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (GammaUp_le _ _) hLe,
    relIndex_GammaUp hh0 (dvd_mul_left h n)]
  have hrel := Subgroup.relIndex_mul_index hLe
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n * h) := ⟨mul_ne_zero hn0 hh0⟩
  have hψn : psi n ≠ 0 := by
    rw [← Gamma0_index' n]
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := Gamma0 n))
  have hidx : ((Gamma0 (n * h)).relIndex (Gamma0 n) : ℚ) = psi (n * h) / psi n := by
    rw [eq_div_iff hψn, ← Gamma0_index' n, ← Gamma0_index' (n * h)]
    exact_mod_cast hrel
  have hψN : psi N = h * psi (n * h) := by
    rw [← hNnh, show n * h ^ 2 = (n * h) * h by ring]
    exact psi_mul_of_primeFactors_subset (mul_ne_zero hn0 hh0) hh0
      (Nat.primeFactors_mono (dvd_mul_left h n) (mul_ne_zero hn0 hh0))
  push_cast
  rw [hidx, hψN]
  ring

end

end NormalizerLean
