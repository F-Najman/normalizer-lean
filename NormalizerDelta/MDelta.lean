import NormalizerDelta.Proofs
import NormalizerDelta.DefsExtra

/-!
# §M: M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D is the set of matrices of the generalized Newman bound

* The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup (`alSub`): products by the general
  product law `isAtkinLehner_mul_gen`, inverses by the adjugate.  So Γ₀(n)⁺ = `alSub n`.
* D⁻¹ w D, for w = (1/√Q)[[Qx, y], [nz, Qw]], is (1/√Q)[[Qx, y/h], [Nz/h, Qw]] (N = n h²): the form of
  `IsNewmanFormH N h_Δ` with e = Q.  Conversely D g D⁻¹ of such a g is ±w_e.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Γ₀(n)⁺ -/

theorem isAtkinLehner_inv {n Q : ℕ} {g : SL(2, ℝ)} (hg : IsAtkinLehner n Q g) :
    IsAtkinLehner n Q g⁻¹ := by
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  refine ⟨w, -y, -z, x, by linear_combination hdet, ?_⟩
  rw [coe_inv_of_coe_eq_smul hgm]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup. -/
def alSub (n : ℕ) [NeZero n] : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, (isAtkinLehner_one_iff' n 1).2 (Subgroup.one_mem _)⟩
  mul_mem' := by
    rintro g g' ⟨Q, hQ, hg⟩ ⟨Q', hQ', hg'⟩
    exact ⟨_, mul_div_gcd_dvd hQ hQ', isAtkinLehner_mul_gen hQ hQ' hg hg'⟩
  inv_mem' := by
    rintro g ⟨Q, hQ, hg⟩
    exact ⟨Q, hQ, isAtkinLehner_inv hg⟩

theorem Gamma0Plus_eq (n : ℕ) [NeZero n] : Gamma0Plus n = alSub n :=
  Subgroup.closure_eq (alSub n)

theorem mem_Gamma0Plus {n : ℕ} [NeZero n] {g : SL(2, ℝ)} :
    g ∈ Gamma0Plus n ↔ ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g := by
  rw [Gamma0Plus_eq]; rfl

/-! ### n_Δ -/

theorem nDelta_mul (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    nDelta N Δ * hDelta N Δ ^ 2 = N :=
  Nat.div_mul_cancel (hDelta_sq_dvd' N Δ)

instance nDelta_neZero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : NeZero (nDelta N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nDelta_mul N Δ, h, zero_mul])⟩

theorem hDelta_pos (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : 0 < hDelta N Δ :=
  Nat.pos_of_ne_zero (hDelta_ne_zero Δ)

/-! ### Conjugation by D⁻¹ -/

/-- Conjugation by D⁻¹: [[a, b], [c, d]] ↦ [[a, b/M], [Mc, d]]. -/
theorem coe_conj_Dm_inv {M : ℕ} (hM : 0 < M) {Y : SL(2, ℝ)} {a b c d : ℝ}
    (hY : (Y : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M)⁻¹ Y : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, b / M; M * c, d] := by
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_Dm hM, hY,
    adjugate_fin_two_of]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

theorem conj_Dm_inv_conj_Dm (M : ℕ) (g : SL(2, ℝ)) :
    MulAut.conj (Dm M)⁻¹ (MulAut.conj (Dm M) g) = g := by
  simp [MulAut.conj_apply, mul_assoc]

/-! ### M_Δ -/

theorem mem_MDelta_iff {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {g : SL(2, ℝ)} :
    g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  have hh := hDelta_pos N Δ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hNr : (N : ℝ) = nDelta N Δ * (hDelta N Δ : ℝ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨Q, hQ, x, y, z, w', hdet, hwm⟩ := mem_Gamma0Plus.1 hw
    have hQ0 : 0 < Q := Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne _))
    refine ⟨x, y, z, w', Q, hQ0, hQ, by
      rw [show N / hDelta N Δ ^ 2 = nDelta N Δ from rfl]; linear_combination hdet, 1, Or.inl rfl, ?_⟩
    have hwm' : (w : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(Real.sqrt Q)⁻¹ * (Q * x), (Real.sqrt Q)⁻¹ * y;
          (Real.sqrt Q)⁻¹ * (nDelta N Δ * z), (Real.sqrt Q)⁻¹ * (Q * w')] := by
      rw [hwm]; ext i j; fin_cases i <;> fin_cases j <;> simp
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [coe_conj_Dm_inv hh hwm']
    ext i j; fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> (try ring) <;> simp
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    refine ⟨MulAut.conj (Dm (hDelta N Δ)) g, ?_, conj_Dm_inv_conj_Dm _ g⟩
    have hgm' : (g : Matrix (Fin 2) (Fin 2) ℝ) =
        !![ε / Real.sqrt e * (a * e), ε / Real.sqrt e * (b / hDelta N Δ);
          ε / Real.sqrt e * (N * c / hDelta N Δ), ε / Real.sqrt e * (d * e)] := by
      rw [hgm]; ext i j; fin_cases i <;> fin_cases j <;> simp
    have hc := coe_conj_Dm hh hgm'
    have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn] at hdet he
    refine mem_Gamma0Plus.2 ⟨e, he, ?_⟩
    rcases hε with rfl | rfl
    · refine ⟨a, b, c, d, by linear_combination hdet, ?_⟩
      rw [hc]
      ext i j; fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> (try ring) <;> simp
    · refine ⟨-a, -b, -c, -d, by linear_combination hdet, ?_⟩
      rw [hc]
      ext i j; fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> (try ring) <;> simp

theorem coe_MDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (MDelta N Δ : Set SL(2, ℝ)) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

theorem Gamma0R_le_MDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Gamma0R N ≤ MDelta N Δ := by
  intro γ hγ
  obtain ⟨a, b, c', d, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hh := hDelta_pos N Δ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hNz : (N : ℤ) = nDelta N Δ * (hDelta N Δ : ℤ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  refine mem_MDelta_iff.2 ⟨a, b * hDelta N Δ, z * hDelta N Δ, d, 1, one_pos, one_dvd _, ?_, 1,
    Or.inl rfl, ?_⟩
  · have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn]; push_cast; rw [hNz] at hdet; linear_combination hdet
  · rw [hγm]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem normG_GammaDeltaR_le_MDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ :=
  fun _ hg => mem_MDelta_iff.2 (newman_delta' Δ hg)

end

end NormalizerLean
