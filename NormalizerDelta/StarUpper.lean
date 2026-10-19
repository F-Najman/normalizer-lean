module

public import NormalizerDelta.StarNorm

@[expose] public section

/-!
# Part 7, §N: the upper bound Nor(Γ_Δ(N)) ≤ D*⁻¹Γ₀(n*)⁺D*

* `conjPlus N h` = D_h⁻¹Γ₀(N/h²)⁺D_h; it is monotone in h (for h ∣ H, H² ∣ N), it is the set of matrices of
  the generalized Newman form with parameter h, M_Δ = `conjPlus N h_Δ`, M* = `conjPlus N h*`, and
  Nor(Γ₀(N)) = `conjPlus N h(N)`.
* The upper bound: write g ∈ Nor(Γ_Δ(N)) ≤ M_Δ as D_H⁻¹ w D_H (H = h_Δ, w = (1/√Q)[[QA, B], [n_H C, QD']]).
  Conjugating T and U_N gives 1 + Hn_H·AC ∈ Δ and 1 − Hn_H·BD' ∈ Δ, so Δ contains the kernel for
  h₁ = H/gcd(H, AC, BD'), hence h₁ ∣ h*, and e = H/h* divides AC and BD'.  With e₂ = gcd(e, A) and e₁ = e/e₂,
  D* g D*⁻¹ is Atkin–Lehner of level n* for Q e₂².
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-- D_h⁻¹ Γ₀(N/h²)⁺ D_h. -/
def conjPlus (N h : ℕ) : Subgroup SL(2, ℝ) :=
  (Gamma0Plus (N / h ^ 2)).map (MulAut.conj (Dm h)⁻¹).toMonoidHom

theorem MStar_eq (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : MStar N Δ = conjPlus N (hStar N Δ) := rfl

theorem MDelta_eq (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : MDelta N Δ = conjPlus N (hDelta N Δ) := rfl

theorem div_sq_neZero {h : ℕ} [NeZero N] (hsq : h ^ 2 ∣ N) : NeZero (N / h ^ 2) :=
  ⟨fun h0 => NeZero.ne N (by rw [← Nat.div_mul_cancel hsq, h0, zero_mul])⟩

theorem mem_conjPlus_iff {h : ℕ} [NeZero N] (hh : 0 < h) (hsq : h ^ 2 ∣ N) {g : SL(2, ℝ)} :
    g ∈ conjPlus N h ↔ ∃ Q : ℕ, Q ∣ N / h ^ 2 ∧ IsAtkinLehner (N / h ^ 2) Q (MulAut.conj (Dm h) g) := by
  haveI := div_sq_neZero hsq
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨Q, hQ, hwQ⟩ := mem_Gamma0Plus.1 hw
    refine ⟨Q, hQ, ?_⟩
    simpa [MulAut.conj_apply, mul_assoc] using hwQ
  · rintro ⟨Q, hQ, hwQ⟩
    exact ⟨MulAut.conj (Dm h) g, mem_Gamma0Plus.2 ⟨Q, hQ, hwQ⟩, conj_Dm_inv_conj_Dm h g⟩

/-- conj D_H of D_h⁻¹ w D_h, for w = s [[Qx, y], [n z, Qw]] and H = e h: s [[Qx, e y], [n z / e, Qw]]. -/
theorem coe_conj_conj {h e : ℕ} (hh : 0 < h) (he : 0 < e) {w : SL(2, ℝ)} {a b c d : ℝ}
    (hw : (w : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm (h * e)) (MulAut.conj (Dm h)⁻¹ w) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, e * b; c / e, d] := by
  have h1 := coe_conj_Dm_inv hh hw
  have h2 := coe_conj_Dm (Nat.mul_pos hh he) h1
  rw [h2]
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- Monotonicity: D_h⁻¹Γ₀(N/h²)⁺D_h ≤ D_H⁻¹Γ₀(N/H²)⁺D_H for h ∣ H, H² ∣ N. -/
theorem conjPlus_mono [NeZero N] {h H : ℕ} (hh : 0 < h) (hhH : h ∣ H) (hH : H ^ 2 ∣ N) :
    conjPlus N h ≤ conjPlus N H := by
  obtain ⟨e, rfl⟩ := hhH
  have hH0 : 0 < h * e := Nat.pos_of_ne_zero (by
    rintro h0; rw [h0] at hH; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using hH)))
  have he : 0 < e := Nat.pos_of_mul_pos_left hH0
  have hsq : h ^ 2 ∣ N := (pow_dvd_pow_of_dvd (dvd_mul_right h e) 2).trans hH
  haveI := div_sq_neZero hsq
  haveI := div_sq_neZero hH
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨Q, hQ, x, y, z, w', hdet, hwm⟩ := mem_Gamma0Plus.1 hw
  set nh := N / h ^ 2 with hnhdef
  set nH := N / (h * e) ^ 2 with hnHdef
  have hnn : nh = nH * e ^ 2 := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [mul_assoc, ← mul_pow, mul_comm e h, hnHdef, Nat.div_mul_cancel hH]
  have hQ0 : 0 < Q := Q_pos_of_dvd hQ
  have hcop : Nat.Coprime Q (nh / Q) := coprime_of_isAtkinLehner hQ ⟨x, y, z, w', hdet, hwm⟩
  -- f = gcd(Q, e), Q = Q' f², e = f e'
  set f := Nat.gcd Q e with hfdef
  have hf0 : 0 < f := Nat.gcd_pos_of_pos_left _ hQ0
  obtain ⟨e', he'⟩ : f ∣ e := Nat.gcd_dvd_right Q e
  have hfQ : f ∣ Q := Nat.gcd_dvd_left Q e
  have hf2 : f ^ 2 ∣ Q := by
    obtain ⟨R, hR⟩ := hQ
    have hRdef : nh / Q = R := by rw [hR, Nat.mul_div_cancel_left _ hQ0]
    rw [hRdef] at hcop
    have h1 : f ^ 2 ∣ Q * R := by
      rw [← hR, hnn]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ⟨e', he'⟩ 2) _
    exact (Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_left hfQ hcop)).dvd_of_dvd_mul_right h1
  obtain ⟨Q', hQ'⟩ := hf2
  have hQ'0 : 0 < Q' := Nat.pos_of_mul_pos_left (hQ' ▸ hQ0 : 0 < f ^ 2 * Q')
  have hcopQe : Nat.Coprime Q' e' := by
    have h1 := Nat.coprime_div_gcd_div_gcd (m := Q) (n := e) hf0
    rw [← hfdef] at h1
    have hQf : Q / f = f * Q' := by rw [hQ', sq, mul_assoc, Nat.mul_div_cancel_left _ hf0]
    have hef : e / f = e' := by rw [he', Nat.mul_div_cancel_left _ hf0]
    rw [hQf, hef] at h1
    exact Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) h1
  have hQ'n : Q' ∣ nH := by
    have h1 : f ^ 2 * Q' ∣ f ^ 2 * (nH * e' ^ 2) := by
      rw [← hQ']; convert hQ using 1; rw [hnn, he']; ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hf0 2) h1
    exact (Nat.Coprime.pow_right 2 hcopQe).dvd_of_dvd_mul_right h2
  refine (mem_conjPlus_iff hH0 hH).2 ⟨Q', hQ'n, f * x, e' * y, e' * z, f * w', ?_, ?_⟩
  · -- determinant: divide Q²xw − n_h yz = Q by f²
    have hdet' : ((f : ℤ) ^ 2) * ((Q' : ℤ) ^ 2 * (f * x) * (f * w') - nH * (e' * y) * (e' * z)) =
        (f : ℤ) ^ 2 * Q' := by
      have : (Q : ℤ) = f ^ 2 * Q' := by exact_mod_cast hQ'
      have hn : (nh : ℤ) = nH * (f * e') ^ 2 := by rw [hnn, he']; push_cast; ring
      rw [this, hn] at hdet
      linear_combination hdet
    exact mul_left_cancel₀ (by positivity) hdet'
  · have hsQ : Real.sqrt Q = f * Real.sqrt Q' := by
      rw [hQ', Nat.cast_mul, Real.sqrt_mul (by positivity), Nat.cast_pow, Real.sqrt_sq (by positivity)]
    have hwm' : (w : Matrix (Fin 2) (Fin 2) ℝ) = !![(Real.sqrt Q)⁻¹ * (Q * x), (Real.sqrt Q)⁻¹ * y;
        (Real.sqrt Q)⁻¹ * (nh * z), (Real.sqrt Q)⁻¹ * (Q * w')] := by
      rw [hwm]; ext i j; fin_cases i <;> fin_cases j <;> simp
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [coe_conj_conj hh he hwm']
    have hf0' : (f : ℝ) ≠ 0 := by exact_mod_cast hf0.ne'
    have hs0 : Real.sqrt Q' ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hQ'0)).ne'
    have hQR : (Q : ℝ) = f ^ 2 * Q' := by exact_mod_cast hQ'
    have heR : (e : ℝ) = f * e' := by exact_mod_cast he'
    have hnR : (nh : ℝ) = nH * (f * e') ^ 2 := by rw [hnn, he']; push_cast; ring
    rw [hsQ, hQR, heR, hnR]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-! ### The generalized Newman form and Nor(Γ₀(N)) -/

theorem isNewmanFormH_of_mem_conjPlus {h : ℕ} [NeZero N] (hh : 0 < h) (hsq : h ^ 2 ∣ N) {g : SL(2, ℝ)}
    (hg : g ∈ conjPlus N h) : IsNewmanFormH N h g := by
  haveI := div_sq_neZero hsq
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hNr : (N : ℝ) = (N / h ^ 2 : ℕ) * (h : ℝ) ^ 2 := by exact_mod_cast (Nat.div_mul_cancel hsq).symm
  obtain ⟨w, hw, rfl⟩ := hg
  obtain ⟨Q, hQ, x, y, z, w', hdet, hwm⟩ := mem_Gamma0Plus.1 hw
  have hQ0 : 0 < Q := Q_pos_of_dvd hQ
  refine ⟨x, y, z, w', Q, hQ0, hQ, by linear_combination hdet, 1, Or.inl rfl, ?_⟩
  have hwm' : (w : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(Real.sqrt Q)⁻¹ * (Q * x), (Real.sqrt Q)⁻¹ * y;
        (Real.sqrt Q)⁻¹ * ((N / h ^ 2 : ℕ) * z), (Real.sqrt Q)⁻¹ * (Q * w')] := by
    rw [hwm]; ext i j; fin_cases i <;> fin_cases j <;> simp
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [coe_conj_Dm_inv hh hwm']
  ext i j; fin_cases i <;> fin_cases j <;> simp [hNr] <;> field_simp <;> (try ring) <;> simp

theorem conjPlus_hPart_le_Norm0 (N : ℕ) [NeZero N] : conjPlus N (hPart N) ≤ Norm0 N := fun _ hg =>
  newmanForm_mem_normalizer' (isNewmanFormH_of_mem_conjPlus (hPart_pos N) (hPart_sq_dvd (NeZero.ne N)) hg)

theorem MStar_le_MDelta' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : MStar N Δ ≤ MDelta N Δ :=
  conjPlus_mono (hStar_pos N Δ) (hStar_dvd_hDelta' N Δ) (hDelta_sq_dvd' N Δ)

/-- conj D_h of D_{he}⁻¹ w D_{he}: [[a, b], [c, d]] ↦ [[a, b/e], [e c, d]]. -/
theorem coe_conj_conj' {h e : ℕ} (hh : 0 < h) (he : 0 < e) {w : SL(2, ℝ)} {a b c d : ℝ}
    (hw : (w : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm h) (MulAut.conj (Dm (h * e))⁻¹ w) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, b / e; e * c, d] := by
  have h1 := coe_conj_Dm_inv (Nat.mul_pos hh he) hw
  have h2 := coe_conj_Dm hh h1
  rw [h2]
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- (1 + X)^z = 1 + zX for X² = 0. -/
theorem val_zpow_of_sq_zero {U : (ZMod N)ˣ} {X : ZMod N} (hU : (U : ZMod N) = 1 + X) (hX : X * X = 0)
    (z : ℤ) : ((U ^ z : (ZMod N)ˣ) : ZMod N) = 1 + z * X := by
  have hUinv : ((U⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 - X := by
    have h1 : (U : ZMod N) * ((U⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hU] at h1
    linear_combination (1 - X) * h1 + ((U⁻¹ : (ZMod N)ˣ) : ZMod N) * hX
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [_root_.zpow_add_one, Units.val_mul, ih, hU]; push_cast
    linear_combination (i : ZMod N) * hX
  | pred i ih =>
    rw [_root_.zpow_sub_one, Units.val_mul, ih, hUinv]; push_cast
    linear_combination (i : ZMod N) * hX

theorem sq_modEq_of_dvd_hDelta [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {k : ℕ} (hk : k ∣ hDelta N Δ)
    {d : (ZMod N)ˣ} (hd : d ∈ Δ) : (d : ZMod N).val ^ 2 ≡ 1 [MOD k] := by
  by_cases hN1 : N = 1
  · subst hN1
    have : hDelta 1 Δ = 1 := Nat.dvd_one.1 ((dvd_pow_self _ two_ne_zero).trans (hDelta_sq_dvd' 1 Δ))
    rw [this, Nat.dvd_one] at hk
    rw [hk]; exact Nat.modEq_one
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (one_le_val_of_unit hN1 d))).2
    ((hk.trans (hDelta_dvd_epsDelta Δ)).trans (epsDelta_dvd_val hd))).symm

/-- The entry x₂₂ of the conjugate of T or U_N by D_H⁻¹ w D_H lies in Δ. -/
theorem exists_mem_conj_unipotent [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {H Q m : ℕ} (hH : 0 < H)
    (hQ0 : 0 < Q) {A B C D' : ℤ} (hdetw : (Q : ℤ) * A * D' - m * B * C = 1) {w : SL(2, ℝ)}
    (hwm : (w : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * A, B; (Q : ℝ) * m * C, (Q : ℝ) * D'])
    (hN : (N : ℝ) = Q * m * H ^ 2) (hg : MulAut.conj (Dm H)⁻¹ w ∈ NormG (GammaDeltaR N Δ)) :
    (∃ u ∈ Δ, (u : ZMod N) = ((1 + H * (Q * m * (A * C)) : ℤ) : ZMod N)) ∧
      ∃ u ∈ Δ, (u : ZMod N) = ((1 - H * (Q * m * (B * D')) : ℤ) : ZMod N) := by
  constructor
  · have hT : (matT : Matrix (Fin 2) (Fin 2) ℝ) =
        !![((1 : ℤ) : ℝ), ((1 : ℤ) : ℝ); (Q : ℝ) * m * H ^ 2 * ((0 : ℤ) : ℝ), ((1 : ℤ) : ℝ)] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matT]
    have key := coe_conj_al_mul_conj hH hQ0 hdetw hwm hT (t := 0) (by ring)
    have hmem := (Subgroup.mem_normalizer_iff.1 hg matT).1 matT_mem_GammaDeltaR
    have hY : ((MulAut.conj (Dm H)⁻¹ w * matT * (MulAut.conj (Dm H)⁻¹ w)⁻¹ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![((Q * A * D' - H * Q * m * A * C - m * B * C : ℤ) : ℝ),
          ((Q * A ^ 2 : ℤ) : ℝ); ((Q * m * H ^ 2 * (-(m * C ^ 2)) : ℤ) : ℝ),
          ((1 + H * (Q * m * (A * C)) : ℤ) : ℝ)] := by
      rw [key]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    exact exists_mem_of_mem_GammaDeltaR hY hmem
  · have hU : (matU N : Matrix (Fin 2) (Fin 2) ℝ) =
        !![((1 : ℤ) : ℝ), ((0 : ℤ) : ℝ); (Q : ℝ) * m * H ^ 2 * ((1 : ℤ) : ℝ), ((1 : ℤ) : ℝ)] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [matU, hN]
    have key := coe_conj_al_mul_conj hH hQ0 hdetw hwm hU (t := 0) (by ring)
    have hmem := (Subgroup.mem_normalizer_iff.1 hg (matU N)).1 matU_mem_GammaDeltaR
    have hY : ((MulAut.conj (Dm H)⁻¹ w * matU N * (MulAut.conj (Dm H)⁻¹ w)⁻¹ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![((Q * A * D' + H * Q * m * B * D' - m * B * C : ℤ) : ℝ),
          ((-(m * B ^ 2)) : ℤ); ((Q * m * H ^ 2 * (Q * D' ^ 2) : ℤ) : ℝ),
          ((1 - H * (Q * m * (B * D')) : ℤ) : ℝ)] := by
      rw [key]; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    exact exists_mem_of_mem_GammaDeltaR hY hmem

/-- **The upper bound**: Nor(Γ_Δ(N)) ≤ D*⁻¹Γ₀(n*)⁺D*. -/
theorem normG_le_MStar' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MStar N Δ := by
  intro g hg
  have hgM := normG_GammaDeltaR_le_MDelta' N Δ hg
  rw [MDelta_eq] at hgM
  set H := hDelta N Δ with hHdef
  have hH := hDelta_pos N Δ
  have hHsq := hDelta_sq_dvd' N Δ
  haveI := div_sq_neZero hHsq
  obtain ⟨w, hw, hgw⟩ := hgM
  have hgw' : MulAut.conj (Dm H)⁻¹ w = g := hgw
  obtain ⟨Q, hQ, hwQ⟩ := mem_Gamma0Plus.1 hw
  obtain ⟨m, A, B, C, D', hnm, hdetw, hwm⟩ := al_entries hQ hwQ
  have hQ0 : 0 < Q := Q_pos_of_dvd hQ
  have hNnat : N = Q * m * H ^ 2 := by rw [← hnm, Nat.div_mul_cancel hHsq]
  have hNR : (N : ℝ) = Q * m * H ^ 2 := by exact_mod_cast hNnat
  have hNZ : (N : ℤ) = Q * m * H ^ 2 := by exact_mod_cast hNnat
  obtain ⟨⟨u₁, hu₁, hu₁v⟩, ⟨u₂, hu₂, hu₂v⟩⟩ :=
    exists_mem_conj_unipotent (H := H) hH hQ0 hdetw hwm hNR (hgw' ▸ hg)
  -- X = H Q m AC and Y = H Q m BD' square to 0 mod N
  set X : ZMod N := ((H * (Q * m * (A * C)) : ℤ) : ZMod N)
  set Y : ZMod N := ((H * (Q * m * (B * D')) : ℤ) : ZMod N)
  have hN0 : ((N : ℤ) : ZMod N) = 0 := by simp
  have hXX : X * X = 0 := by
    simp only [X, ← Int.cast_mul]
    rw [show H * (Q * m * (A * C)) * (H * (Q * m * (A * C))) = (N : ℤ) * (Q * m * (A * C) ^ 2) by
      rw [hNZ]; ring, Int.cast_mul, hN0, zero_mul]
  have hYY : (-Y) * (-Y) = 0 := by
    simp only [Y, ← Int.cast_neg, ← Int.cast_mul]
    rw [show -(H * (Q * m * (B * D'))) * -(H * (Q * m * (B * D'))) = (N : ℤ) * (Q * m * (B * D') ^ 2) by
      rw [hNZ]; ring, Int.cast_mul, hN0, zero_mul]
  have hXY : X * Y = 0 := by
    simp only [X, Y, ← Int.cast_mul]
    rw [show H * (Q * m * (A * C)) * (H * (Q * m * (B * D'))) = (N : ℤ) * (Q * m * (A * C * (B * D'))) by
      rw [hNZ]; ring, Int.cast_mul, hN0, zero_mul]
  have hu₁' : (u₁ : ZMod N) = 1 + X := by rw [hu₁v]; simp [X]
  have hu₂' : (u₂ : ZMod N) = 1 + -Y := by rw [hu₂v]; simp [Y]; ring
  -- g₀ = gcd(H, AC, BD') and h₁ = H / g₀
  set g₁ : ℕ := Int.gcd (H : ℤ) (A * C)
  set g₀ : ℕ := Int.gcd (g₁ : ℤ) (B * D')
  have hg₁0 : 0 < g₁ := Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hH.ne')
  have hg₀0 : 0 < g₀ := Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hg₁0.ne')
  have hg₀g₁ : g₀ ∣ g₁ := Int.natCast_dvd_natCast.1 (Int.gcd_dvd_left _ _)
  have hg₁H : g₁ ∣ H := Int.natCast_dvd_natCast.1 (Int.gcd_dvd_left _ _)
  have hg₀H : g₀ ∣ H := hg₀g₁.trans hg₁H
  have hg₀AC : (g₀ : ℤ) ∣ A * C := (Int.natCast_dvd_natCast.2 hg₀g₁).trans (Int.gcd_dvd_right _ _)
  have hg₀BD : (g₀ : ℤ) ∣ B * D' := Int.gcd_dvd_right _ _
  set h₁ := H / g₀
  have hh₁H : h₁ ∣ H := Nat.div_dvd_of_dvd hg₀H
  have hh₁g : h₁ * g₀ = H := Nat.div_mul_cancel hg₀H
  have hh₁0 : 0 < h₁ := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at hh₁g; exact hH.ne' hh₁g.symm)
  have hC₁ : IsHStar N Δ h₁ := by
    refine isHStar_iff.2 ⟨hh₁0, (pow_dvd_pow_of_dvd hh₁H 2).trans hHsq,
      fun d hd => sq_modEq_of_dvd_hDelta hh₁H hd, fun u hu => ?_⟩
    by_cases hN1 : N = 1
    · subst hN1
      have : u = 1 := Subsingleton.elim _ _
      rw [this]; exact Δ.one_mem
    have hK : N / h₁ = Q * m * H * g₀ := by
      apply Nat.div_eq_of_eq_mul_left hh₁0
      rw [hNnat, ← hh₁g]; ring
    rw [hK] at hu
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (one_le_val_of_unit hN1 u)).1 hu.symm
    have huv : (u : ZMod N) = 1 + ((Q * m * H * g₀ * k : ℕ) : ZMod N) := by
      rw [← ZMod.natCast_zmod_val (u : ZMod N), ← hk, Nat.cast_sub (one_le_val_of_unit hN1 u)]
      push_cast; ring
    -- Bézout: g₀ = H α + AC β + BD' δ
    have hb1 := Int.gcd_eq_gcd_ab (H : ℤ) (A * C)
    have hb0 := Int.gcd_eq_gcd_ab (g₁ : ℤ) (B * D')
    set α := Int.gcdA (H : ℤ) (A * C)
    set β := Int.gcdB (H : ℤ) (A * C)
    set α' := Int.gcdA (g₁ : ℤ) (B * D')
    set δ := Int.gcdB (g₁ : ℤ) (B * D')
    have hpow := Δ.mul_mem (Δ.zpow_mem hu₁ ((k : ℤ) * β * α')) (Δ.zpow_mem hu₂ (-((k : ℤ) * δ)))
    convert hpow using 1
    apply Units.ext
    rw [Units.val_mul, val_zpow_of_sq_zero hu₁' hXX, val_zpow_of_sq_zero hu₂' hYY, huv]
    have e1 : ((Q * m * H * g₀ * k : ℕ) : ZMod N) =
        ((N : ℤ) : ZMod N) * ((k : ℤ) * α * α') + ((k : ℤ) * β * α' : ℤ) * X + ((k : ℤ) * δ : ℤ) * Y := by
      simp only [X, Y]
      have : ((Q * m * H * g₀ * k : ℕ) : ℤ) = (N : ℤ) * (k * α * α') + (k * β * α') * (H * (Q * m * (A * C))) +
          (k * δ) * (H * (Q * m * (B * D'))) := by
        push_cast
        rw [hb0, hb1, hNZ]; ring
      rw [← Int.cast_natCast, this]; push_cast; ring
    rw [e1, hN0]
    push_cast
    linear_combination (-((k : ZMod N) * (β : ZMod N) * (α' : ZMod N)) * ((k : ZMod N) * (δ : ZMod N))) * hXY
  -- e = H / h* divides AC and BD'
  have hh₁s : h₁ ∣ hStar N Δ := dvd_hStar' Δ hC₁
  have hsH : hStar N Δ ∣ H := hStar_dvd_hDelta' N Δ
  obtain ⟨e, he⟩ := hsH
  have hs0 := hStar_pos N Δ
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at he; exact hH.ne' he)
  have heg : e ∣ g₀ := by
    obtain ⟨k, hk⟩ := hh₁s
    have : h₁ * g₀ = h₁ * (k * e) := by rw [hh₁g, he, hk]; ring
    exact ⟨k, by rw [Nat.eq_of_mul_eq_mul_left hh₁0 this]; ring⟩
  have heAC : (e : ℤ) ∣ A * C := (Int.natCast_dvd_natCast.2 heg).trans hg₀AC
  have heBD : (e : ℤ) ∣ B * D' := (Int.natCast_dvd_natCast.2 heg).trans hg₀BD
  -- coprimality from QAD' − mBC = 1
  have cop : ∀ {x y : ℤ}, IsCoprime x y → Nat.Coprime x.natAbs y.natAbs := fun h =>
    Int.isCoprime_iff_gcd_eq_one.1 h
  have cAC := cop (⟨Q * D', -(m * B), by linear_combination hdetw⟩ : IsCoprime A C)
  have cBD := cop (⟨-(m * C), Q * A, by linear_combination hdetw⟩ : IsCoprime B D')
  have cAB := cop (⟨Q * D', -(m * C), by linear_combination hdetw⟩ : IsCoprime A B)
  have cCD := cop (⟨-(m * B), Q * A, by linear_combination hdetw⟩ : IsCoprime C D')
  have heAC' : e ∣ A.natAbs * C.natAbs := by rw [← Int.natAbs_mul]; exact Int.natCast_dvd.1 heAC
  have heBD' : e ∣ B.natAbs * D'.natAbs := by rw [← Int.natAbs_mul]; exact Int.natCast_dvd.1 heBD
  set e₂ := Nat.gcd e A.natAbs
  set e₁ := Nat.gcd e C.natAbs
  have he12 : e = e₂ * e₁ := by
    rw [← Nat.Coprime.gcd_mul e cAC, Nat.gcd_eq_left heAC']
  have heBD2 : e = Nat.gcd e B.natAbs * Nat.gcd e D'.natAbs := by
    rw [← Nat.Coprime.gcd_mul e cBD, Nat.gcd_eq_left heBD']
  have he₂A : e₂ ∣ A.natAbs := Nat.gcd_dvd_right _ _
  have he₁C : e₁ ∣ C.natAbs := Nat.gcd_dvd_right _ _
  have he₂D : e₂ ∣ D'.natAbs := by
    have h1 : e₂ ∣ Nat.gcd e B.natAbs * Nat.gcd e D'.natAbs := heBD2 ▸ Nat.gcd_dvd_left _ _
    have h2 : Nat.Coprime e₂ (Nat.gcd e B.natAbs) :=
      Nat.Coprime.coprime_dvd_left he₂A (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) cAB)
    exact (h2.dvd_of_dvd_mul_left h1).trans (Nat.gcd_dvd_right _ _)
  have he₁B : e₁ ∣ B.natAbs := by
    have h1 : e₁ ∣ Nat.gcd e B.natAbs * Nat.gcd e D'.natAbs := heBD2 ▸ Nat.gcd_dvd_left _ _
    have h2 : Nat.Coprime e₁ (Nat.gcd e D'.natAbs) :=
      Nat.Coprime.coprime_dvd_left he₁C (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) cCD)
    exact (h2.dvd_of_dvd_mul_right h1).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨x', hx'⟩ := Int.natCast_dvd.2 he₂A
  obtain ⟨w'', hw''⟩ := Int.natCast_dvd.2 he₂D
  obtain ⟨y', hy'⟩ := Int.natCast_dvd.2 he₁B
  obtain ⟨z', hz'⟩ := Int.natCast_dvd.2 he₁C
  have he₂0 : 0 < e₂ := Nat.gcd_pos_of_pos_left _ he0
  have he₁0 : 0 < e₁ := Nat.gcd_pos_of_pos_left _ he0
  -- the level n* = Q m e² and the witness
  have hnS : nStar N Δ = Q * (m * e₁ ^ 2 * e₂ ^ 2) := by
    apply Nat.div_eq_of_eq_mul_left (pow_pos hs0 2)
    have h2 : N = Q * m * (hStar N Δ * (e₂ * e₁)) ^ 2 := by rw [← he12, ← he]; exact hNnat
    calc N = Q * m * (hStar N Δ * (e₂ * e₁)) ^ 2 := h2
      _ = Q * (m * e₁ ^ 2 * e₂ ^ 2) * hStar N Δ ^ 2 := by ring
  rw [MStar_eq, ← hgw']
  refine (mem_conjPlus_iff hs0 (hStar_sq_dvd N Δ)).2 ⟨Q * e₂ ^ 2, ?_, x', y', z', w'', ?_, ?_⟩
  · show Q * e₂ ^ 2 ∣ nStar N Δ
    rw [hnS]; exact ⟨m * e₁ ^ 2, by ring⟩
  · show ((Q * e₂ ^ 2 : ℕ) : ℤ) ^ 2 * x' * w'' - ((nStar N Δ : ℕ) : ℤ) * y' * z' = (Q * e₂ ^ 2 : ℕ)
    rw [hnS]; push_cast
    rw [hx', hw'', hy', hz'] at hdetw
    linear_combination (Q * (e₂ : ℤ) ^ 2) * hdetw
  · have hwm' : (w : Matrix (Fin 2) (Fin 2) ℝ) = !![(Real.sqrt Q)⁻¹ * (Q * A), (Real.sqrt Q)⁻¹ * B;
        (Real.sqrt Q)⁻¹ * (Q * m * C), (Real.sqrt Q)⁻¹ * (Q * D')] := by
      rw [hwm]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [show H = hStar N Δ * e from he, coe_conj_conj' hs0 he0 hwm']
    have hQ0' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ0.ne'
    have hs0' : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hQ0)).ne'
    have he₂0' : (e₂ : ℝ) ≠ 0 := by exact_mod_cast he₂0.ne'
    have he₁0' : (e₁ : ℝ) ≠ 0 := by exact_mod_cast he₁0.ne'
    have hsQ : Real.sqrt ((Q * e₂ ^ 2 : ℕ) : ℝ) = Real.sqrt Q * e₂ := by
      push_cast; rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hsQ, show (N / hStar N Δ ^ 2 : ℕ) = Q * (m * e₁ ^ 2 * e₂ ^ 2) from hnS]
    have hA : (A : ℝ) = e₂ * x' := by exact_mod_cast hx'
    have hD : (D' : ℝ) = e₂ * w'' := by exact_mod_cast hw''
    have hB : (B : ℝ) = e₁ * y' := by exact_mod_cast hy'
    have hC : (C : ℝ) = e₁ * z' := by exact_mod_cast hz'
    have heR : (e : ℝ) = e₂ * e₁ := by exact_mod_cast he12
    rw [hA, hD, hB, hC, heR]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end

end NormalizerLean
