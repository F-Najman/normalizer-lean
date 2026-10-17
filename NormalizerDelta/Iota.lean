module

public import NormalizerDelta.IndexDelta

@[expose] public section

/-!
# s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ} for 4 ∤ N, 9 ∤ N

* `al_conj`: for g = (1/√Q)[[Qx, y], [Nz, Qw]] (Q²xw − Nyz = Q, Q ∣ N) and γ ∈ Γ₀(N), g γ g⁻¹ = γ'' ∈ Γ₀(N)
  with γ''₁₁ = −(N/Q)yz γ₀₀ − yw γ₁₀ + Nxz γ₀₁ + Qxw γ₁₁, so γ''₁₁ ≡ γ₀₀ (mod Q) and
  γ''₁₁ ≡ γ₁₁ (mod N/Q) (as Qxw − (N/Q)yz = 1): the lower right entry goes to ι_Q of it.
* `IsIota` is symmetric, ι_Q(d) exists (by `al_conj`) and is unique (CRT), so g normalizes Γ_Δ(N) iff
  ι_Q(Δ) = Δ (`al_mem_normG_iff`).
* For h(N) = 1 every class of B(N) is a class w_Q (Newman), and Q is determined by the class
  (p ∣ Q ⟺ p ∣ e(g), invariant under Γ₀(N): the frozen `chi`), which gives the bijection.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

/-! ### Atkin–Lehner conjugation of the lower right entry -/

theorem al_conj {Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)} (hg : IsAtkinLehner N Q g)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ γ'' ∈ CongruenceSubgroup.Gamma0 N, ofZ γ'' = g * ofZ γ * g⁻¹ ∧
      (Q : ℤ) ∣ γ'' 1 1 - γ 0 0 ∧ ((N / Q : ℕ) : ℤ) ∣ γ'' 1 1 - γ 1 1 := by
  have hgN := isAtkinLehner_mem_normalizer' hQ hg
  have hmem : g * ofZ γ * g⁻¹ ∈ Gamma0R N :=
    (Subgroup.mem_normalizer_iff.1 hgN _).1 (Subgroup.mem_map_of_mem _ hγ)
  obtain ⟨γ'', hγ''0, hγ''⟩ := Subgroup.mem_map.1 hmem
  refine ⟨γ'', hγ''0, hγ'', ?_⟩
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  have hQ0 : Q ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)
  obtain ⟨K, hK⟩ := hQ
  have hKdiv : N / Q = K := by rw [hK, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)]
  rw [hKdiv]
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ0
  have hdet' : (Q : ℤ) * x * w - K * y * z = 1 := by
    apply mul_left_cancel₀ hQz
    rw [hK] at hdet; push_cast at hdet
    linear_combination hdet
  have hc : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  obtain ⟨t10, ht10⟩ := hc
  -- the (1,1) entry of g γ g⁻¹
  have h11 := congrArg (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hγ''
  rw [coe_conj, hgm, coe_ofZ, adjugate_smul, Fintype.card_fin, adjugate_fin_two_of] at h11
  simp only [smul_mul, mul_smul, smul_smul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Nat.reduceSub, pow_one, coe_ofZ] at h11
  have hs : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * (Q : ℝ) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_mul_cancel₀ (by exact_mod_cast hQ0)]
  have hNr : (N : ℝ) = Q * K := by exact_mod_cast hK
  have hint : γ'' 1 1 = -(K * y * z * γ 0 0) - y * w * γ 1 0 + N * x * z * γ 0 1 +
      Q * x * w * γ 1 1 := by
    have hr : (γ'' 1 1 : ℝ) = -(K * y * z * γ 0 0) - y * w * γ 1 0 + N * x * z * γ 0 1 +
        Q * x * w * γ 1 1 := by
      have : ((γ'' 1 1 : ℤ) : ℝ) = (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * (Q : ℝ) *
          (-(K * y * z * γ 0 0) - y * w * γ 1 0 + N * x * z * γ 0 1 + Q * x * w * γ 1 1) := by
        rw [h11, hNr]; ring
      rw [this, hs, one_mul]
    exact_mod_cast hr
  constructor
  · refine ⟨-(x * w * γ 0 0) - y * w * K * t10 + K * x * z * γ 0 1 + x * w * γ 1 1, ?_⟩
    rw [hint, ht10, hK]; push_cast
    linear_combination (γ 0 0) * hdet'
  · refine ⟨-(y * z * γ 0 0) - y * w * Q * t10 + Q * x * z * γ 0 1 + y * z * γ 1 1, ?_⟩
    rw [hint, ht10, hK]; push_cast
    linear_combination (γ 1 1) * hdet'

/-! ### ι_Q -/

theorem isIota_symm {Q : ℕ} {d u : (ZMod N)ˣ} : IsIota N Q d u ↔ IsIota N Q u d := by
  unfold IsIota
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by rw [mul_comm]; exact h1, h2.symm⟩

theorem isIota_of_al_conj {Q : ℕ} [NeZero N] (hQ : Q ∣ N) {γ γ'' : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hγ'' : γ'' ∈ CongruenceSubgroup.Gamma0 N)
    (h1 : (Q : ℤ) ∣ γ'' 1 1 - γ 0 0) (h2 : ((N / Q : ℕ) : ℤ) ∣ γ'' 1 1 - γ 1 1) :
    IsIota N Q (unitMap N ⟨γ, hγ⟩) (unitMap N ⟨γ'', hγ''⟩) := by
  unfold IsIota
  rw [coe_unitMap, coe_unitMap]
  simp only
  rw [ZMod.cast_intCast hQ, ZMod.cast_intCast hQ, ZMod.cast_intCast (Nat.div_dvd_of_dvd hQ),
    ZMod.cast_intCast (Nat.div_dvd_of_dvd hQ)]
  refine ⟨?_, (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
    have := h2.neg_right; convert this using 1; ring)⟩
  have hc : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  have hQc : (Q : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.2 hQ).trans hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by have := γ.2; rwa [det_fin_two] at this
  have e1 : ((γ'' 1 1 : ℤ) : ZMod Q) = ((γ 0 0 : ℤ) : ZMod Q) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
      have := h1.neg_right; convert this using 1; ring)
  have e2 : ((γ 1 0 : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hQc
  rw [e1]
  have := congrArg (fun z : ℤ => (z : ZMod Q)) hdet
  push_cast at this
  rw [e2, mul_zero, sub_zero] at this
  exact this

theorem exists_isIota {Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hcop : Nat.Coprime Q (N / Q))
    (d : (ZMod N)ˣ) : ∃ u, IsIota N Q d u := by
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := unitMap_surjective d
  obtain ⟨g, hg⟩ := exists_isAtkinLehner' hQ hcop
  obtain ⟨γ'', hγ'', -, h1, h2⟩ := al_conj hQ hg hγ
  exact ⟨_, isIota_of_al_conj hQ hγ hγ'' h1 h2⟩

theorem isIota_unique {Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hcop : Nat.Coprime Q (N / Q))
    {d u u' : (ZMod N)ˣ} (h : IsIota N Q d u) (h' : IsIota N Q d u') : u = u' := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  haveI : NeZero Q := ⟨by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ)⟩
  set a := (u : ZMod N).val
  set a' := (u' : ZMod N).val
  simp only [ZMod.cast_eq_val] at h1 h1' h2 h2'
  have eQ : (a : ZMod Q) = (a' : ZMod Q) := by
    calc (a : ZMod Q) = a * (((d : ZMod N).val : ZMod Q) * a') := by
          rw [mul_comm _ (a' : ZMod Q), h1', mul_one]
      _ = (a * ((d : ZMod N).val : ZMod Q)) * a' := by ring
      _ = a' := by rw [h1, one_mul]
  have eK : (a : ZMod (N / Q)) = (a' : ZMod (N / Q)) := h2.trans h2'.symm
  rw [ZMod.natCast_eq_natCast_iff'] at eQ eK
  have hQd : (Q : ℤ) ∣ (a : ℤ) - a' := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
    exact ((ZMod.natCast_eq_natCast_iff' _ _ _).2 eQ).symm
  have hKd : ((N / Q : ℕ) : ℤ) ∣ (a : ℤ) - a' := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast
    exact ((ZMod.natCast_eq_natCast_iff' _ _ _).2 eK).symm
  have hNd : (N : ℤ) ∣ (a : ℤ) - a' := by
    have := (Nat.Coprime.isCoprime hcop).mul_dvd hQd hKd
    rwa [← Nat.cast_mul, Nat.mul_div_cancel' hQ] at this
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (u' : ZMod N)]
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 hNd
  push_cast at this
  exact this.symm

/-- An Atkin–Lehner element w_Q normalizes Γ_Δ(N) iff ι_Q(Δ) = Δ. -/
theorem al_mem_normG_iff {Q : ℕ} [NeZero N] (hQ : Q ∣ N) (hcop : Nat.Coprime Q (N / Q))
    {g : SL(2, ℝ)} (hg : IsAtkinLehner N Q g) (Δ : Subgroup (ZMod N)ˣ) :
    g ∈ NormG (GammaDeltaR N Δ) ↔ ∀ u, u ∈ Δ ↔ ∃ d ∈ Δ, IsIota N Q d u := by
  have hgN := isAtkinLehner_mem_normalizer' hQ hg
  -- ι maps Δ into Δ, if g normalizes
  have key : g ∈ NormG (GammaDeltaR N Δ) → ∀ d ∈ Δ, ∀ u, IsIota N Q d u → u ∈ Δ := by
    intro hgD d hd u hdu
    obtain ⟨⟨γ, hγ⟩, rfl⟩ := unitMap_surjective d
    obtain ⟨γ'', hγ''0, hγ'', h1, h2⟩ := al_conj hQ hg hγ
    have hγD : ofZ γ ∈ GammaDeltaR N Δ := ofZ_mem_toR ⟨hγ, _, hd, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hgD _).1 hγD
    rw [← hγ''] at this
    obtain ⟨γ3, ⟨-, v, hv, hvd⟩, h3⟩ := mem_toR.1 this
    obtain rfl := ofZ_injective h3
    have hu : u = unitMap N ⟨γ3, hγ''0⟩ := isIota_unique hQ hcop hdu (isIota_of_al_conj hQ hγ hγ''0 h1 h2)
    have : v = unitMap N ⟨γ3, hγ''0⟩ := Units.ext (by rw [coe_unitMap, hvd])
    rw [hu, ← this]; exact hv
  constructor
  · intro hgD u
    constructor
    · intro hu
      obtain ⟨v, hv⟩ := exists_isIota hQ hcop u
      exact ⟨v, key hgD u hu v hv, isIota_symm.1 hv⟩
    · rintro ⟨d, hd, hdu⟩
      exact key hgD d hd u hdu
  · intro hstab
    rw [Subgroup.mem_normalizer_iff]
    intro Y
    constructor
    · intro hY
      obtain ⟨γ, ⟨hγ, v, hv, hvd⟩, rfl⟩ := mem_toR.1 hY
      obtain ⟨γ'', hγ''0, hγ'', h1, h2⟩ := al_conj hQ hg hγ
      rw [← hγ'']
      refine ofZ_mem_toR ⟨hγ''0, unitMap N ⟨γ'', hγ''0⟩,
        (hstab _).2 ⟨v, hv, ?_⟩, rfl⟩
      have : v = unitMap N ⟨γ, hγ⟩ := Units.ext (by rw [coe_unitMap, hvd])
      rw [this]
      exact isIota_of_al_conj hQ hγ hγ''0 h1 h2
    · intro hY
      have hY0 : Y ∈ Gamma0R N := by
        have := (Subgroup.mem_normalizer_iff.1 hgN Y).2 (GammaDeltaR_le_Gamma0R hY)
        exact this
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hY0
      obtain ⟨γ'', hγ''0, hγ'', h1, h2⟩ := al_conj hQ hg hγ
      rw [← hγ''] at hY
      obtain ⟨γ3, ⟨-, v, hv, hvd⟩, h3⟩ := mem_toR.1 hY
      obtain rfl := ofZ_injective h3
      have hv' : v = unitMap N ⟨γ3, hγ''0⟩ := Units.ext (by rw [coe_unitMap, hvd])
      obtain ⟨d', hd', hd'v⟩ := (hstab v).1 hv
      have hι := isIota_of_al_conj hQ hγ hγ''0 h1 h2
      rw [← hv'] at hι
      have : unitMap N ⟨γ, hγ⟩ = d' :=
        isIota_unique hQ hcop (isIota_symm.1 hι) (isIota_symm.1 hd'v)
      exact ofZ_mem_toR ⟨hγ, d', hd', by rw [← this, coe_unitMap]⟩

end

end NormalizerLean
