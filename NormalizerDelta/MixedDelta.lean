module

public import NormalizerDelta.MixedCount
public import NormalizerDelta.StarCount

@[expose] public section

/-!
# Part 8: Γ_{H₁}(N₁) ∩ Γ_Δ(N₂) (`card_BG_inf_GammaDelta'`)

With L = Nor(Γ_Δ(N₂)) and G* = D*⁻¹Γ₀(n*)D* (Part 7), let L_ok = {g ∈ L : `HasNormDet H₁ g`}, a subgroup
(`Lok`).  By `card_BG_inf'` the order is [N(H₁) : H₁]·[L_ok : Γ_Δ(N₂)], and [L_ok : Γ_Δ(N₂)] =
[G* : Γ_Δ(N₂)]·[L_ok : G*].  An element g ∈ L with D* g D*⁻¹ Atkin–Lehner for Q is (det m)^{-1/2}·m for an integral m
of determinant h*²Q (`exists_int_rep_of_conj_isAtkinLehner`), so g ∈ L_ok iff Q mod N₁ ∈ Det(H₁), and Part 7's
bijection L/G* → {Q} restricts to L_ok/G* → {Q : Q mod N₁ ∈ Det(H₁)} (`relIndex_Gamma0Star_Lok`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### projSL of integer matrices -/

theorem projSL_mul_int {m m' : Matrix (Fin 2) (Fin 2) ℤ} (hm : 0 < m.det) (hm' : 0 < m'.det) :
    projSL ((m * m').map (Int.cast : ℤ → ℝ)) =
      projSL (m.map (Int.cast : ℤ → ℝ)) * projSL (m'.map (Int.cast : ℤ → ℝ)) := by
  have hmm : 0 < (m * m').det := by rw [det_mul]; exact mul_pos hm hm'
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_projSL_int hmm, coe_projSL_int hm, coe_projSL_int hm',
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, Int.cast_mul,
    Real.sqrt_mul (by exact_mod_cast hm.le), mul_inv, mul_comm (Real.sqrt _)⁻¹]
  congr 1
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

theorem projSL_one_int : projSL ((1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) = 1 := by
  apply Subtype.ext
  rw [coe_projSL_int (by simp), Matrix.det_one, Int.cast_one, Real.sqrt_one, inv_one, one_smul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-! ### Det(H) -/

theorem isNormDet_mul {N : ℕ} {H : Subgroup SL(2, ZMod N)} {u v : ZMod N} (hu : IsNormDet H u)
    (hv : IsNormDet H v) : IsNormDet H (u * v) := by
  obtain ⟨g, hg, hgn⟩ := hu
  obtain ⟨g', hg', hgn'⟩ := hv
  refine ⟨g * g', by rw [det_mul, hg, hg'], fun h hh => ?_⟩
  obtain ⟨h', hh', e'⟩ := hgn' h hh
  obtain ⟨h'', hh'', e''⟩ := hgn h' hh'
  exact ⟨h'', hh'', by rw [Matrix.mul_assoc, e', ← Matrix.mul_assoc, e'', Matrix.mul_assoc]⟩

theorem isNormDet_sq {N : ℕ} (H : Subgroup SL(2, ZMod N)) (a : ZMod N) : IsNormDet H (a ^ 2) :=
  ⟨a • 1, by simp [sq], fun h hh => ⟨h, hh, by simp⟩⟩

theorem isNormDet_sq_mul_iff {N : ℕ} {H : Subgroup SL(2, ZMod N)} {a : ZMod N} (ha : IsUnit a) (u : ZMod N) :
    IsNormDet H (a ^ 2 * u) ↔ IsNormDet H u := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := ha.exists_left_inv
    have := isNormDet_mul (isNormDet_sq H b) h
    rwa [← mul_assoc, ← mul_pow, hb, one_pow, one_mul] at this
  · exact isNormDet_mul (isNormDet_sq H a)

/-! ### Integral representatives of D*⁻¹ w D* -/

theorem exists_int_rep_of_conj_isAtkinLehner {h n Q : ℕ} (hh : 0 < h) (hQ : 0 < Q) {g : SL(2, ℝ)}
    (hal : IsAtkinLehner n Q (Dm h * g * (Dm h)⁻¹)) :
    ∃ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = (h : ℤ) ^ 2 * Q ∧ g = projSL (m.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨x, y, z, w, hdet, hw⟩ := hal
  set s := (Real.sqrt Q)⁻¹
  have hw' : ((Dm h * g * (Dm h)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![s * (Q * x), s * y; s * (n * z), s * (Q * w)] := by
    rw [hw]; ext i j; fin_cases i <;> fin_cases j <;> simp [s]
  have hg : g = MulAut.conj (Dm h)⁻¹ (Dm h * g * (Dm h)⁻¹) := by simp [mul_assoc]
  have hgm := coe_conj_Dm_inv hh hw'
  rw [← hg] at hgm
  set m : Matrix (Fin 2) (Fin 2) ℤ := !![h * Q * x, y; h ^ 2 * n * z, h * Q * w] with hmdef
  have hmdet : m.det = (h : ℤ) ^ 2 * Q := by
    rw [hmdef, det_fin_two_of]; linear_combination (h : ℤ) ^ 2 * hdet
  have hmpos : 0 < m.det := by rw [hmdet]; positivity
  refine ⟨m, hmdet, Subtype.ext ?_⟩
  rw [coe_projSL_int hmpos, hgm, hmdet]
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hsq : Real.sqrt (((h : ℤ) ^ 2 * (Q : ℤ) : ℤ) : ℝ) = h * Real.sqrt Q := by
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq, mul_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hmdef, s] <;> field_simp


/-! ### The subgroup L_ok -/

theorem Gamma_le_GammaDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : CongruenceSubgroup.Gamma N ≤ GammaDelta N Δ :=
  fun γ hγ => by
    obtain ⟨-, -, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    exact ⟨CongruenceSubgroup.Gamma0_mem.2 h10, 1, Δ.one_mem, by rw [h11, Units.val_one]⟩

theorem isUnit_natCast_of_dvd {N₁ N₂ k : ℕ} (hcop : N₁.Coprime N₂) (hk : k ∣ N₂) : IsUnit ((k : ℕ) : ZMod N₁) :=
  (ZMod.isUnit_iff_coprime k N₁).2 (Nat.Coprime.coprime_dvd_left hk hcop.symm)

/-- L_ok = {g ∈ Nor(Γ_Δ(N₂)) : `HasNormDet H₁ g`}. -/
def LokDelta {N₁ : ℕ} (H₁ : Subgroup SL(2, ZMod N₁)) (N₂ : ℕ) (Δ : Subgroup (ZMod N₂)ˣ) : Subgroup SL(2, ℝ) where
  carrier := {g | g ∈ NormG (GammaDeltaR N₂ Δ) ∧ HasNormDet H₁ g}
  one_mem' := ⟨one_mem _, 1, by simp, projSL_one_int.symm, by simp, by simpa using isNormDet_one H₁⟩
  mul_mem' := by
    rintro a b ⟨ha, m, hm, rfl, hmu, hmn⟩ ⟨hb, m', hm', rfl, hmu', hmn'⟩
    refine ⟨mul_mem ha hb, m * m', by rw [det_mul]; exact mul_pos hm hm', (projSL_mul_int hm hm').symm, ?_, ?_⟩
    · rw [det_mul, Int.cast_mul]; exact hmu.mul hmu'
    · rw [det_mul, Int.cast_mul]; exact isNormDet_mul hmn hmn'
  inv_mem' := by
    rintro a ⟨ha, m, hm, rfl, hmu, hmn⟩
    exact ⟨inv_mem ha, adjugate m, by rwa [det_adjugate_two], (projSL_adjugate hm).symm,
      by rwa [det_adjugate_two], by rwa [det_adjugate_two]⟩

section Delta

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

omit [NeZero N₁] [NeZero N₂] in
theorem GammaH_map_GammaDelta (Δ : Subgroup (ZMod N₂)ˣ) :
    GammaH N₂ ((GammaDelta N₂ Δ).map (redSL N₂)) = GammaDelta N₂ Δ :=
  GammaH_map' (Gamma_le_GammaDelta N₂ Δ)

/-- For g ∈ Nor(Γ_Δ(N₂)) with D* g D*⁻¹ Atkin–Lehner for Q: g ∈ L_ok iff Q mod N₁ ∈ Det(H₁). -/
theorem mem_LokDelta_iff (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (Δ : Subgroup (ZMod N₂)ˣ)
    {g : SL(2, ℝ)} (hg : g ∈ NormG (GammaDeltaR N₂ Δ)) {Q : ℕ} (hQ : Q ∣ nStar N₂ Δ)
    (hal : IsAtkinLehner (nStar N₂ Δ) Q (Dstar N₂ Δ * g * (Dstar N₂ Δ)⁻¹)) :
    g ∈ LokDelta H₁ N₂ Δ ↔ IsNormDet H₁ (Q : ZMod N₁) := by
  have hQ0 : 0 < Q := Q_pos_of_dvd (n := nStar N₂ Δ) (by
    have : NeZero (nStar N₂ Δ) := div_sq_neZero (hStar_sq_dvd N₂ Δ); exact hQ)
  obtain ⟨m, hmdet, rfl⟩ := exists_int_rep_of_conj_isAtkinLehner (hStar_pos N₂ Δ) hQ0 hal
  have hmpos : 0 < m.det := by rw [hmdet]; have := hStar_pos N₂ Δ; positivity
  have hdvdQ : Q ∣ N₂ := hQ.trans ⟨hStar N₂ Δ ^ 2, (nStar_mul N₂ Δ).symm⟩
  have huh := isUnit_natCast_of_dvd (N₁ := N₁) hcop (hStar_dvd N₂ Δ)
  have huQ := isUnit_natCast_of_dvd (N₁ := N₁) hcop hdvdQ
  have hunit : IsUnit ((m.det : ℤ) : ZMod N₁) := by
    rw [hmdet]; push_cast; exact (huh.pow 2).mul huQ
  have hg' : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ NormG (toR (GammaH N₂ ((GammaDelta N₂ Δ).map (redSL N₂)))) := by
    rw [GammaH_map_GammaDelta]; exact hg
  have e : projSL (m.map (Int.cast : ℤ → ℝ)) ∈ LokDelta H₁ N₂ Δ ↔
      HasNormDet H₁ (projSL (m.map (Int.cast : ℤ → ℝ))) := ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  rw [e, hasNormDet_iff hcop H₁ _ hmpos hunit hg', hmdet]
  push_cast
  exact isNormDet_sq_mul_iff huh _

theorem Gamma0Star_le_LokDelta (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁)) (Δ : Subgroup (ZMod N₂)ˣ) :
    Gamma0Star N₂ Δ ≤ LokDelta H₁ N₂ Δ := by
  intro g hg
  have hn := Gamma0Star_le_normG' N₂ Δ hg
  have hal : IsAtkinLehner (nStar N₂ Δ) 1 (Dstar N₂ Δ * g * (Dstar N₂ Δ)⁻¹) :=
    (isAtkinLehner_one_iff' _ _).2 (mem_Gamma0Star_iff.1 hg)
  rw [mem_LokDelta_iff hcop H₁ Δ hn (one_dvd _) hal, Nat.cast_one]
  exact isNormDet_one H₁

theorem relIndex_Gamma0Star_LokDelta (hcop : N₁.Coprime N₂) (H₁ : Subgroup SL(2, ZMod N₁))
    (Δ : Subgroup (ZMod N₂)ˣ) :
    (Gamma0Star N₂ Δ).relIndex (LokDelta H₁ N₂ Δ) = wMixed H₁ N₂ Δ := by
  set L := LokDelta H₁ N₂ Δ
  set K := (Gamma0Star N₂ Δ).subgroupOf L
  set n := nStar N₂ Δ
  have : NeZero n := div_sq_neZero (hStar_sq_dvd N₂ Δ)
  let S := {Q : ℕ // Q ∣ n ∧ Nat.Coprime Q (n / Q) ∧ IsIotaStable N₂ Δ Q ∧ IsNormDet H₁ (Q : ZMod N₁)}
  have hspec := fun g : L => (mem_normG_GammaDeltaR_iff' Δ g).1 g.2.1
  have hok : ∀ g : L, IsNormDet H₁ ((Classical.choose (hspec g) : ℕ) : ZMod N₁) := fun g =>
    (mem_LokDelta_iff hcop H₁ Δ g.2.1 (Classical.choose_spec (hspec g)).1
      (Classical.choose_spec (hspec g)).2.2.2).1 g.2
  let φ : L → S := fun g => ⟨Classical.choose (hspec g), (Classical.choose_spec (hspec g)).1,
    (Classical.choose_spec (hspec g)).2.1, (Classical.choose_spec (hspec g)).2.2.1, hok g⟩
  have hφal : ∀ g : L, IsAtkinLehner n (φ g).1 (Dstar N₂ Δ * g * (Dstar N₂ Δ)⁻¹) := fun g =>
    (Classical.choose_spec (hspec g)).2.2.2
  have key : ∀ g g' : L, φ g = φ g' ↔ g⁻¹ * g' ∈ K := by
    intro g g'
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_Gamma0Star_iff,
      ← isAtkinLehner_one_iff']
    have hconj : Dstar N₂ Δ * ((g : SL(2, ℝ))⁻¹ * g') * (Dstar N₂ Δ)⁻¹ =
        (Dstar N₂ Δ * g * (Dstar N₂ Δ)⁻¹)⁻¹ * (Dstar N₂ Δ * g' * (Dstar N₂ Δ)⁻¹) := by group
    rw [hconj]
    have hm := isAtkinLehner_mul_gen (φ g).2.1 (φ g').2.1 (isAtkinLehner_inv (hφal g)) (hφal g')
    constructor
    · intro he
      rw [he, Nat.gcd_self, Nat.div_self (Q_pos_of_dvd (φ g').2.1), one_mul] at hm
      exact hm
    · intro h1
      apply Subtype.ext
      have hu := isAtkinLehner_unique (mul_div_gcd_dvd (φ g).2.1 (φ g').2.1) (one_dvd n) hm h1
      have hg0 : 0 < Nat.gcd (φ g).1 (φ g').1 := Nat.gcd_pos_of_pos_left _ (Q_pos_of_dvd (φ g).2.1)
      have e1 := Nat.eq_one_of_mul_eq_one_right hu
      have e2 := Nat.eq_one_of_mul_eq_one_left hu
      have := Nat.div_mul_cancel (Nat.gcd_dvd_left (φ g).1 (φ g').1)
      have := Nat.div_mul_cancel (Nat.gcd_dvd_right (φ g).1 (φ g').1)
      rw [e1] at *; rw [e2] at *
      omega
  have hsurj : Function.Surjective φ := by
    rintro ⟨Q, hQ, hc, hst, hnd⟩
    obtain ⟨w, hw⟩ := exists_isAtkinLehner' hQ hc
    have hmem := (conj_mem_normG_iff' Δ hQ hc hw).2 hst
    have hal : IsAtkinLehner n Q (Dstar N₂ Δ * ((Dstar N₂ Δ)⁻¹ * w * Dstar N₂ Δ) * (Dstar N₂ Δ)⁻¹) := by
      rwa [show Dstar N₂ Δ * ((Dstar N₂ Δ)⁻¹ * w * Dstar N₂ Δ) * (Dstar N₂ Δ)⁻¹ = w by group]
    have hL : (Dstar N₂ Δ)⁻¹ * w * Dstar N₂ Δ ∈ L := (mem_LokDelta_iff hcop H₁ Δ hmem hQ hal).2 hnd
    refine ⟨⟨_, hL⟩, Subtype.ext ?_⟩
    exact isAtkinLehner_unique (φ _).2.1 hQ (hφal ⟨_, hL⟩) hal
  let F : L ⧸ K → S := Quotient.lift φ (fun a b hab => (key a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hF : Function.Bijective F := by
    refine ⟨fun x y hxy => ?_, fun s => ?_⟩
    · induction x using QuotientGroup.induction_on
      induction y using QuotientGroup.induction_on
      exact QuotientGroup.eq.2 ((key _ _).1 hxy)
    · obtain ⟨g, hg⟩ := hsurj s
      exact ⟨QuotientGroup.mk g, hg⟩
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective F hF)]
  rfl

theorem card_BG_inf_GammaDelta' (hcop : N₁.Coprime N₂) {H₁ : Subgroup SL(2, ZMod N₁)}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ N₁ → ¬ IsBorelMod H₁ p ∨ IsSplitMod H₁ (p ^ N₁.factorization p))
    (Δ : Subgroup (ZMod N₂)ˣ) :
    (Nat.card (BG (toR (GammaH N₁ H₁ ⊓ GammaDelta N₂ Δ))) : ℚ) =
      H₁.relIndex (NormH H₁) * Δ.index * (psi N₂ / psi (nStar N₂ Δ)) * wMixed H₁ N₂ Δ := by
  have h1 := card_BG_inf' hcop ((GammaDelta N₂ Δ).map (redSL N₂)) hloc
  rw [GammaH_map_GammaDelta] at h1
  rw [h1]
  have hcount : Nat.card {x : BG (toR (GammaDelta N₂ Δ)) // ∃ g, x.IsClassOf g ∧ HasNormDet H₁ g} =
      (GammaDeltaR N₂ Δ).relIndex (LokDelta H₁ N₂ Δ) := by
    apply card_subtype_eq_relIndex (fun g hg => hg.1 : LokDelta H₁ N₂ Δ ≤ NormG (GammaDeltaR N₂ Δ))
    intro x
    constructor
    · rintro ⟨g, ⟨hg, rfl⟩, hnd⟩
      exact ⟨⟨g, hg, hnd⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, ⟨g.2.1, rfl⟩, g.2.2⟩
  have hle0 := (Gamma0R_le_Gamma0Star' N₂ Δ).1
  rw [hcount, ← Subgroup.relIndex_mul_relIndex (GammaDeltaR N₂ Δ) (Gamma0Star N₂ Δ) (LokDelta H₁ N₂ Δ)
      (GammaDeltaR_le_Gamma0R.trans hle0) (Gamma0Star_le_LokDelta hcop H₁ Δ),
    ← Subgroup.relIndex_mul_relIndex (GammaDeltaR N₂ Δ) (Gamma0R N₂) (Gamma0Star N₂ Δ)
      GammaDeltaR_le_Gamma0R hle0,
    relIndex_GammaDeltaR_Gamma0R, relIndex_Gamma0Star_LokDelta hcop H₁ Δ]
  push_cast
  rw [(Gamma0R_le_Gamma0Star' N₂ Δ).2]
  ring

end Delta

end

end NormalizerLean
