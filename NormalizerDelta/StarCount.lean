module

public import NormalizerDelta.StarUpper

@[expose] public section

/-!
# Part 7, §N: the normalizer exactly, its index, and Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N))

* `mem_normG_GammaDeltaR_iff'`: the upper bound and the criterion together.
* The index: Γ₀(N) ≤ D*⁻¹Γ₀(n*)D* =: Γ*, of index ψ(N)/ψ(n*) (as for C(N) in Part 1); the cosets of Γ* in
  Nor(Γ_Δ(N)) correspond to the ι*-stable Q ∥ n* (the Q of an Atkin–Lehner element is unique), so
  [Nor : Γ_Δ(N)] = i_Δ · ψ(N)/ψ(n*) · w*_Δ.
* Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) iff h* ∣ h(N): ⇐ by monotonicity of `conjPlus`; ⇒ because S_{h*} = D*⁻¹TD* ∈ Γ*
  normalizes Γ₀(N) only if every unit squares to 1 mod h*.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

variable {N : ℕ}

theorem conj_Dstar_inv (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) (g : SL(2, ℝ)) :
    (Dstar N Δ)⁻¹ * (Dstar N Δ * g * (Dstar N Δ)⁻¹) * Dstar N Δ = g := by group

/-! ### The normalizer -/

theorem mem_normG_GammaDeltaR_iff' {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) (g : SL(2, ℝ)) :
    g ∈ NormG (GammaDeltaR N Δ) ↔
      ∃ Q : ℕ, Q ∣ nStar N Δ ∧ Nat.Coprime Q (nStar N Δ / Q) ∧ IsIotaStable N Δ Q ∧
        IsAtkinLehner (nStar N Δ) Q (Dstar N Δ * g * (Dstar N Δ)⁻¹) := by
  constructor
  · intro hg
    have hM := normG_le_MStar' N Δ hg
    rw [MStar_eq, mem_conjPlus_iff (hStar_pos N Δ) (hStar_sq_dvd N Δ)] at hM
    obtain ⟨Q, hQ, hal⟩ := hM
    have hal' : IsAtkinLehner (nStar N Δ) Q (Dstar N Δ * g * (Dstar N Δ)⁻¹) := hal
    have hQ' : Q ∣ nStar N Δ := hQ
    have hc := coprime_of_isAtkinLehner (N := nStar N Δ) hQ' hal'
    refine ⟨Q, hQ, hc, ?_, hal'⟩
    have := (conj_mem_normG_iff' Δ hQ hc hal').1
    rw [conj_Dstar_inv] at this
    exact this hg
  · rintro ⟨Q, hQ, hc, hst, hal⟩
    have := (conj_mem_normG_iff' Δ hQ hc hal).2 hst
    rwa [conj_Dstar_inv] at this

/-! ### Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) iff h* ∣ h(N) -/

theorem normG_GammaDeltaR_le_Norm0_iff' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ Norm0 N ↔ hStar N Δ ∣ hPart N := by
  constructor
  · intro hle
    rw [← hStar_top' N]
    apply dvd_hStar'
    set h := hStar N Δ with hhdef
    have hh := hStar_pos N Δ
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    refine isHStar_iff.2 ⟨hh, hStar_sq_dvd N Δ, fun u _ => ?_, fun u _ => Subgroup.mem_top u⟩
    -- S = D*⁻¹ T D* lies in Γ* ≤ Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N))
    have hT : matT ∈ Gamma0R (nStar N Δ) :=
      mem_Gamma0R_of_entries 1 1 0 1 (by ext i j; fin_cases i <;> fin_cases j <;> simp [matT]) (dvd_zero _)
    have hS : MulAut.conj (Dstar N Δ)⁻¹ matT ∈ Norm0 N :=
      hle (Gamma0Star_le_normG' N Δ ⟨matT, hT, rfl⟩)
    have hSm : ((MulAut.conj (Dstar N Δ)⁻¹ matT : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![(1 : ℝ), 1 / (h : ℝ); (h : ℝ) * 0, 1] :=
      coe_conj_Dm_inv hh (by ext i j; fin_cases i <;> fin_cases j <;> simp [matT])
    obtain ⟨a, b, c, d, hdet, hud⟩ := exists_Gamma0R_entries u
    let γ : SL(2, ℝ) := ⟨!![(a : ℝ), b; (N : ℝ) * c, d], by rw [det_fin_two_of]; exact_mod_cast hdet⟩
    have hγ : γ ∈ Gamma0R N := mem_Gamma0R_of_entries a b (N * c) d (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [γ]) (dvd_mul_right _ _)
    have hconj := (Subgroup.mem_normalizer_iff.1 hS γ).1 hγ
    obtain ⟨a₁, b₁, c₁, d₁, -, -, hm⟩ := exists_entries_of_mem_Gamma0R hconj
    have h01 := congrFun (congrFun hm 0) 1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, hSm, adjugate_fin_two_of] at h01
    simp [γ, Matrix.mul_apply, Fin.sum_univ_two] at h01
    have hNR : (N : ℝ) = nStar N Δ * h ^ 2 := by exact_mod_cast (nStar_mul N Δ).symm
    -- (d − a)/h = b₁ − b + n* c
    have hda : ((d - a : ℤ) : ℝ) = h * ((b₁ - b + nStar N Δ * c : ℤ) : ℝ) := by
      rw [hNR] at h01; push_cast
      field_simp at h01
      linear_combination h01
    have hda' : d - a = h * (b₁ - b + nStar N Δ * c) := by exact_mod_cast hda
    have hhN : (h : ℤ) ∣ N := Int.natCast_dvd_natCast.2 (hStar_dvd N Δ)
    have hsq : (h : ℤ) ∣ d ^ 2 - 1 := by
      have e : d ^ 2 - 1 = d * (d - a) + b * (N * c) := by linear_combination hdet
      rw [e, hda']
      exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
        (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hhN _) _)
    -- u.val ≡ d mod N
    have hv : (N : ℤ) ∣ d - (u : ZMod N).val := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hud
    have hval : (h : ℤ) ∣ ((u : ZMod N).val : ℤ) ^ 2 - 1 := by
      have e : ((u : ZMod N).val : ℤ) ^ 2 - 1 = (d ^ 2 - 1) - (d - (u : ZMod N).val) *
          (d + (u : ZMod N).val) := by ring
      rw [e]
      exact dvd_sub hsq (dvd_mul_of_dvd_left (hhN.trans hv) _)
    apply Nat.ModEq.symm
    exact Nat.modEq_iff_dvd.2 (by push_cast; exact hval)
  · intro hdvd
    exact (normG_le_MStar' N Δ).trans ((conjPlus_mono (hStar_pos N Δ) hdvd
      (hPart_sq_dvd (NeZero.ne N))).trans (conjPlus_hPart_le_Norm0 N))

/-! ### [Γ* : Γ₀(N)] = ψ(N)/ψ(n*) -/

theorem Gamma0R_map_conj_gen {h : ℕ} [NeZero N] (hh : 0 < h) (hsq : h ^ 2 ∣ N) :
    (Gamma0R N).map (MulAut.conj (Dm h)).toMonoidHom =
      (GammaUp (N / h ^ 2 * h) h).map (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) := by
  set n := N / h ^ 2
  have hNnh : n * h ^ 2 = N := Nat.div_mul_cancel hsq
  have hNZ : (N : ℤ) = n * h ^ 2 := by exact_mod_cast hNnh.symm
  have hNR : (N : ℝ) = n * h ^ 2 := by exact_mod_cast hNnh.symm
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  ext x
  simp only [Subgroup.mem_map, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨a, b, c', d, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
    have hdet' : a * d - (h * b) * (n * h * z) = 1 := by rw [hNZ] at hdet; linear_combination hdet
    refine ⟨mkSL a (h * b) (n * h * z) d hdet', ⟨⟨b, by simp [mkSL]⟩, ⟨z, by simp [mkSL]⟩⟩, ?_⟩
    apply Subtype.ext
    rw [show (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (mkSL a (h * b) (n * h * z) d hdet') :
      SL(2, ℝ)) = ofZ (mkSL a (h * b) (n * h * z) d hdet') from rfl, coe_ofZ_mkSL, coe_conj_Dm hh hγm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hNR] <;> field_simp <;> ring
  · rintro ⟨A, ⟨⟨b, hb⟩, ⟨z, hz⟩⟩, rfl⟩
    set a := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    set d := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
    have hdet : a * d - b * (N * z) = 1 := by
      have := A.2
      rw [det_fin_two, hb, hz] at this
      push_cast at this
      rw [hNZ]; linear_combination this
    have hAm : ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), h * b; n * h * z, d] := by
      rw [show (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A : SL(2, ℝ)) = ofZ A from rfl, coe_ofZ,
        hb, hz]
      push_cast; rfl
    refine ⟨MulAut.conj (Dm h)⁻¹ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A), ?_, ?_⟩
    · refine mem_Gamma0R_of_entries a b (N * z) d ?_ (dvd_mul_right _ _)
      rw [coe_conj_Dm_inv hh hAm]
      ext i j; fin_cases i <;> fin_cases j <;> simp [hNR] <;> field_simp <;> ring
    · simp [MulAut.conj_apply, mul_assoc]

theorem relIndex_Gamma0R_Gamma0Star (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    ((Gamma0R N).relIndex (Gamma0Star N Δ) : ℚ) = psi N / psi (nStar N Δ) := by
  set h := hStar N Δ
  set n := nStar N Δ
  have hh := hStar_pos N Δ
  have hh0 : h ≠ 0 := hh.ne'
  have hn0 : n ≠ 0 := NeZero.ne _
  have hNnh : n * h ^ 2 = N := nStar_mul N Δ
  have hmap : (Gamma0Star N Δ).map (MulAut.conj (Dm h)).toMonoidHom = Gamma0R n := by
    unfold Gamma0Star
    rw [Subgroup.map_map]
    have hD : Dstar N Δ = Dm h := rfl
    have : (MulAut.conj (Dm h)).toMonoidHom.comp (MulAut.conj (Dstar N Δ)⁻¹).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        inv_inv, MonoidHom.id_apply, hD]
      group
    rw [this, Subgroup.map_id]
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (Dm h)).toMonoidHom) _ _
      (MulEquiv.injective _), Gamma0R_map_conj_gen hh (hStar_sq_dvd N Δ), hmap, Gamma0R,
    Subgroup.relIndex_map_map_of_injective _ _ SLmap_injective]
  change ((GammaUp (n * h) h).relIndex (CongruenceSubgroup.Gamma0 n) : ℚ) = psi N / psi n
  have hLe : CongruenceSubgroup.Gamma0 (n * h) ≤ CongruenceSubgroup.Gamma0 n :=
    Gamma0_le_of_dvd (dvd_mul_right n h)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (GammaUp_le _ _) hLe, relIndex_GammaUp hh0 (dvd_mul_left h n)]
  have hrel := Subgroup.relIndex_mul_index hLe
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n * h) := ⟨mul_ne_zero hn0 hh0⟩
  have hψn : psi n ≠ 0 := by
    rw [← Gamma0_index' n]
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := CongruenceSubgroup.Gamma0 n))
  have hidx : ((CongruenceSubgroup.Gamma0 (n * h)).relIndex (CongruenceSubgroup.Gamma0 n) : ℚ) =
      psi (n * h) / psi n := by
    rw [eq_div_iff hψn, ← Gamma0_index' n, ← Gamma0_index' (n * h)]
    exact_mod_cast hrel
  have hψN : psi N = h * psi (n * h) := by
    rw [← hNnh, show n * h ^ 2 = (n * h) * h by ring]
    exact psi_mul_of_primeFactors_subset (mul_ne_zero hn0 hh0) hh0
      (Nat.primeFactors_mono (dvd_mul_left h n) (mul_ne_zero hn0 hh0))
  push_cast
  rw [hidx, hψN]
  ring

theorem Gamma0R_le_Gamma0Star' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0R N ≤ Gamma0Star N Δ ∧
      ((Gamma0R N).relIndex (Gamma0Star N Δ) : ℚ) = psi N / psi (nStar N Δ) := by
  refine ⟨fun γ hγ => ?_, relIndex_Gamma0R_Gamma0Star N Δ⟩
  have hh := hStar_pos N Δ
  have h1 : MulAut.conj (Dm (hStar N Δ)) γ ∈ (Gamma0R N).map (MulAut.conj (Dm (hStar N Δ))).toMonoidHom :=
    ⟨γ, hγ, rfl⟩
  rw [Gamma0R_map_conj_gen hh (hStar_sq_dvd N Δ)] at h1
  have h2 : MulAut.conj (Dm (hStar N Δ)) γ ∈ Gamma0R (nStar N Δ) :=
    Subgroup.map_mono (GammaUp_le _ _) |>.trans (Subgroup.map_mono (Gamma0_le_of_dvd (dvd_mul_right _ _)))
      |> fun h => h h1
  exact ⟨_, h2, by simp [Dstar, MulAut.conj_apply, mul_assoc]⟩

/-! ### [Nor : Γ*] = w*_Δ -/

theorem eq_one_of_isAtkinLehner_one {n R : ℕ} (h : IsAtkinLehner n R 1) : R = 1 := by
  obtain ⟨x, y, z, w, -, hm⟩ := h
  have h00 := congrFun (congrFun hm 0) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at h00 h11
  have hR : R ≠ 0 := by rintro rfl; simp at h00
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hs : Real.sqrt R ^ 2 = R := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have e : (R : ℝ) * (x * w) = 1 := by
    have : (1 : ℝ) * 1 = ((Real.sqrt R)⁻¹ * (R * x)) * ((Real.sqrt R)⁻¹ * (R * w)) := by rw [← h00, ← h11]
    field_simp at this
    rw [hs] at this
    have : (R : ℝ) * (R * (x * w) - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hR'
    · linear_combination h0
  have e' : (R : ℤ) * (x * w) = 1 := by exact_mod_cast e
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) e'

/-- The Q of an Atkin–Lehner element is unique. -/
theorem isAtkinLehner_unique {n Q Q' : ℕ} [NeZero n] (hQ : Q ∣ n) (hQ' : Q' ∣ n) {y : SL(2, ℝ)}
    (h1 : IsAtkinLehner n Q y) (h2 : IsAtkinLehner n Q' y) : Q = Q' := by
  have h3 := isAtkinLehner_mul_gen hQ hQ' (isAtkinLehner_inv h1) h2
  rw [inv_mul_cancel] at h3
  have h4 := eq_one_of_isAtkinLehner_one h3
  have hg0 : 0 < Nat.gcd Q Q' := Nat.gcd_pos_of_pos_left _ (Q_pos_of_dvd hQ)
  have e1 : Q / Nat.gcd Q Q' = 1 := Nat.eq_one_of_mul_eq_one_right h4
  have e2 : Q' / Nat.gcd Q Q' = 1 := Nat.eq_one_of_mul_eq_one_left h4
  have := Nat.div_mul_cancel (Nat.gcd_dvd_left Q Q')
  have := Nat.div_mul_cancel (Nat.gcd_dvd_right Q Q')
  rw [e1] at *; rw [e2] at *
  omega

theorem mem_Gamma0Star_iff {N : ℕ} {Δ : Subgroup (ZMod N)ˣ} {x : SL(2, ℝ)} :
    x ∈ Gamma0Star N Δ ↔ Dstar N Δ * x * (Dstar N Δ)⁻¹ ∈ Gamma0R (nStar N Δ) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem relIndex_Gamma0Star_normG (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Gamma0Star N Δ).relIndex (NormG (GammaDeltaR N Δ)) = wStar N Δ := by
  set L := NormG (GammaDeltaR N Δ)
  set K := (Gamma0Star N Δ).subgroupOf L
  set n := nStar N Δ
  let S := {Q : ℕ // Q ∣ n ∧ Nat.Coprime Q (n / Q) ∧ IsIotaStable N Δ Q}
  have hspec := fun g : L => (mem_normG_GammaDeltaR_iff' Δ g).1 g.2
  let φ : L → S := fun g => ⟨Classical.choose (hspec g), (Classical.choose_spec (hspec g)).1,
    (Classical.choose_spec (hspec g)).2.1, (Classical.choose_spec (hspec g)).2.2.1⟩
  have hφal : ∀ g : L, IsAtkinLehner n (φ g).1 (Dstar N Δ * g * (Dstar N Δ)⁻¹) := fun g =>
    (Classical.choose_spec (hspec g)).2.2.2
  have key : ∀ g g' : L, φ g = φ g' ↔ g⁻¹ * g' ∈ K := by
    intro g g'
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_Gamma0Star_iff,
      ← isAtkinLehner_one_iff']
    have hconj : Dstar N Δ * ((g : SL(2, ℝ))⁻¹ * g') * (Dstar N Δ)⁻¹ =
        (Dstar N Δ * g * (Dstar N Δ)⁻¹)⁻¹ * (Dstar N Δ * g' * (Dstar N Δ)⁻¹) := by group
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
    rintro ⟨Q, hQ, hc, hst⟩
    obtain ⟨w, hw⟩ := exists_isAtkinLehner' hQ hc
    have hmem := (conj_mem_normG_iff' Δ hQ hc hw).2 hst
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    have hal := hφal ⟨_, hmem⟩
    have : Dstar N Δ * ((Dstar N Δ)⁻¹ * w * Dstar N Δ) * (Dstar N Δ)⁻¹ = w := by group
    simp only [this] at hal
    exact isAtkinLehner_unique (φ _).2.1 hQ hal hw
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

/-! ### The order -/

theorem card_BG_GammaDeltaR_hStar' (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Nat.card (BG (GammaDeltaR N Δ)) : ℚ) = Δ.index * (psi N / psi (nStar N Δ)) * wStar N Δ := by
  rw [card_BG_GammaDeltaR_eq', ← Subgroup.relIndex_mul_relIndex (Gamma0R N) (Gamma0Star N Δ) _
    (Gamma0R_le_Gamma0Star' N Δ).1 (Gamma0Star_le_normG' N Δ), relIndex_Gamma0Star_normG]
  push_cast
  rw [relIndex_Gamma0R_Gamma0Star]
  ring

end

end NormalizerLean
