import NormalizerLean.LocalRels

/-!
# The global relations hold: `globalRels_mem_Gamma0`

* the local relators hold in Γ₀(N), by the embedding argument (12) of [BA]: words in w_{m_p}, S_{h(m_p)}
  have the shape μ·[[a, b], [Nc, d]] with a, b, c, d, μ² ∈ ℤ[1/p], and such an element of Γ₀(m_p) lies
  in Γ₀(N);
* [w_p, w_q] ∈ Γ₀(N), since w_p w_q and w_q w_p are both Atkin–Lehner elements for m_p m_q;
* [s_p, s_q] = 1;
* w_p s_q w_p⁻¹ s_q^{-m_p} ∈ Γ₀(N), which is (15) of [BA].
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### ℤ[1/p] -/

/-- `x ∈ ℤ[1/p]`. -/
def IsPLoc (p : ℕ) (x : ℝ) : Prop := ∃ (z : ℤ) (t : ℕ), x = z / (p : ℝ) ^ t

theorem IsPLoc.int (p : ℕ) (z : ℤ) : IsPLoc p z := ⟨z, 0, by simp⟩

theorem IsPLoc.add {p : ℕ} (hp : p ≠ 0) {x y : ℝ} (hx : IsPLoc p x) (hy : IsPLoc p y) :
    IsPLoc p (x + y) := by
  obtain ⟨z₁, t₁, rfl⟩ := hx
  obtain ⟨z₂, t₂, rfl⟩ := hy
  refine ⟨z₁ * p ^ t₂ + z₂ * p ^ t₁, t₁ + t₂, ?_⟩
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp
  push_cast
  field_simp
  ring

theorem IsPLoc.mul {p : ℕ} {x y : ℝ} (hx : IsPLoc p x) (hy : IsPLoc p y) :
    IsPLoc p (x * y) := by
  obtain ⟨z₁, t₁, rfl⟩ := hx
  obtain ⟨z₂, t₂, rfl⟩ := hy
  exact ⟨z₁ * z₂, t₁ + t₂, by push_cast; ring⟩

theorem IsPLoc.neg {p : ℕ} {x : ℝ} (hx : IsPLoc p x) : IsPLoc p (-x) := by
  obtain ⟨z, t, rfl⟩ := hx
  exact ⟨-z, t, by push_cast; ring⟩

theorem IsPLoc.inv_pow (p t : ℕ) : IsPLoc p ((p : ℝ) ^ t)⁻¹ := ⟨1, t, by simp⟩

/-! ### The embedding invariant -/

/-- `g = μ • [[a, b], [N c, d]]` with `μ², a, b, c, d ∈ ℤ[1/p]`. -/
def Emb (N p : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ μ : ℝ, IsPLoc p (μ ^ 2) ∧ ∃ a b c d : ℝ, IsPLoc p a ∧ IsPLoc p b ∧ IsPLoc p c ∧ IsPLoc p d ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) = μ • !![a, b; (N : ℝ) * c, d]

theorem Emb.one (N p : ℕ) : Emb N p 1 := by
  refine ⟨1, ⟨1, 0, by simp⟩, 1, 0, 0, 1, ⟨1, 0, by simp⟩, ⟨0, 0, by simp⟩, ⟨0, 0, by simp⟩,
    ⟨1, 0, by simp⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem Emb.mul {N p : ℕ} (hp : p ≠ 0) {g g' : SL(2, ℝ)} (hg : Emb N p g) (hg' : Emb N p g') :
    Emb N p (g * g') := by
  obtain ⟨μ, hμ, a, b, c, d, ha, hb, hc, hd, hgm⟩ := hg
  obtain ⟨μ', hμ', a', b', c', d', ha', hb', hc', hd', hgm'⟩ := hg'
  have hN : ∀ x, IsPLoc p x → IsPLoc p ((N : ℝ) * x) := fun x hx => by
    simpa using (IsPLoc.int p N).mul hx
  refine ⟨μ * μ', by rw [mul_pow]; exact hμ.mul hμ', a * a' + b * (N * c'), a * b' + b * d',
    c * a' + d * c', (N * c) * b' + d * d', ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.mul ha').add hp (hb.mul (hN _ hc'))
  · exact (ha.mul hb').add hp (hb.mul hd')
  · exact (hc.mul ha').add hp (hd.mul hc')
  · exact ((hN _ hc).mul hb').add hp (hd.mul hd')
  · rw [Matrix.SpecialLinearGroup.coe_mul, hgm, hgm', Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_fin_two]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem Emb.inv {N p : ℕ} {g : SL(2, ℝ)} (hg : Emb N p g) : Emb N p g⁻¹ := by
  obtain ⟨μ, hμ, a, b, c, d, ha, hb, hc, hd, hgm⟩ := hg
  refine ⟨μ, hμ, d, -b, -c, a, hd, hb.neg, hc.neg, ha, ?_⟩
  rw [coe_inv_of_coe_eq_smul hgm]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem Emb.lift {N p : ℕ} (hp : p ≠ 0) {α : Type*} (f : α → SL(2, ℝ)) (hf : ∀ a, Emb N p (f a))
    (ρ : FreeGroup α) : Emb N p (FreeGroup.lift f ρ) := by
  induction ρ using FreeGroup.induction_on with
  | one => simpa using Emb.one N p
  | of x => simpa using hf x
  | inv_of x _ => simpa using (hf x).inv
  | mul x y hx hy => simpa using hx.mul hp hy

/-- The embedding argument (12): an element of the invariant shape lying in Γ₀(p^{v_p(N)}) lies in
Γ₀(N). -/
theorem Emb.mem_of_mem {N p : ℕ} (hp : p.Prime) (hN : N ≠ 0) {g : SL(2, ℝ)} (hg : Emb N p g)
    (hm : g ∈ Gamma0R (mPart N p)) : g ∈ Gamma0R N := by
  obtain ⟨μ, ⟨e, t, hμ⟩, a, b, c, d, -, -, ⟨z, s, rfl⟩, -, hgm⟩ := hg
  obtain ⟨A, B, C, D, -, hmC, hgABCD⟩ := exists_entries_of_mem_Gamma0R hm
  refine mem_Gamma0R_of_entries A B C D hgABCD ?_
  -- the lower-left entry
  have hC : (C : ℝ) = μ * (N * (z / (p : ℝ) ^ s)) := by
    have := congrFun (congrFun hgm 1) 0
    rw [hgABCD] at this
    simpa using this
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hC2 : ((C ^ 2 * p ^ (t + 2 * s) : ℤ) : ℝ) = ((e * N ^ 2 * z ^ 2 : ℤ) : ℝ) := by
    push_cast
    rw [hC, mul_pow, hμ]
    field_simp
    ring
  have hC2' : C ^ 2 * (p : ℤ) ^ (t + 2 * s) = e * N ^ 2 * z ^ 2 := by exact_mod_cast hC2
  -- N = m K with gcd(K, p) = 1
  set m := mPart N p with hm_def
  set K := N / m with hK_def
  have hmN : m ∣ N := Nat.ordProj_dvd N p
  have hNmK : N = m * K := (Nat.mul_div_cancel' hmN).symm
  have hcopK : Nat.Coprime p K := Nat.coprime_ordCompl hp hN
  have hK2 : (K : ℤ) ^ 2 ∣ C ^ 2 := by
    have h1 : (K : ℤ) ^ 2 ∣ C ^ 2 * (p : ℤ) ^ (t + 2 * s) := by
      rw [hC2', hNmK]
      push_cast
      exact Dvd.intro (e * m ^ 2 * z ^ 2) (by ring)
    have hcop : IsCoprime ((K : ℤ) ^ 2) ((p : ℤ) ^ (t + 2 * s)) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast (Nat.Coprime.pow _ _ hcopK.symm)
    exact hcop.dvd_of_dvd_mul_right h1
  have hKC : (K : ℤ) ∣ C := (Int.pow_dvd_pow_iff two_ne_zero).1 hK2
  have hcopmK : IsCoprime (m : ℤ) (K : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast (Nat.Coprime.pow_left _ hcopK)
  rw [hNmK]
  push_cast
  exact hcopmK.mul_dvd hmC hKC

/-! ### The generators have the invariant shape -/

theorem Emb.of_isAtkinLehner {N p : ℕ} {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N (mPart N p) g) : Emb N p g := by
  obtain ⟨x, y, z, w, -, hgm⟩ := hg
  refine ⟨(Real.sqrt (mPart N p))⁻¹, ⟨1, N.factorization p, ?_⟩, (mPart N p : ℝ) * x, y, z,
    (mPart N p : ℝ) * w, ?_, IsPLoc.int p y, IsPLoc.int p z, ?_, hgm⟩
  · rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp [mPart]
  · exact ⟨mPart N p * x, 0, by simp⟩
  · exact ⟨mPart N p * w, 0, by simp⟩

theorem hPart_mPart_eq_pow {N p : ℕ} (hp : p.Prime) : ∃ j, hPart (mPart N p) = p ^ j := by
  unfold mPart
  by_cases h2 : p = 2
  · subst h2; exact ⟨_, hPart_two_pow _⟩
  by_cases h3 : p = 3
  · subst h3; exact ⟨_, hPart_three_pow _⟩
  exact ⟨0, by rw [hPart_prime_pow hp h2 h3]; simp⟩

theorem Emb.S {N p : ℕ} (hp : p.Prime) : Emb N p (S (hPart (mPart N p))) := by
  obtain ⟨j, hj⟩ := hPart_mPart_eq_pow (N := N) hp
  refine ⟨1, by simpa using IsPLoc.int p 1, 1, (hPart (mPart N p) : ℝ)⁻¹, 0, 1,
    by simpa using IsPLoc.int p 1, ?_, by simpa using IsPLoc.int p 0,
    by simpa using IsPLoc.int p 1, ?_⟩
  · rw [hj]; push_cast; exact IsPLoc.inv_pow p j
  · rw [coe_S]; simp

/-! ### Atkin–Lehner elements at a smaller level, and products -/

theorem isAtkinLehner_self_of_dvd {N Q : ℕ} (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : IsAtkinLehner Q Q g := by
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  obtain ⟨K, rfl⟩ := hQ
  refine ⟨x, y, K * z, w, by push_cast at hdet ⊢; linear_combination hdet, ?_⟩
  rw [hgm]
  congr 2
  push_cast
  ring

theorem isAtkinLehner_mul {N Q₁ Q₂ : ℕ} (hQ : Q₁ * Q₂ ∣ N) {g₁ g₂ : SL(2, ℝ)}
    (h₁ : IsAtkinLehner N Q₁ g₁) (h₂ : IsAtkinLehner N Q₂ g₂) :
    IsAtkinLehner N (Q₁ * Q₂) (g₁ * g₂) := by
  obtain ⟨x₁, y₁, z₁, w₁, hd₁, hg₁⟩ := h₁
  obtain ⟨x₂, y₂, z₂, w₂, hd₂, hg₂⟩ := h₂
  obtain ⟨L, rfl⟩ := hQ
  refine ⟨x₁ * x₂ + L * y₁ * z₂, Q₁ * x₁ * y₂ + Q₂ * w₂ * y₁, Q₂ * z₁ * x₂ + Q₁ * w₁ * z₂,
    L * z₁ * y₂ + w₁ * w₂, ?_, ?_⟩
  · push_cast at hd₁ hd₂ ⊢
    linear_combination ((Q₂ : ℤ) ^ 2 * x₂ * w₂ - Q₁ * Q₂ * L * y₂ * z₂) * hd₁ + (Q₁ : ℤ) * hd₂
  · rw [Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_fin_two]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ### Translations commute; (15) -/

theorem smul_mul_mul_smul_mul_eq {Q s : ℝ} (hs : s * s = Q) (hQ : Q ≠ 0)
    {W γ A T X : Matrix (Fin 2) (Fin 2) ℝ} (h : W * γ * A * T = Q • X) :
    (s⁻¹ • W) * γ * (s⁻¹ • A) * T = X := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h, smul_smul, inv_mul_inv_mul_eq_one hs hQ, one_smul]

theorem S_mul_comm (a b : ℕ) : S a * S b = S b * S a := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_S, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- (15) of [BA]: for an AL element g of level N = m k² L for Q = m, with k ∣ 24,
g S_k g⁻¹ S_k^{-m} ∈ Γ₀(N). -/
theorem interaction_mem {N m k L : ℕ} (hNL : N = m * k ^ 2 * L) (hm : m ≠ 0) (hk : k ≠ 0)
    (hk24 : k ∣ 24) {g : SL(2, ℝ)} (hg : IsAtkinLehner N m g) :
    g * S k * g⁻¹ * (S k ^ m)⁻¹ ∈ Gamma0R N := by
  subst hNL
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  -- x ≡ m w (mod k)
  have hdet' : (m : ℤ) * x * w - k ^ 2 * L * y * z = 1 := by
    have hmz : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hm
    apply mul_left_cancel₀ hmz
    push_cast at hdet
    linear_combination hdet
  have hxm : x * (m * w) ≡ 1 [ZMOD k] := by
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    exact ⟨k * L * y * z, by linear_combination hdet'⟩
  obtain ⟨e, he⟩ := Int.ModEq.dvd (modEq_of_mul_modEq_one hk24 hxm)
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hginv := coe_inv_of_coe_eq_smul hgm
  have hx : x = m * w - k * e := by linarith
  subst hx
  refine mem_Gamma0R_of_entries
    (m * w * (m * w - k * e) - L * k ^ 2 * y * z - L * k * m * (m * w - k * e) * z)
    (L * k * m * y * z + L * m ^ 2 * (m * w - k * e) * z - m * (m * w - k * e) * e)
    (-(((m * k ^ 2 * L : ℕ) : ℤ) * (L * k * z ^ 2)))
    (L ^ 2 * k ^ 2 * m ^ 2 * z ^ 2 - L * k ^ 2 * y * z + L * k * m * (m * w - k * e) * z +
      m * w * (m * w - k * e)) ?_ (by rw [dvd_neg]; exact dvd_mul_right _ _)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hgm, hginv, Matrix.SpecialLinearGroup.coe_inv, coe_S_pow,
    coe_S, adjugate_fin_two_of]
  apply smul_mul_mul_smul_mul_eq hs hmr
  rw [mul_fin_two, mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-! ### Assembly -/

theorem lift_map_eq {α β : Type*} (G : β → SL(2, ℝ)) (ι : α → β) (ρ : FreeGroup α) :
    FreeGroup.lift G (FreeGroup.map ι ρ) = FreeGroup.lift (G ∘ ι) ρ := by
  have : (FreeGroup.lift G).comp (FreeGroup.map ι) = FreeGroup.lift (G ∘ ι) :=
    FreeGroup.ext_hom _ _ (fun a => by simp)
  exact DFunLike.congr_fun this ρ

theorem mPart_ne_zero {N p : ℕ} (hp : p.Prime) : mPart N p ≠ 0 :=
  pow_ne_zero _ hp.ne_zero

theorem mPart_mul_mPart_dvd {N p q : ℕ} (hN : N ≠ 0) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    mPart N p * mPart N q ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq))
    (Nat.ordProj_dvd N p) (Nat.ordProj_dvd N q)

theorem bracket_eq_one_of_commute {G : Type*} [Group G] {x y : G} (h : x * y = y * x) :
    bracket x y = 1 := by
  have : bracket x y = (y * x)⁻¹ * (x * y) := by simp [bracket, mul_assoc]
  rw [this, h, inv_mul_cancel]

/-- **Stage-1 milestone**: the global relators hold, for any choice of AL elements. -/
theorem globalRels_mem_Gamma0' (N : ℕ) [NeZero N] (wg : N.primeFactors → SL(2, ℝ))
    (hw : ∀ p : N.primeFactors, IsAtkinLehner N (mPart N p) (wg p)) :
    ∀ ρ ∈ globalRels N,
      FreeGroup.lift (fun x : GGen N => match x.2 with
        | .w => wg x.1
        | .s => S (hPart (mPart N x.1))) ρ ∈ Gamma0R N := by
  intro ρ hρ
  have hN := NeZero.ne N
  simp only [globalRels, Set.mem_union, Set.mem_iUnion, Set.mem_image] at hρ
  rcases hρ with ⟨p, ρ', hρ', rfl⟩ | ⟨p, q, hpq, hρ⟩
  · -- the local relators, via (12)
    have hpP : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hpos : 0 < N.factorization p :=
      hpP.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors p.2)
    rw [lift_map_eq]
    have hGι : ((fun x : GGen N => match x.2 with
        | .w => wg x.1
        | .s => S (hPart (mPart N x.1))) ∘ (fun x : LGen => (p, x))) =
        (fun x : LGen => match x with
          | .w => wg p
          | .s => S (hPart ((p : ℕ) ^ N.factorization p))) := by
      funext x
      cases x <;> rfl
    rw [hGι]
    have hloc := localRels_mem_Gamma0' p (N.factorization p) hpP hpos
      (isAtkinLehner_self_of_dvd (Nat.ordProj_dvd N p) (hw p)) ρ' hρ'
    refine Emb.mem_of_mem hpP hN ?_ hloc
    refine Emb.lift hpP.ne_zero _ (fun x => ?_) ρ'
    cases x
    · exact Emb.of_isAtkinLehner (hw p)
    · exact Emb.S hpP
  · -- the interaction relators (1)
    have hpP : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hqP : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have hpq' : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
    have hdvd := mPart_mul_mPart_dvd hN hpP hqP hpq'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
    rcases hρ with rfl | rfl | rfl
    · -- [w_p, w_q]
      simp only [bracket, map_mul, map_inv, FreeGroup.lift_apply_of]
      have hX := isAtkinLehner_mul (by rwa [mul_comm]) (hw q) (hw p)
      have hY := isAtkinLehner_mul hdvd (hw p) (hw q)
      rw [mul_comm] at hX
      have hXN := isAtkinLehner_mem_normalizer' hdvd hX
      have := (mul_inv_mem_iff_inv_mul_mem hXN).1 (isAtkinLehner_mul_inv_mem' hdvd hX hY)
      simpa [mul_assoc] using this
    · -- [s_p, s_q]
      have := bracket_eq_one_of_commute (S_mul_comm (hPart (mPart N p)) (hPart (mPart N q)))
      simp only [bracket] at this
      simp only [bracket, map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [this]
      exact one_mem _
    · -- w_p s_q w_p⁻¹ = s_q^{m_p}
      simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      have hk0 : hPart (mPart N q) ≠ 0 := (hPart_pos _).ne'
      have hksq : hPart (mPart N q) ^ 2 ∣ mPart N q := hPart_sq_dvd (mPart_ne_zero hqP)
      obtain ⟨L, hL⟩ : mPart N p * hPart (mPart N q) ^ 2 ∣ N :=
        dvd_trans (mul_dvd_mul_left _ hksq) hdvd
      exact interaction_mem hL (mPart_ne_zero hpP) hk0 (hPart_dvd_24 _) (hw p)

end

end NormalizerLean
