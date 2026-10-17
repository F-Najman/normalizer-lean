module

public import NormalizerLean.Embed

@[expose] public section

/-!
# T6, part 2: the global presentation

G = ⟨w_p, s_p (p ∣ N) | local relations, [w_p, w_q], [s_p, s_q], w_p s_q w_p⁻¹ s_q^{−m_p}⟩.
The map Φ : G → B(N), w_p ↦ [w_{m_p}], s_p ↦ [S_{h(m_p)}], is well defined (Stage 1) and onto (T4).
For the order: let A_p = ⟨w_p, s_p⟩ (an image of the local presentation, so |A_p| ≤ |B(m_p)| by
T5), and X_T = ⟨A_p : p ∈ T⟩. For q ∉ T, w_q normalizes X_T and X_T normalizes ⟨s_q⟩, so
X_{T ∪ {q}} = X_T · A_q (collection). Hence |G| ≤ ∏_p |B(m_p)| = |B(N)| (T3), and Φ is bijective.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open Words

/-! ### Generalities -/

theorem mk_map_eq {α β : Type*} {R : Set (FreeGroup β)} (ι : α → β) (ρ : FreeGroup α) :
    PresentedGroup.mk R (FreeGroup.map ι ρ) = FreeGroup.lift (fun a => PresentedGroup.of (ι a)) ρ := by
  have : (PresentedGroup.mk R).comp (FreeGroup.map ι) =
      FreeGroup.lift (fun a => PresentedGroup.of (ι a)) :=
    FreeGroup.ext_hom _ _ (fun a => by simp [PresentedGroup.of])
  exact DFunLike.congr_fun this ρ

theorem mul_comm_of_bracket {G : Type*} [Group G] {x y : G} (h : bracket x y = 1) :
    x * y = y * x := by
  unfold bracket at h
  calc x * y = (y * x) * (x⁻¹ * y⁻¹ * x * y) := by group
    _ = y * x := by rw [h, mul_one]

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g s : G} {k j : ℤ}
    (h1 : g * s * g⁻¹ = s ^ k) (h2 : g⁻¹ * s * g = s ^ j) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨n, rfl⟩
    have : g * s ^ n * g⁻¹ = (g * s * g⁻¹) ^ n := conj_zpow.symm
    rw [this, h1, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem_zpowers s _
  · rintro ⟨n, hn⟩
    have hh : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    have : g⁻¹ * s ^ n * g = (g⁻¹ * s * g) ^ n := by
      have := conj_zpow (a := g⁻¹) (b := s) (i := n)
      rw [inv_inv] at this
      exact this.symm
    rw [hh, ← hn, this, h2, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem_zpowers s _

/-! ### The presented group and its relations -/

variable (N : ℕ)

/-- The global presented group. -/
abbrev GP : Type := PresentedGroup (globalRels N)

/-- The generator (p, l). -/
abbrev gen (p : N.primeFactors) (l : LGen) : GP N := PresentedGroup.of (p, l)

theorem loc_rel_GP (p : N.primeFactors) {ρ : FreeGroup LGen}
    (hρ : ρ ∈ localRels p (N.factorization p)) :
    FreeGroup.lift (fun l => gen N p l) ρ = 1 := by
  rw [← mk_map_eq]
  exact PresentedGroup.one_of_mem
    (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨p, Set.mem_image_of_mem _ hρ⟩))

theorem gen_w_sq (p : N.primeFactors) : gen N p .w ^ 2 = 1 := by
  have := loc_rel_GP N p (ρ := w ^ 2) (by simp [localRels, localRelList])
  simpa using this

theorem gen_w_inv (p : N.primeFactors) : (gen N p .w)⁻¹ = gen N p .w := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, gen_w_sq]

theorem gen_s_pow (p : N.primeFactors) : gen N p .s ^ hPart (mPart N p) = 1 := by
  have := loc_rel_GP N p (ρ := s ^ hPart ((p : ℕ) ^ N.factorization p))
    (by simp [localRels, localRelList])
  simp only [map_pow, FreeGroup.lift_apply_of] at this
  exact this

theorem cross_mem {p q : N.primeFactors} (hpq : p ≠ q) :
    bracket (FreeGroup.of (p, LGen.w)) (FreeGroup.of (q, LGen.w)) ∈ globalRels N ∧
      bracket (FreeGroup.of (p, LGen.s)) (FreeGroup.of (q, LGen.s)) ∈ globalRels N ∧
      FreeGroup.of (p, LGen.w) * FreeGroup.of (q, LGen.s) * (FreeGroup.of (p, LGen.w))⁻¹ *
        (FreeGroup.of (q, LGen.s) ^ mPart N p)⁻¹ ∈ globalRels N := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨q,
      Set.mem_iUnion.2 ⟨hpq, by simp⟩⟩⟩)

theorem gen_w_comm {p q : N.primeFactors} (hpq : p ≠ q) :
    gen N p .w * gen N q .w = gen N q .w * gen N p .w := by
  have h := PresentedGroup.one_of_mem (cross_mem N hpq).1
  simp only [bracket, map_mul, map_inv] at h
  exact mul_comm_of_bracket h

theorem gen_s_comm {p q : N.primeFactors} (hpq : p ≠ q) :
    gen N p .s * gen N q .s = gen N q .s * gen N p .s := by
  have h := PresentedGroup.one_of_mem (cross_mem N hpq).2.1
  simp only [bracket, map_mul, map_inv] at h
  exact mul_comm_of_bracket h

theorem gen_w_s_conj {p q : N.primeFactors} (hpq : p ≠ q) :
    gen N p .w * gen N q .s * (gen N p .w)⁻¹ = gen N q .s ^ mPart N p := by
  have h := PresentedGroup.one_of_mem (cross_mem N hpq).2.2
  simp only [map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.1 h

/-! ### The local subgroups A_p and the collection argument -/

/-- ι_p : local presentation → G. -/
def iotaP (p : N.primeFactors) : PresentedGroup (localRels p (N.factorization p)) →* GP N :=
  PresentedGroup.toGroup (f := fun l => gen N p l) (fun _ hρ => loc_rel_GP N p hρ)

/-- A_p = ⟨w_p, s_p⟩. -/
abbrev Aloc (p : N.primeFactors) : Subgroup (GP N) := (iotaP N p).range

theorem gen_mem_Aloc (p : N.primeFactors) (l : LGen) : gen N p l ∈ Aloc N p :=
  ⟨PresentedGroup.of l, PresentedGroup.toGroup.of _⟩

/-- The generators of the primes in T. -/
def gensT (T : Finset N.primeFactors) : Set (GP N) := {g | ∃ p ∈ T, ∃ l, g = gen N p l}

/-- X_T = ⟨A_p : p ∈ T⟩. -/
abbrev XT (T : Finset N.primeFactors) : Subgroup (GP N) := Subgroup.closure (gensT N T)

theorem conj_w_mem {T : Finset N.primeFactors} {q : N.primeFactors} (hq : q ∉ T) {x : GP N}
    (hx : x ∈ XT N T) : gen N q .w * x * (gen N q .w)⁻¹ ∈ XT N T := by
  have hle : (XT N T).map (MulAut.conj (gen N q .w)).toMonoidHom ≤ XT N T := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨p, hp, l, rfl⟩, rfl⟩
    have hqp : q ≠ p := fun h => hq (h ▸ hp)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    cases l
    · rw [gen_w_comm N hqp, mul_inv_cancel_right]
      exact Subgroup.subset_closure ⟨p, hp, .w, rfl⟩
    · rw [gen_w_s_conj N hqp]
      exact pow_mem (Subgroup.subset_closure (show gen N p .s ∈ gensT N T from ⟨p, hp, .s, rfl⟩)) _
  have := hle (Subgroup.mem_map_of_mem _ hx)
  simpa using this

theorem XT_le_normalizer {T : Finset N.primeFactors} {q : N.primeFactors} (hq : q ∉ T) :
    XT N T ≤ Subgroup.normalizer (Subgroup.zpowers (gen N q .s) : Set (GP N)) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨p, hp, l, rfl⟩
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  cases l
  · have h1 := gen_w_s_conj N hpq
    have h1' : (gen N p .w)⁻¹ * gen N q .s * gen N p .w = gen N q .s ^ mPart N p := by
      have h := h1
      rw [gen_w_inv] at h ⊢
      exact h
    exact mem_normalizer_zpowers (k := (mPart N p : ℤ)) (j := (mPart N p : ℤ))
      (by rw [h1, zpow_natCast]) (by rw [h1', zpow_natCast])
  · have hc := gen_s_comm N hpq
    exact mem_normalizer_zpowers (k := 1) (j := 1)
      (by rw [hc, mul_inv_cancel_right, zpow_one])
      (by rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul, zpow_one])

theorem conj_s_mem {T : Finset N.primeFactors} {q : N.primeFactors} (hq : q ∉ T) {x : GP N}
    (hx : x ∈ XT N T) : x⁻¹ * gen N q .s * x ∈ Subgroup.zpowers (gen N q .s) := by
  have hn := XT_le_normalizer N hq (inv_mem hx)
  rw [Subgroup.mem_normalizer_iff] at hn
  have := (hn (gen N q .s)).1 (Subgroup.mem_zpowers _)
  rwa [inv_inv] at this

/-- Collection: X_{T ∪ {q}} = X_T · A_q. -/
theorem collect {T : Finset N.primeFactors} {q : N.primeFactors} (hq : q ∉ T) {z : GP N}
    (hz : z ∈ XT N (insert q T)) : ∃ x ∈ XT N T, ∃ y ∈ Aloc N q, z = x * y := by
  induction hz using Subgroup.closure_induction_left with
  | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  | mul_left g hg z hz ih =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ih
    obtain ⟨p, hp, l, rfl⟩ := hg
    rcases Finset.mem_insert.1 hp with rfl | hpT
    · cases l
      · exact ⟨_, conj_w_mem N hq hx, _, mul_mem (gen_mem_Aloc N p .w) hy, by group⟩
      · exact ⟨x, hx, _, mul_mem (Subgroup.zpowers_le.2 (gen_mem_Aloc N p .s)
          (conj_s_mem N hq hx)) hy, by group⟩
    · exact ⟨_, mul_mem (Subgroup.subset_closure ⟨p, hpT, l, rfl⟩) hx, y, hy, by group⟩
  | inv_mul_cancel g hg z hz ih =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ih
    obtain ⟨p, hp, l, rfl⟩ := hg
    rcases Finset.mem_insert.1 hp with rfl | hpT
    · cases l
      · rw [gen_w_inv]
        exact ⟨_, conj_w_mem N hq hx, _, mul_mem (gen_mem_Aloc N p .w) hy, by group⟩
      · exact ⟨x, hx, _, mul_mem (inv_mem (Subgroup.zpowers_le.2 (gen_mem_Aloc N p .s)
          (conj_s_mem N hq hx))) hy, by group⟩
    · exact ⟨_, mul_mem (inv_mem (Subgroup.subset_closure ⟨p, hpT, l, rfl⟩)) hx, y, hy,
        by group⟩

variable [NeZero N]

omit [NeZero N] in
theorem Aloc_finite_card (p : N.primeFactors) :
    Finite (Aloc N p) ∧ Nat.card (Aloc N p) ≤ Nat.card (B (mPart N p)) := by
  have hpP := Nat.prime_of_mem_primeFactors p.2
  have hcard := card_localPres p (N.factorization p) hpP (factorization_pos_of_mem p.2)
  have : NeZero ((p : ℕ) ^ N.factorization p) := ⟨pow_ne_zero _ hpP.ne_zero⟩
  have := finite_B' ((p : ℕ) ^ N.factorization p)
  have : Finite (PresentedGroup (localRels p (N.factorization p))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hs := (iotaP N p).rangeRestrict_surjective
  refine ⟨Finite.of_surjective _ hs, ?_⟩
  calc Nat.card (Aloc N p) ≤ Nat.card (PresentedGroup (localRels p (N.factorization p))) :=
        Nat.card_le_card_of_surjective _ hs
    _ = Nat.card (B (mPart N p)) := hcard

omit [NeZero N] in
theorem XT_card (T : Finset N.primeFactors) :
    Finite (XT N T) ∧ Nat.card (XT N T) ≤ ∏ p ∈ T, Nat.card (B (mPart N p)) := by
  induction T using Finset.induction_on with
  | empty =>
    have : XT N ∅ = ⊥ := by
      rw [XT, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨p, hp, -⟩
      simp at hp
    rw [this]
    exact ⟨inferInstance, by simp⟩
  | insert q T hq ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨hfinA, hcardA⟩ := Aloc_finite_card N q
    have hXle : XT N T ≤ XT N (insert q T) := Subgroup.closure_mono (by
      rintro _ ⟨p, hp, l, rfl⟩
      exact ⟨p, Finset.mem_insert_of_mem hp, l, rfl⟩)
    have hAle : Aloc N q ≤ XT N (insert q T) := by
      rw [Aloc, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        Subgroup.closure_le]
      rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
      rw [iotaP, PresentedGroup.toGroup.of]
      exact Subgroup.subset_closure ⟨q, Finset.mem_insert_self q T, l, rfl⟩
    let μ : XT N T × Aloc N q → XT N (insert q T) :=
      fun xy => ⟨xy.1 * xy.2, mul_mem (hXle xy.1.2) (hAle xy.2.2)⟩
    have hμ : Function.Surjective μ := by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := collect N hq hz
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
    refine ⟨Finite.of_surjective μ hμ, ?_⟩
    calc Nat.card (XT N (insert q T)) ≤ Nat.card (XT N T × Aloc N q) :=
          Nat.card_le_card_of_surjective μ hμ
      _ = Nat.card (XT N T) * Nat.card (Aloc N q) := Nat.card_prod _ _
      _ ≤ (∏ p ∈ T, Nat.card (B (mPart N p))) * Nat.card (B (mPart N q)) :=
          Nat.mul_le_mul hcard hcardA
      _ = ∏ p ∈ insert q T, Nat.card (B (mPart N p)) := by rw [Finset.prod_insert hq, mul_comm]

omit [NeZero N] in
theorem XT_univ : XT N Finset.univ = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of]
  apply Subgroup.closure_mono
  rintro _ ⟨⟨p, l⟩, rfl⟩
  exact ⟨p, Finset.mem_univ _, l, rfl⟩

/-- ∏_{p ∣ N} |B(m_p)| = |B(N)| (T3). -/
theorem prod_card_B_mPart :
    ∏ p ∈ (Finset.univ : Finset N.primeFactors), Nat.card (B (mPart N p)) = Nat.card (B N) := by
  have hN := NeZero.ne N
  rw [card_B_explicit' N]
  apply Nat.cast_injective (R := ℚ)
  rw [rhs_eq_prod hN, Nat.cast_prod]
  have e : ∏ p : N.primeFactors, (Nat.card (B (mPart N p)) : ℚ) =
      ∏ p ∈ N.primeFactors, (Nat.card (B (mPart N p)) : ℚ) :=
    Finset.prod_coe_sort N.primeFactors (fun p => (Nat.card (B (mPart N p)) : ℚ))
  rw [e]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP := Nat.prime_of_mem_primeFactors hp
  rw [show mPart N p = p ^ N.factorization p from rfl,
    card_B_prime_pow hpP (factorization_pos_of_mem hp), rfac]
  split_ifs <;> simp

theorem card_GP_le : Finite (GP N) ∧ Nat.card (GP N) ≤ Nat.card (B N) := by
  obtain ⟨hfin, hcard⟩ := XT_card N Finset.univ
  rw [XT_univ] at hfin hcard
  rw [Subgroup.card_top] at hcard
  exact ⟨Finite.of_equiv _ Subgroup.topEquiv.toEquiv, hcard.trans (prod_card_B_mPart N).le⟩

/-! ### The map Φ : G → B(N) -/

/-- A choice of Atkin–Lehner element w_{m_p} for each p ∣ N. -/
def wgC (p : N.primeFactors) : SL(2, ℝ) :=
  (exists_AL_loc (N := N) (Nat.prime_of_mem_primeFactors p.2)).choose

theorem wgC_spec (p : N.primeFactors) : IsAtkinLehner N (mPart N p) (wgC N p) :=
  (exists_AL_loc (N := N) (Nat.prime_of_mem_primeFactors p.2)).choose_spec

/-- w_p ↦ w_{m_p}, s_p ↦ S_{h(m_p)}. -/
def GF : GGen N → SL(2, ℝ) := fun x => match x.2 with
  | .w => wgC N x.1
  | .s => S (hPart (mPart N x.1))

theorem GF_mem : ∀ x, GF N x ∈ Norm0 N
  | (p, .w) => isAtkinLehner_mem_normalizer' (mPart_dvd N p) (wgC_spec N p)
  | (p, .s) => S_mem_normalizer' (hPart_mPart_dvd N p)

/-- Φ : G → B(N). -/
def PhiG : GP N →* B N :=
  PresentedGroup.toGroup (f := fun x => (QuotientGroup.mk ⟨GF N x, GF_mem N x⟩ : B N))
    (fun ρ hρ => lift_mk_eq_one _ _ (globalRels_mem_Gamma0' N (wgC N) (wgC_spec N) ρ hρ))

theorem PhiG_w (p : N.primeFactors) :
    PhiG N (gen N p .w) = QuotientGroup.mk ⟨wgC N p, GF_mem N (p, .w)⟩ :=
  PresentedGroup.toGroup.of _

theorem PhiG_s (p : N.primeFactors) :
    PhiG N (gen N p .s) = QuotientGroup.mk ⟨S (hPart (mPart N p)), GF_mem N (p, .s)⟩ :=
  PresentedGroup.toGroup.of _

theorem PhiG_surjective : Function.Surjective (PhiG N) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_localGens' N, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨q, hq, hx⟩ := hx
  rcases hx with hAL | hS
  · obtain ⟨hmem, rfl⟩ := hAL.2 _ (wgC_spec N ⟨q, hq⟩)
    exact ⟨gen N ⟨q, hq⟩ .w, PhiG_w N _⟩
  · obtain ⟨hmem, rfl⟩ := hS
    exact ⟨gen N ⟨q, hq⟩ .s, PhiG_s N _⟩

theorem PhiG_bijective : Function.Bijective (PhiG N) := by
  obtain ⟨hfin, hle⟩ := card_GP_le N
  exact (PhiG_surjective N).bijective_of_nat_card_le hle

/-- **T6**, the global presentation. -/
theorem globalPresentation' (N : ℕ) [NeZero N] :
    ∃ φ : PresentedGroup (globalRels N) ≃* B N, ∀ p : N.primeFactors,
      (φ (.of (p, .w))).IsALClass (mPart N p) ∧
        (φ (.of (p, .s))).IsClassOf (S (hPart (mPart N p))) := by
  refine ⟨MulEquiv.ofBijective _ (PhiG_bijective N), fun p => ⟨?_, ?_⟩⟩
  · rw [MulEquiv.ofBijective_apply, PhiG_w]
    exact isALClass_mk (mPart_dvd N p) (wgC_spec N p)
  · rw [MulEquiv.ofBijective_apply, PhiG_s]
    exact B.isClassOf_mk _

end

end NormalizerLean
