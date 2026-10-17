module

public import NormalizerLean.Local

@[expose] public section

/-!
# T6, part 1: B_p ≅ B(m_p) ((12) of [BA])

Fix p ∣ N, a = v_p(N), m = m_p = pᵃ, and an Atkin–Lehner element w for m at level N (it is also one
at level m). For the local presentation P = ⟨w, s | localRels p a⟩ and F : w ↦ w, s ↦ S_{h(m)}:

* α : P → B(N), u ↦ [F(u)]_N, is well defined by the embedding argument (12) (Stage 1);
* its range is B_p = ⟨[w_{m_p}], [S_{h(m_p)}]⟩;
* α is injective: if F(u) ∈ Γ₀(N) ⊆ Γ₀(m), then u = 1 in P, because P → B(m), u ↦ [F(u)]_m, is
  the T5 isomorphism (its generators have the same classes as Fricke's);
* φ = (T5 iso) ∘ α⁻¹ : B_p → B(m) sends the class of g mod Γ₀(N) to the class of g mod Γ₀(m).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open Words

theorem Gamma0R_mono {m N : ℕ} (h : m ∣ N) : Gamma0R N ≤ Gamma0R m :=
  Subgroup.map_mono (Gamma0_le_of_dvd h)

theorem toGroup_mk {α G : Type*} [Group G] {R : Set (FreeGroup α)} {f : α → G}
    (h : ∀ r ∈ R, FreeGroup.lift f r = 1) (u : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk R u) = FreeGroup.lift f u :=
  rfl

theorem factorization_pos_of_mem {N p : ℕ} (hp : p ∈ N.primeFactors) : 0 < N.factorization p :=
  (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (Nat.mem_primeFactors.1 hp).2.2
    (Nat.dvd_of_mem_primeFactors hp)

instance neZero_mPart {N p : ℕ} [Fact p.Prime] : NeZero (mPart N p) :=
  ⟨mPart_ne_zero Fact.out⟩

section

variable {N p : ℕ} [NeZero N] {wg : SL(2, ℝ)} (hw : IsAtkinLehner N (mPart N p) wg)

include hw

theorem locF_mem_N : ∀ x, locF wg (hPart (mPart N p)) x ∈ Norm0 N
  | .w => isAtkinLehner_mem_normalizer' (mPart_dvd N p) hw
  | .s => S_mem_normalizer' (hPart_mPart_dvd N p)

omit [NeZero N] in
theorem locF_mem_m [NeZero (mPart N p)] : ∀ x, locF wg (hPart (mPart N p)) x ∈ Norm0 (mPart N p)
  | .w => isAtkinLehner_mem_normalizer' dvd_rfl (isAtkinLehner_self_of_dvd (mPart_dvd N p) hw)
  | .s => S_h_mem _

variable (hp : p ∈ N.primeFactors)

include hp

omit [NeZero N] in
theorem locF_rels_m : ∀ ρ ∈ localRels p (N.factorization p),
    FreeGroup.lift (locF wg (hPart (mPart N p))) ρ ∈ Gamma0R (mPart N p) := by
  intro ρ hρ
  have hloc := localRels_mem_Gamma0' p (N.factorization p) (Nat.prime_of_mem_primeFactors hp)
    (factorization_pos_of_mem hp) (isAtkinLehner_self_of_dvd (Nat.ordProj_dvd N p) hw) ρ hρ
  rw [locF_eq] at hloc
  exact hloc

theorem locF_rels_N : ∀ ρ ∈ localRels p (N.factorization p),
    FreeGroup.lift (locF wg (hPart (mPart N p))) ρ ∈ Gamma0R N := by
  intro ρ hρ
  have hpP := Nat.prime_of_mem_primeFactors hp
  refine Emb.mem_of_mem hpP (NeZero.ne N) ?_ (locF_rels_m hw hp ρ hρ)
  refine Emb.lift hpP.ne_zero _ (fun x => ?_) ρ
  cases x
  · exact Emb.of_isAtkinLehner hw
  · exact Emb.S hpP

/-- α : P → B(N). -/
def alphaN : PresentedGroup (localRels p (N.factorization p)) →* B N :=
  PresentedGroup.toGroup (f := fun x =>
      (QuotientGroup.mk ⟨locF wg (hPart (mPart N p)) x, locF_mem_N hw x⟩ : B N))
    (fun ρ hρ => lift_mk_eq_one _ _ (locF_rels_N hw hp ρ hρ))

theorem alphaN_mk (u : FreeGroup LGen) :
    alphaN hw hp (PresentedGroup.mk _ u) =
      QuotientGroup.mk ⟨FreeGroup.lift (locF wg (hPart (mPart N p))) u,
        lift_mem_Norm0 _ (locF_mem_N hw) u⟩ :=
  lift_mk_eq _ _ u

theorem alphaN_range : (alphaN hw hp).range = Bloc N p := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [alphaN, PresentedGroup.toGroup.of]
    cases x
    · exact Subgroup.subset_closure (Or.inl (isALClass_mk (mPart_dvd N p) hw))
    · exact Subgroup.subset_closure (Or.inr (B.isClassOf_mk _))
  · rw [Bloc, Subgroup.closure_le]
    rintro x (hAL | hS)
    · obtain ⟨hmem, rfl⟩ := hAL.2 wg hw
      exact ⟨PresentedGroup.of .w, PresentedGroup.toGroup.of _⟩
    · obtain ⟨hmem, rfl⟩ := hS
      exact ⟨PresentedGroup.of .s, PresentedGroup.toGroup.of _⟩

/-- The T5 map, evaluated on a word: the class mod Γ₀(m) of F(u). -/
theorem presHom_local_mk [NeZero (mPart N p)] (u : FreeGroup LGen) :
    presHom (mPart N p) (localRels_fricke p (N.factorization p) (Nat.prime_of_mem_primeFactors hp)
        (factorization_pos_of_mem hp) (mPart_ne_zero (Nat.prime_of_mem_primeFactors hp)))
        (PresentedGroup.mk _ u) =
      QuotientGroup.mk ⟨FreeGroup.lift (locF wg (hPart (mPart N p))) u,
        lift_mem_Norm0 _ (locF_mem_m hw) u⟩ := by
  change FreeGroup.lift (fun x => (QuotientGroup.mk ⟨locF (fricke (mPart N p) (NeZero.ne _))
    (hPart (mPart N p)) x, locF_fricke_mem (mPart N p) x⟩ : B (mPart N p))) u = _
  rw [← lift_mk_eq _ (locF_mem_m hw)]
  refine congrArg (fun f => FreeGroup.lift f u) (funext fun x => ?_)
  cases x
  · rw [B.mk_eq_mk_iff]
    exact (mul_inv_mem_iff_inv_mul_mem (fricke_mem_Norm0 _)).1
      (isAtkinLehner_mul_inv_mem' dvd_rfl (fricke_isAtkinLehner _ _)
        (isAtkinLehner_self_of_dvd (mPart_dvd N p) hw))
  · rfl

theorem alphaN_injective : Function.Injective (alphaN hw hp) := by
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have : NeZero (p ^ N.factorization p) := neZero_mPart
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨u, rfl⟩ := PresentedGroup.mk_surjective _ y
  rw [alphaN_mk, B.mk_eq_one_iff] at hy
  have h1 := presHom_local_mk hw hp u
  rw [(B.mk_eq_one_iff _).2 (Gamma0R_mono (mPart_dvd N p) hy)] at h1
  exact (presHom_local_bijective p (N.factorization p) (Nat.prime_of_mem_primeFactors hp)
    (factorization_pos_of_mem hp)).1 (h1.trans (map_one _).symm)

end

/-- **T6**, (12). -/
theorem localEmbedding' (N p : ℕ) [NeZero N] (hp : p ∈ N.primeFactors) :
    ∃ φ : Bloc N p ≃* B (mPart N p),
      ∀ (x : Bloc N p) (g : SL(2, ℝ)), (x : B N).IsClassOf g → (φ x).IsClassOf g := by
  have hpP := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpP⟩
  have : NeZero (p ^ N.factorization p) := neZero_mPart
  obtain ⟨wg, hw⟩ := exists_AL_loc (N := N) hpP
  have hinj := alphaN_injective hw hp
  let e1 := MonoidHom.ofInjective hinj
  let e2 := MulEquiv.subgroupCongr (alphaN_range hw hp)
  have hbij : Function.Bijective (presHom (mPart N p) (localRels_fricke p (N.factorization p) hpP
      (factorization_pos_of_mem hp) (mPart_ne_zero hpP))) :=
    presHom_local_bijective p (N.factorization p) hpP (factorization_pos_of_mem hp)
  let e3 := MulEquiv.ofBijective _ hbij
  refine ⟨(e2.symm.trans e1.symm).trans e3, ?_⟩
  rintro x g ⟨hg, hxg⟩
  obtain ⟨u, hu⟩ := PresentedGroup.mk_surjective _ (e1.symm (e2.symm x))
  have hαy : alphaN hw hp (PresentedGroup.mk _ u) = (x : B N) := by
    rw [hu, ← MonoidHom.ofInjective_apply hinj, MulEquiv.apply_symm_apply]
    rfl
  rw [alphaN_mk, hxg, B.mk_eq_mk_iff] at hαy
  have hγ := Gamma0R_mono (mPart_dvd N p) hαy
  have hFu := lift_mem_Norm0 _ (locF_mem_m hw) u
  have hgm : g ∈ Norm0 (mPart N p) := by
    have := mul_mem hFu (Gamma0R_le_Norm0 _ hγ)
    rwa [mul_inv_cancel_left] at this
  refine ⟨hgm, ?_⟩
  change e3 (e1.symm (e2.symm x)) = _
  rw [← hu, MulEquiv.ofBijective_apply]
  rw [presHom_local_mk hw hp u, B.mk_eq_mk_iff]
  exact hγ

end

end NormalizerLean
