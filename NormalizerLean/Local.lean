import NormalizerLean.LocalCerts
import NormalizerLean.LocalRels
import NormalizerLean.Gen

/-!
# T5: the local presentations

For m = pᵃ, the map PresentedGroup (localRels p a) → B(m), w ↦ [w_m], s ↦ [S_{h(m)}], is well
defined (Stage 1: the relators hold for the Fricke element), surjective (T4 at level m), and both
groups have the same order: the coset certificates in `LocalCerts.lean` give the order of the
presented group, and T3 gives |B(pᵃ)|.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open Words

/-! ### Words evaluated in B(N) -/

theorem lift_mem_Norm0 {N : ℕ} {α : Type*} (f : α → SL(2, ℝ)) (hf : ∀ a, f a ∈ Norm0 N)
    (ρ : FreeGroup α) : FreeGroup.lift f ρ ∈ Norm0 N := by
  rw [← coe_lift_subtype f hf]
  exact Subtype.prop _

/-- The B(N)-valued lift is the class of the SL₂(ℝ)-valued lift. -/
theorem lift_mk_eq {N : ℕ} {α : Type*} (f : α → SL(2, ℝ)) (hf : ∀ a, f a ∈ Norm0 N)
    (ρ : FreeGroup α) :
    FreeGroup.lift (fun a => (QuotientGroup.mk ⟨f a, hf a⟩ : B N)) ρ =
      QuotientGroup.mk ⟨FreeGroup.lift f ρ, lift_mem_Norm0 f hf ρ⟩ := by
  have hq : (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N))).comp
      (FreeGroup.lift (fun a => (⟨f a, hf a⟩ : Norm0 N))) =
      FreeGroup.lift (fun a => (QuotientGroup.mk ⟨f a, hf a⟩ : B N)) :=
    FreeGroup.ext_hom _ _ (fun a => by simp)
  rw [← hq, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  congr 1
  exact Subtype.ext (coe_lift_subtype f hf ρ)

theorem lift_mk_eq_one {N : ℕ} {α : Type*} (f : α → SL(2, ℝ)) (hf : ∀ a, f a ∈ Norm0 N)
    {ρ : FreeGroup α} (hρ : FreeGroup.lift f ρ ∈ Gamma0R N) :
    FreeGroup.lift (fun a => (QuotientGroup.mk ⟨f a, hf a⟩ : B N)) ρ = 1 := by
  rw [lift_mk_eq]
  exact (B.mk_eq_one_iff _).2 hρ

/-! ### The map from a two-generator presentation to B(m) -/

theorem locF_fricke_mem (m : ℕ) [NeZero m] :
    ∀ x, locF (fricke m (NeZero.ne m)) (hPart m) x ∈ Norm0 m
  | .w => fricke_mem_Norm0 m
  | .s => S_h_mem m

/-- w ↦ [w_m], s ↦ [S_{h(m)}], for any relators that hold for the Fricke element. -/
def presHom (m : ℕ) [NeZero m] {R : Set (FreeGroup LGen)}
    (hR : ∀ ρ ∈ R, FreeGroup.lift (locF (fricke m (NeZero.ne m)) (hPart m)) ρ ∈ Gamma0R m) :
    PresentedGroup R →* B m :=
  PresentedGroup.toGroup (f := fun x =>
      (QuotientGroup.mk ⟨locF (fricke m (NeZero.ne m)) (hPart m) x, locF_fricke_mem m x⟩ : B m))
    (fun ρ hρ => lift_mk_eq_one _ _ (hR ρ hρ))

section presHom

variable {m : ℕ} [NeZero m] {R : Set (FreeGroup LGen)}
  (hR : ∀ ρ ∈ R, FreeGroup.lift (locF (fricke m (NeZero.ne m)) (hPart m)) ρ ∈ Gamma0R m)

theorem presHom_w :
    presHom m hR (.of .w) = QuotientGroup.mk ⟨fricke m (NeZero.ne m), fricke_mem_Norm0 m⟩ :=
  PresentedGroup.toGroup.of _

theorem presHom_s : presHom m hR (.of .s) = sC m :=
  PresentedGroup.toGroup.of _

theorem presHom_w_isALClass : (presHom m hR (.of .w)).IsALClass m := by
  rw [presHom_w]
  exact isALClass_mk dvd_rfl (fricke_isAtkinLehner m (NeZero.ne m))

theorem presHom_s_isClassOf : (presHom m hR (.of .s)).IsClassOf (S (hPart m)) := by
  rw [presHom_s]
  exact B.isClassOf_mk _

/-- At a prime power the map is onto (T4). -/
theorem presHom_surjective {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hm : m = p ^ a) :
    Function.Surjective (presHom m hR) := by
  subst hm
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_localGens' (p ^ a), Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨q, hq, hx⟩ := hx
  rw [Nat.primeFactors_prime_pow ha.ne' hp, Finset.mem_singleton] at hq
  subst hq
  have hmp : mPart (q ^ a) q = q ^ a := by simp [mPart, hp.factorization_self]
  rcases hx with hAL | hS
  · rw [hmp] at hAL
    obtain ⟨hmem, rfl⟩ := hAL.2 _ (fricke_isAtkinLehner (q ^ a) (NeZero.ne _))
    exact ⟨_, presHom_w hR⟩
  · rw [hmp] at hS
    obtain ⟨hmem, rfl⟩ := hS
    exact ⟨_, presHom_s hR⟩

end presHom

/-! ### Orders -/

theorem card_B_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    Nat.card (B (p ^ a)) = if p = 2 then f₂ a else if p = 3 then f₃ a else 2 := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [card_B_explicit', Nat.primeFactors_prime_pow ha.ne' hp, factorization_prime_pow hp,
    factorization_prime_pow hp]
  by_cases h2 : p = 2
  · subst h2
    have : ({2} : Finset ℕ) \ {2, 3} = ∅ := by decide
    simp [f₃_zero, this]
  by_cases h3 : p = 3
  · subst h3
    have : ({3} : Finset ℕ) \ {2, 3} = ∅ := by decide
    simp [f₂_zero, this]
  · have : ({p} : Finset ℕ) \ {2, 3} = {p} := by
      ext q; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, by tauto⟩
    simp [h2, h3, this, f₂_zero, f₃_zero]

theorem card_local_of {p a : ℕ} {RL : List (FreeGroup LGen)} (h : localRelList p a = RL)
    (C : CosetCert) (hC : C.check RL = true) : Nat.card (PresentedGroup (localRels p a)) = C.n :=
  CosetCert.card_eq_of_check (C := C) (R := localRels p a) (RL := RL)
    (fun r => by simp only [localRels, Set.mem_ofPred_eq, h]) hC

theorem card_localPres (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    Nat.card (PresentedGroup (localRels p a)) = Nat.card (B (p ^ a)) := by
  rw [card_B_prime_pow hp ha]
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl]
    rcases Nat.lt_or_ge a 9 with h9 | h9
    · interval_cases a
      · exact card_local_of (RL := [w ^ 2, s ^ 1] ++ localExtraRels 2 1)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L1 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 2] ++ localExtraRels 2 2)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L22 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 2] ++ localExtraRels 2 3)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L23 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 4] ++ localExtraRels 2 4)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L24 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 4] ++ localExtraRels 2 5)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L25 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 8] ++ localExtraRels 2 6)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L26 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 8] ++ localExtraRels 2 7)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L27 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 8] ++ localExtraRels 2 8)
          (by rw [localRelList, hPart_two_pow]; rfl) cosetCert_L28 (by decide +kernel)
    · rw [f₂_ge (by omega)]
      exact card_local_of (RL := [w ^ 2, s ^ 8] ++ [bracket r s])
        (by rw [localRelList, hPart_two_pow, show min 3 (a / 2) = 3 by omega,
          localExtraRels_two_ge a h9]; rfl) cosetCert_L29 (by decide +kernel)
  by_cases h3 : p = 3
  · subst h3
    rw [if_neg (by norm_num), if_pos rfl]
    rcases Nat.lt_or_ge a 3 with h9 | h9
    · interval_cases a
      · exact card_local_of (RL := [w ^ 2, s ^ 1] ++ localExtraRels 3 1)
          (by rw [localRelList, hPart_three_pow]; rfl) cosetCert_L1 (by decide +kernel)
      · exact card_local_of (RL := [w ^ 2, s ^ 3] ++ localExtraRels 3 2)
          (by rw [localRelList, hPart_three_pow]; rfl) cosetCert_L32 (by decide +kernel)
    · rw [f₃_ge h9]
      exact card_local_of (RL := [w ^ 2, s ^ 3] ++ [bracket r s])
        (by rw [localRelList, hPart_three_pow, show min 1 (a / 2) = 1 by omega,
          localExtraRels_three_ge a h9]; rfl) cosetCert_L33 (by decide +kernel)
  · rw [if_neg h2, if_neg h3]
    exact card_local_of (RL := [w ^ 2, s ^ 1] ++ [])
      (by rw [localRelList, hPart_prime_pow hp h2 h3, localExtraRels_ge_five p a h2 h3])
      cosetCert_L1 (by decide +kernel)

/-! ### T5 -/

/-- The local presentation map is bijective. -/
theorem presHom_local_bijective (p a : ℕ) (hp : p.Prime) (ha : 0 < a) [NeZero (p ^ a)] :
    Function.Bijective (presHom (p ^ a) (localRels_fricke p a hp ha (NeZero.ne _))) := by
  have := finite_B' (p ^ a)
  have hcard := card_localPres p a hp ha
  have : Finite (PresentedGroup (localRels p a)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  exact (presHom_surjective _ hp ha rfl).bijective_of_nat_card_le hcard.le

/-- **T5.** -/
theorem localPresentation' (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    ∃ φ : PresentedGroup (localRels p a) ≃* B (p ^ a),
      (φ (.of .w)).IsALClass (p ^ a) ∧ (φ (.of .s)).IsClassOf (S (hPart (p ^ a))) := by
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hR := localRels_fricke p a hp ha (NeZero.ne _)
  exact ⟨MulEquiv.ofBijective _ (presHom_local_bijective p a hp ha), presHom_w_isALClass hR,
    presHom_s_isClassOf hR⟩

end

end NormalizerLean
