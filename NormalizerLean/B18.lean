module

public import NormalizerLean.Global

@[expose] public section

/-!
# T7, examples: B(18) ≅ S₄, and B(18) ≇ C₂ × A₄

18 = 2 · 3², m₂ = 2, m₃ = 9, h(2) = 1, h(9) = 3. The global presentation (T6) has generators
w₂, s₂, w₃, s₃; ψ : w₂ ↦ (0 1), s₂ ↦ 1, w₃ ↦ (0 1)(2 3), s₃ ↦ (0 1)(1 2) satisfies its relators
(checked by `decide`), is onto (the closure of the images is computed by `decide`), and
|G| = |B(18)| = 24 = |S₄|. S₄ has trivial centre (`decide`), C₂ × A₄ does not.
-/

open Equiv

namespace NormalizerLean

noncomputable section

open Words

/-! ### Closure in a finite group by `decide` -/

/-- One step: S ∪ S·gens. -/
def growStep {G : Type*} [Mul G] [DecidableEq G] (gens : List G) (S : Finset G) : Finset G :=
  S ∪ S.biUnion (fun x => (gens.map (x * ·)).toFinset)

/-- The products of at most k generators. -/
def growIter {G : Type*} [Monoid G] [DecidableEq G] (gens : List G) : ℕ → Finset G
  | 0 => {1}
  | k + 1 => growStep gens (growIter gens k)

theorem mem_of_growIter {G : Type*} [Group G] [DecidableEq G] (H : Subgroup G) {gens : List G}
    (hg : ∀ g ∈ gens, g ∈ H) : ∀ k, ∀ x ∈ growIter gens k, x ∈ H
  | 0, x, hx => by
    simp only [growIter, Finset.mem_singleton] at hx
    rw [hx]
    exact one_mem _
  | k + 1, x, hx => by
    simp only [growIter, growStep, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_map] at hx
    rcases hx with hx | ⟨y, hy, g, hg', rfl⟩
    · exact mem_of_growIter H hg k x hx
    · exact mul_mem (mem_of_growIter H hg k y hy) (hg g hg')

theorem lift_map_eq' {α β G : Type*} [Group G] (F : β → G) (ι : α → β) (ρ : FreeGroup α) :
    FreeGroup.lift F (FreeGroup.map ι ρ) = FreeGroup.lift (F ∘ ι) ρ := by
  have : (FreeGroup.lift F).comp (FreeGroup.map ι) = FreeGroup.lift (F ∘ ι) :=
    FreeGroup.ext_hom _ _ (fun a => by simp)
  exact DFunLike.congr_fun this ρ

/-! ### Arithmetic of 18 -/

theorem primeFactors_18 : Nat.primeFactors 18 = {2, 3} := by
  rw [show (18 : ℕ) = 2 * 3 ^ 2 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors Nat.prime_two, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  decide

theorem factorization_18 (p : ℕ) :
    Nat.factorization 18 p = (if p = 2 then 1 else 0) + (if p = 3 then 2 else 0) := by
  rw [show (18 : ℕ) = 2 ^ 1 * 3 ^ 2 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, factorization_prime_pow Nat.prime_two, factorization_prime_pow Nat.prime_three]
  simp only [eq_comm]

theorem factorization_18_two : Nat.factorization 18 2 = 1 := by rw [factorization_18]; rfl
theorem factorization_18_three : Nat.factorization 18 3 = 2 := by rw [factorization_18]; rfl

theorem card_B18 : Nat.card (B 18) = 24 := by
  rw [card_B_explicit', factorization_18_two, factorization_18_three, primeFactors_18]
  decide

/-! ### The map to S₄ -/

def pa : Perm (Fin 4) := swap 0 1
def pb : Perm (Fin 4) := swap 0 1 * swap 2 3
def pc : Perm (Fin 4) := swap 0 1 * swap 1 2

/-- w₂ ↦ (0 1), s₂ ↦ 1, w₃ ↦ (0 1)(2 3), s₃ ↦ (0 1)(1 2). -/
def f18 : GGen 18 → Perm (Fin 4) := fun x =>
  if (x.1 : ℕ) = 2 then (match x.2 with | .w => pa | .s => 1)
  else (match x.2 with | .w => pb | .s => pc)

theorem mem_pf18 (p : (18 : ℕ).primeFactors) : (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by
  have h : ∀ n : ℕ, n ∈ Nat.primeFactors 18 → n = 2 ∨ n = 3 := by
    intro n hn
    rw [primeFactors_18] at hn
    simpa using hn
  exact h p p.2

theorem mPart_18_two : mPart 18 2 = 2 := by simp [mPart, factorization_18_two]
theorem mPart_18_three : mPart 18 3 = 9 := by simp [mPart, factorization_18_three]

theorem f18_w2 {p : (18 : ℕ).primeFactors} (hp : (p : ℕ) = 2) : f18 (p, .w) = pa := by
  simp [f18, hp]
theorem f18_s2 {p : (18 : ℕ).primeFactors} (hp : (p : ℕ) = 2) : f18 (p, .s) = 1 := by
  simp [f18, hp]
theorem f18_w3 {p : (18 : ℕ).primeFactors} (hp : (p : ℕ) = 3) : f18 (p, .w) = pb := by
  simp [f18, hp]
theorem f18_s3 {p : (18 : ℕ).primeFactors} (hp : (p : ℕ) = 3) : f18 (p, .s) = pc := by
  simp [f18, hp]

theorem f18_rels : ∀ ρ ∈ globalRels 18, FreeGroup.lift f18 ρ = 1 := by
  intro ρ hρ
  simp only [globalRels, Set.mem_union, Set.mem_iUnion, Set.mem_image] at hρ
  rcases hρ with ⟨p, ρ', hρ', rfl⟩ | ⟨p, q, hpq, hρ⟩
  · rw [lift_map_eq']
    rcases mem_pf18 p with hp | hp
    · rw [hp, factorization_18_two] at hρ'
      have e : localRelList 2 1 = [w ^ 2, s ^ 1] := by rw [localRelList, hPart_two_pow]; rfl
      simp only [localRels, Set.mem_ofPred_eq, e, List.mem_cons, List.not_mem_nil,
        or_false] at hρ'
      rcases hρ' with rfl | rfl <;>
        simp only [map_pow, FreeGroup.lift_apply_of, Function.comp_apply, f18_w2 hp,
          f18_s2 hp] <;> decide
    · rw [hp, factorization_18_three] at hρ'
      have e : localRelList 3 2 = [w ^ 2, s ^ 3, (w * s) ^ 3] := by
        rw [localRelList, hPart_three_pow]; rfl
      simp only [localRels, Set.mem_ofPred_eq, e, List.mem_cons, List.not_mem_nil,
        or_false] at hρ'
      rcases hρ' with rfl | rfl | rfl <;>
        simp only [map_pow, map_mul, FreeGroup.lift_apply_of, Function.comp_apply, f18_w3 hp,
          f18_s3 hp] <;> decide
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
    rcases mem_pf18 p with hp | hp <;> rcases mem_pf18 q with hq | hq
    · exact absurd (Subtype.ext (hp.trans hq.symm)) hpq
    · rcases hρ with rfl | rfl | rfl <;>
        simp only [bracket, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, f18_w2 hp,
          f18_s2 hp, f18_w3 hq, f18_s3 hq, hp, mPart_18_two] <;> decide
    · rcases hρ with rfl | rfl | rfl <;>
        simp only [bracket, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, f18_w3 hp,
          f18_s3 hp, f18_w2 hq, f18_s2 hq, hp, mPart_18_three] <;> decide
    · exact absurd (Subtype.ext (hp.trans hq.symm)) hpq

/-- ψ : G(18) → S₄. -/
def psi18 : GP 18 →* Perm (Fin 4) := PresentedGroup.toGroup f18_rels

-- The elaborator recurses deeply on statements mentioning `growIter … 6`, hence `maxRecDepth`.
set_option maxRecDepth 100000 in
theorem growIter_all : ∀ σ : Perm (Fin 4), σ ∈ growIter [pa, pb, pc] 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem psi18_surjective : Function.Surjective psi18 := by
  have h2 : (2 : ℕ) ∈ (18 : ℕ).primeFactors := by rw [primeFactors_18]; simp
  have h3 : (3 : ℕ) ∈ (18 : ℕ).primeFactors := by rw [primeFactors_18]; simp
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro σ _
  refine mem_of_growIter psi18.range (fun g hg => ?_) 6 σ (growIter_all σ)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨gen 18 ⟨2, h2⟩ .w, (PresentedGroup.toGroup.of _).trans (f18_w2 rfl)⟩
  · exact ⟨gen 18 ⟨3, h3⟩ .w, (PresentedGroup.toGroup.of _).trans (f18_w3 rfl)⟩
  · exact ⟨gen 18 ⟨3, h3⟩ .s, (PresentedGroup.toGroup.of _).trans (f18_s3 rfl)⟩

theorem psi18_bijective : Function.Bijective psi18 := by
  have := (card_GP_le 18).1
  refine psi18_surjective.bijective_of_nat_card_le ?_
  rw [Nat.card_eq_of_bijective _ (PhiG_bijective 18), card_B18, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

/-- **T7**, example: B(18) ≅ S₄. -/
theorem B18_equiv_perm' : Nonempty (B 18 ≃* Equiv.Perm (Fin 4)) :=
  ⟨(MulEquiv.ofBijective _ (PhiG_bijective 18)).symm.trans
    (MulEquiv.ofBijective _ psi18_bijective)⟩

theorem perm4_center : ∀ σ : Perm (Fin 4), σ ≠ 1 → ∃ τ : Perm (Fin 4), σ * τ ≠ τ * σ := by
  decide +kernel

/-- **T7**, example: B(18) is not C₂ × A₄ (S₄ has trivial centre, C₂ × A₄ does not). -/
theorem B18_not_C2_prod_A4' :
    IsEmpty (B 18 ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 4)) := by
  obtain ⟨e₀⟩ := B18_equiv_perm'
  refine ⟨fun e => ?_⟩
  let e' := e₀.symm.trans e
  let z : Multiplicative (ZMod 2) × alternatingGroup (Fin 4) := (Multiplicative.ofAdd 1, 1)
  have hz : ∀ y, z * y = y * z := fun y => Prod.ext (mul_comm _ _) (by simp [z])
  have hz1 : z ≠ 1 := by
    intro h
    have := congrArg Prod.fst h
    exact absurd this (by decide)
  have hσ1 : e'.symm z ≠ 1 := fun h => hz1 (by simpa using congrArg e' h)
  obtain ⟨τ, hτ⟩ := perm4_center _ hσ1
  apply hτ
  apply e'.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]

end

end NormalizerLean
