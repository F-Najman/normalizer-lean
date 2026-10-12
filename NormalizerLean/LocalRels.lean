import NormalizerLean.RelBasic

/-!
# The local relations hold: `localRels_mem_Gamma0`

Computed with w ↦ the Fricke element and s ↦ S_h, then transferred to an arbitrary Atkin–Lehner
element by `lift_mem_iff_of_cosets`.  The integer matrices below were computed exactly in sympy
(`(14)` is proved symbolically in `RelBasic.lean`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem fricke_sq_mem (m : ℕ) (hm : m ≠ 0) : fricke m hm ^ 2 ∈ Gamma0R m := by
  refine mem_Gamma0R_of_entries (-1) 0 0 (-1) ?_ (dvd_zero _)
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_fricke]
  apply smul_mul_smul_eq (Real.mul_self_sqrt (Nat.cast_nonneg m)) (Nat.cast_ne_zero.2 hm)
  rw [mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem S_pow_self_mem (N h : ℕ) (hh : h ≠ 0) : S h ^ h ∈ Gamma0R N := by
  refine mem_Gamma0R_of_entries 1 1 0 1 ?_ (dvd_zero _)
  rw [coe_S_pow]
  have : (h : ℝ) * (h : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.2 hh)
  simp [this]

/-- Tactic for the numerical cases: evaluate the word as a product of explicit rational matrices. -/
macro "rel_compute" a:term:max b:term:max c:term:max d:term:max hs:term:max : tactic =>
  `(tactic| (
    simp only [bracket, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, locF]
    refine mem_Gamma0R_of_entries $a $b $c $d ?_ (by norm_num)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_pow, coe_S]
    rw [$hs:term]
    norm_num [adjugate_fin_two_of, mul_fin_two, pow_succ]))

theorem extra_4 (hm : (2 : ℕ) ^ 2 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 2, FreeGroup.lift (locF (fricke (2 ^ 2) hm) 2) ρ ∈ Gamma0R (2 ^ 2) := by
  intro ρ hρ
  have hW := coe_fricke_of_sq (2 ^ 2) 2 hm rfl
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl
  rel_compute (-1) 0 0 (-1) hW

theorem extra_9 (hm : (3 : ℕ) ^ 2 ≠ 0) :
    ∀ ρ ∈ localExtraRels 3 2, FreeGroup.lift (locF (fricke (3 ^ 2) hm) 3) ρ ∈ Gamma0R (3 ^ 2) := by
  intro ρ hρ
  have hW := coe_fricke_of_sq (3 ^ 2) 3 hm rfl
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl
  rel_compute (-1) 0 0 (-1) hW

theorem extra_16 (hm : (2 : ℕ) ^ 4 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 4, FreeGroup.lift (locF (fricke (2 ^ 4) hm) 4) ρ ∈ Gamma0R (2 ^ 4) := by
  intro ρ hρ
  have hW := coe_fricke_of_sq (2 ^ 4) 4 hm (by norm_num)
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl
  rel_compute (-1) 0 0 (-1) hW

theorem extra_32 (hm : (2 : ℕ) ^ 5 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 5, FreeGroup.lift (locF (fricke (2 ^ 5) hm) 4) ρ ∈ Gamma0R (2 ^ 5) := by
  intro ρ hρ
  have hR := coe_lift_rr (2 ^ 5) 4 hm (by norm_num)
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl <;> rw [← rr_def]
  · rel_compute (-3) (-1) 64 21 hR
  · rel_compute 21 2 (-32) (-3) hR
  · rel_compute (-1) 0 32 (-1) hR

theorem extra_64 (hm : (2 : ℕ) ^ 6 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 6, FreeGroup.lift (locF (fricke (2 ^ 6) hm) 8) ρ ∈ Gamma0R (2 ^ 6) := by
  intro ρ hρ
  have hW := coe_fricke_of_sq (2 ^ 6) 8 hm (by norm_num)
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl
  · rel_compute (-1) 0 0 (-1) hW
  · rel_compute 241 (-8) (-512) 17 hW
  · rel_compute 13 (-6) 128 (-59) hW

theorem extra_128 (hm : (2 : ℕ) ^ 7 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 7, FreeGroup.lift (locF (fricke (2 ^ 7) hm) 8) ρ ∈ Gamma0R (2 ^ 7) := by
  intro ρ hρ
  have hR := coe_lift_rr (2 ^ 7) 8 hm (by norm_num)
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl <;> rw [← rr_def]
  · rel_compute (-7) (-2) 256 73 hR
  · rel_compute 69 (-1) (-896) 13 hR
  · rel_compute (-35) 1 384 (-11) hR
  · rel_compute (-1) 0 128 (-1) hR

theorem extra_256 (hm : (2 : ℕ) ^ 8 ≠ 0) :
    ∀ ρ ∈ localExtraRels 2 8, FreeGroup.lift (locF (fricke (2 ^ 8) hm) 8) ρ ∈ Gamma0R (2 ^ 8) := by
  intro ρ hρ
  have hW := coe_fricke_of_sq (2 ^ 8) 16 hm (by norm_num)
  simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl
  · rel_compute (-7) (-1) 512 73 hW
  · rel_compute 389 (-3) (-9984) 77 hW

theorem localExtraRels_two_ge (a : ℕ) (h : 9 ≤ a) :
    localExtraRels 2 a = [bracket Words.r Words.s] := by
  unfold localExtraRels
  split <;> first | omega | simp_all

theorem localExtraRels_three_ge (b : ℕ) (h : 3 ≤ b) :
    localExtraRels 3 b = [bracket Words.r Words.s] := by
  unfold localExtraRels
  split <;> first | omega | simp_all

theorem localExtraRels_ge_five (p a : ℕ) (h2 : p ≠ 2) (h3 : p ≠ 3) : localExtraRels p a = [] := by
  unfold localExtraRels
  split <;> simp_all

/-- The local relators hold for w ↦ Fricke. -/
theorem localRels_fricke (p a : ℕ) (hp : p.Prime) (ha : 0 < a) (hm : p ^ a ≠ 0) :
    ∀ ρ ∈ localRels p a,
      FreeGroup.lift (locF (fricke (p ^ a) hm) (hPart (p ^ a))) ρ ∈ Gamma0R (p ^ a) := by
  intro ρ hρ
  simp only [localRels, localRelList, Set.mem_ofPred_eq, List.cons_append, List.nil_append,
    List.mem_cons]
    at hρ
  rcases hρ with rfl | rfl | hρ
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact fricke_sq_mem _ hm
  · rw [map_pow, FreeGroup.lift_apply_of]
    exact S_pow_self_mem _ _ (hPart_pos _).ne'
  by_cases h2 : p = 2
  · subst h2
    rcases Nat.lt_or_ge a 9 with h9 | h9
    · interval_cases a
      · simp [localExtraRels] at hρ
      · rw [show hPart (2 ^ 2) = 2 by rw [hPart_two_pow]; norm_num]
        exact extra_4 hm ρ hρ
      · simp only [localExtraRels, List.mem_cons, List.not_mem_nil, or_false] at hρ
        subst hρ
        rw [← rr_def, show hPart (2 ^ 3) = 2 by rw [hPart_two_pow]; norm_num]
        exact bracket_rr_mem (2 ^ 3) 2 1 hm (by norm_num) (by norm_num)
      · rw [show hPart (2 ^ 4) = 4 by rw [hPart_two_pow]; norm_num]
        exact extra_16 hm ρ hρ
      · rw [show hPart (2 ^ 5) = 4 by rw [hPart_two_pow]; norm_num]
        exact extra_32 hm ρ hρ
      · rw [show hPart (2 ^ 6) = 8 by rw [hPart_two_pow]; norm_num]
        exact extra_64 hm ρ hρ
      · rw [show hPart (2 ^ 7) = 8 by rw [hPart_two_pow]; norm_num]
        exact extra_128 hm ρ hρ
      · rw [show hPart (2 ^ 8) = 8 by rw [hPart_two_pow]; norm_num]
        exact extra_256 hm ρ hρ
    · rw [localExtraRels_two_ge a h9, List.mem_singleton] at hρ
      subst hρ
      have h8 : hPart (2 ^ a) = 8 := by
        rw [hPart_two_pow, show min 3 (a / 2) = 3 by omega]
        norm_num
      rw [← rr_def, h8]
      refine bracket_rr_mem (2 ^ a) 8 (2 ^ (a - 9)) hm (by norm_num) ?_
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
  by_cases h3 : p = 3
  · subst h3
    rcases Nat.lt_or_ge a 3 with h9 | h9
    · interval_cases a
      · simp [localExtraRels] at hρ
      · rw [show hPart (3 ^ 2) = 3 by rw [hPart_three_pow]; norm_num]
        exact extra_9 hm ρ hρ
    · rw [localExtraRels_three_ge a h9, List.mem_singleton] at hρ
      subst hρ
      have h8 : hPart (3 ^ a) = 3 := by
        rw [hPart_three_pow, show min 1 (a / 2) = 1 by omega]
        norm_num
      rw [← rr_def, h8]
      refine bracket_rr_mem (3 ^ a) 3 (3 ^ (a - 3)) hm (by norm_num) ?_
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
  · rw [localExtraRels_ge_five p a h2 h3] at hρ
    simp at hρ

theorem locF_eq (wg : SL(2, ℝ)) (k : ℕ) :
    (fun x : LGen => match x with | .w => wg | .s => S k) = locF wg k := by
  funext x
  cases x <;> rfl

/-- **Stage-1 milestone**: the local relators hold for any Atkin–Lehner element. -/
theorem localRels_mem_Gamma0' (p a : ℕ) (hp : p.Prime) (ha : 0 < a) {wg : SL(2, ℝ)}
    (hw : IsAtkinLehner (p ^ a) (p ^ a) wg) :
    ∀ ρ ∈ localRels p a,
      FreeGroup.lift (fun x : LGen => match x with | .w => wg | .s => S (hPart (p ^ a))) ρ ∈
        Gamma0R (p ^ a) := by
  intro ρ hρ
  have hm : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ a) := ⟨hm⟩
  rw [locF_eq]
  have hfr := fricke_isAtkinLehner (p ^ a) hm
  have hfrN := isAtkinLehner_mem_normalizer' dvd_rfl hfr
  have hwN := isAtkinLehner_mem_normalizer' dvd_rfl hw
  have hSN := S_mem_normalizer' (N := p ^ a) (dvd_refl (hPart (p ^ a)))
  refine (lift_mem_iff_of_cosets (locF (fricke (p ^ a) hm) (hPart (p ^ a)))
    (locF wg (hPart (p ^ a))) ?_ ?_ ?_ ρ).1 (localRels_fricke p a hp ha hm ρ hρ)
  · intro x; cases x <;> assumption
  · intro x; cases x <;> assumption
  · intro x
    cases x
    · exact (mul_inv_mem_iff_inv_mul_mem hfrN).1 (isAtkinLehner_mul_inv_mem' dvd_rfl hfr hw)
    · simp only [locF, inv_mul_cancel]
      exact one_mem _

end

end NormalizerLean
