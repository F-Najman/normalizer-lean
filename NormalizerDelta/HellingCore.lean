module

public import NormalizerDelta.HellingGlue
public import NormalizerDelta.MDelta
public import NormalizerDelta.GenBasic

@[expose] public section

/-!
# Part 9: the core theorem

`IsRep g R`: the real matrix g is a nonzero real multiple of the integral matrix R.  The core theorem `core`: let
G ≤ SL₂(ℝ) be a group all of whose elements have integral representatives, and suppose that for every prime p
there is a nonempty set S_p of vertices of the p-adic tree, bounded, mapped into itself by the representatives of
the elements of G, and equal to the vertex 1 for all but finitely many p.  Then G is conjugate into Γ₀(N)⁺ for a
squarefree N, by projSL(A) with A integral, det A > 0.

Proof: at every prime, G fixes the centre of S_p, a vertex or an edge (`center_conclusion`).  The vertices are glued
into one integral matrix Z (`exists_glue`), and the far ends of the edges into a Z′; the Smith form of adj(Z)·Z′
is diag(e, eN) up to SL₂(ℤ), with N squarefree; conjugation by Z* = Z·U moves the configuration to
{1, diag(1, N)}, whose stabilizer consists of Atkin–Lehner elements (`al_shape`, `isAtkinLehner_of_local`).
-/

open Matrix MatrixGroups

namespace NormalizerLean.Helling

/-- g is a (nonzero) real multiple of the integral matrix R. -/
def IsRep (g : SL(2, ℝ)) (R : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  R.det ≠ 0 ∧ ∃ c : ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Int.cast : ℤ → ℝ)

theorem map_intCast_mul (R Q : Matrix (Fin 2) (Fin 2) ℤ) :
    (R * Q).map (Int.cast : ℤ → ℝ) = R.map Int.cast * Q.map Int.cast :=
  Matrix.map_mul (f := Int.castRingHom ℝ)

theorem map_intCast_adjugate (R : Matrix (Fin 2) (Fin 2) ℤ) :
    R.adjugate.map (Int.cast : ℤ → ℝ) = (R.map Int.cast).adjugate :=
  RingHom.map_adjugate (Int.castRingHom ℝ) R

theorem map_intCast_smul (n : ℤ) (R : Matrix (Fin 2) (Fin 2) ℤ) :
    (n • R).map (Int.cast : ℤ → ℝ) = (n : ℝ) • R.map Int.cast := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem IsRep.mul {g h : SL(2, ℝ)} {R Q : Matrix (Fin 2) (Fin 2) ℤ} (hg : IsRep g R) (hh : IsRep h Q) :
    IsRep (g * h) (R * Q) := by
  obtain ⟨hR, c, hc⟩ := hg
  obtain ⟨hQ, d, hd⟩ := hh
  refine ⟨det_mul_ne_zero hR hQ, c * d, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, hc, hd, map_intCast_mul, smul_mul_smul_comm]

theorem IsRep.inv {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ} (hg : IsRep g R) :
    IsRep g⁻¹ R.adjugate := by
  obtain ⟨hR, c, hc⟩ := hg
  refine ⟨det_adjugate_ne_zero hR, c, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_inv, hc, adjugate_smul, map_intCast_adjugate]
  simp

theorem IsRep.smul {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ} (hg : IsRep g R) {n : ℤ} (hn : n ≠ 0) :
    IsRep g (n • R) := by
  obtain ⟨hR, c, hc⟩ := hg
  refine ⟨det_smul_ne_zero hn hR, c / n, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [hc, map_intCast_smul, smul_smul, div_mul_cancel₀ _ hn']

theorem IsRep.of_smul {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hn : n ≠ 0)
    (hg : IsRep g (n • R)) : IsRep g R := by
  obtain ⟨hR, c, hc⟩ := hg
  refine ⟨fun h => hR (by rw [det_smul, h, mul_zero]), c * n, ?_⟩
  rw [hc, map_intCast_smul, smul_smul]

theorem IsRep.sq_mul_det {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ} (hg : IsRep g R) :
    ∃ c : ℝ, c ^ 2 * (R.det : ℝ) = 1 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map (Int.cast : ℤ → ℝ) := by
  obtain ⟨-, c, hc⟩ := hg
  refine ⟨c, ?_, hc⟩
  have := congrArg Matrix.det hc
  rw [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, det_map_intCast] at this
  exact this.symm

theorem IsRep.det_pos {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ} (hg : IsRep g R) : 0 < R.det := by
  obtain ⟨c, hc, -⟩ := hg.sq_mul_det
  have h1 : (0 : ℝ) < R.det := by
    by_contra h
    push Not at h
    have : c ^ 2 * (R.det : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) h
    linarith
  exact_mod_cast h1

theorem isRep_projSL {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) :
    IsRep (projSL (A.map (Int.cast : ℤ → ℝ))) A :=
  ⟨hA.ne', _, coe_projSL_int hA⟩

theorem isRep_ofZ (γ : SL(2, ℤ)) : IsRep (ofZ γ) (γ : Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨by rw [γ.2]; exact one_ne_zero, 1, by rw [one_smul, coe_ofZ_eq_map]⟩

/-- Two representatives of g are proportional. -/
theorem IsRep.prop {g : SL(2, ℝ)} {R Q : Matrix (Fin 2) (Fin 2) ℤ} (hR : IsRep g R) (hQ : IsRep g Q) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • R = b • Q := by
  obtain ⟨hR0, c, hc⟩ := hR
  obtain ⟨hQ0, d, hd⟩ := hQ
  obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hR0
    rw [det_fin_two, h 0 0, h 0 1]
    ring
  have e : ∀ k l, c * (R k l : ℝ) = d * (Q k l : ℝ) := fun k l => by
    have := congrFun (congrFun (hc.symm.trans hd) k) l
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := hd
    rw [zero_smul] at hc
    have h1 := congrArg Matrix.det hc
    simp at h1
  have hQij : Q i j ≠ 0 := by
    intro h0
    have := e i j
    rw [h0, Int.cast_zero, mul_zero] at this
    exact hij (by exact_mod_cast (mul_eq_zero.1 this).resolve_left hc0)
  refine ⟨Q i j, R i j, hQij, hij, ?_⟩
  ext k l
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h1 := e k l
  have h2 := e i j
  have : ((Q i j * R k l : ℤ) : ℝ) = ((R i j * Q k l : ℤ) : ℝ) := by
    push_cast
    apply mul_left_cancel₀ hc0
    linear_combination (Q i j : ℝ) * h1 - (Q k l : ℝ) * h2
  exact_mod_cast this

/-! ### Conjugation -/

theorem dd_conj {p : ℕ} [Fact p.Prime] {Z R X Y : Matrix (Fin 2) (Fin 2) ℤ} (hZ : Z.det ≠ 0) (hR : R.det ≠ 0)
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    dd p X (Z.adjugate * R * Z * Y) = dd p (Z * X) (R * (Z * Y)) := by
  have e : Z * (Z.adjugate * R * Z * Y) = Z.det • (R * (Z * Y)) := by
    simp only [← Matrix.mul_assoc, mul_adjugate, smul_mul, Matrix.one_mul]
  have h1 : (Z.adjugate * R * Z * Y).det ≠ 0 :=
    det_mul_ne_zero (det_mul_ne_zero (det_mul_ne_zero (det_adjugate_ne_zero hZ) hR) hZ) hY
  rw [← dd_mul_left hZ hX h1, e, dd_smul_right hZ (det_mul_ne_zero hZ hX)
    (det_mul_ne_zero hR (det_mul_ne_zero hZ hY))]

theorem dd_smul_mul {p : ℕ} [Fact p.Prime] {z R w : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hn : n ≠ 0)
    (hz : z.det ≠ 0) (hR : R.det ≠ 0) (hw : w.det ≠ 0) : dd p z ((n • R) * w) = dd p z (R * w) := by
  rw [smul_mul, dd_smul_right hn hz (det_mul_ne_zero hR hw)]

theorem presE_smul {p : ℕ} [Fact p.Prime] {z z' R : Matrix (Fin 2) (Fin 2) ℤ} {n : ℤ} (hn : n ≠ 0)
    (hz : z.det ≠ 0) (hz' : z'.det ≠ 0) (hR : R.det ≠ 0) : PresE p z z' (n • R) ↔ PresE p z z' R := by
  unfold PresE
  rw [dd_smul_mul hn hz hR hz, dd_smul_mul hn hz' hR hz', dd_smul_mul hn hz' hR hz, dd_smul_mul hn hz hR hz']

/-! ### The stabilizer of {1, diag(1, N)} -/

theorem exists_primitive {R : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.det ≠ 0) :
    ∃ Y : Matrix (Fin 2) (Fin 2) ℤ, cont Y = 1 ∧ R = ((cont R : ℕ) : ℤ) • Y := by
  have hc := cont_ne_zero hR
  have hdvd : ∀ i j, ((cont R : ℕ) : ℤ) ∣ R i j := dvd_cont_iff.1 dvd_rfl
  refine ⟨Matrix.of fun i j => R i j / (cont R : ℤ), ?_, ?_⟩
  · have e : R = ((cont R : ℕ) : ℤ) • Matrix.of fun i j => R i j / (cont R : ℤ) := by
      ext i j
      simp [Int.mul_ediv_cancel' (hdvd i j)]
    have := cont_smul ((cont R : ℕ) : ℤ) (Matrix.of fun i j => R i j / (cont R : ℤ))
    rw [← e, Int.natAbs_natCast] at this
    have h2 : cont R * 1 = cont R * cont (Matrix.of fun i j => R i j / (cont R : ℤ)) := by
      rw [mul_one]; exact this
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc) h2).symm
  · ext i j
    simp [Int.mul_ediv_cancel' (hdvd i j)]

/-- An element of SL₂(ℝ) with a representative that fixes the vertex 1 at every p ∤ N and preserves the edge
{1, diag(1, N)} at every p ∣ N is an Atkin–Lehner element of level N. -/
theorem isAtkinLehner_of_local {N : ℕ} (hN : Squarefree N) {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ}
    (hR : IsRep g R) (hfix : ∀ p, (hp : p.Prime) → ¬ p ∣ N → @dd p 1 (R * 1) = 0)
    (hedge : ∀ p, p.Prime → p ∣ N → PresE p 1 (diagN N) R) :
    ∃ e : ℕ, e ∣ N ∧ IsAtkinLehner N e g := by
  have hR0 := hR.1
  obtain ⟨Y, hY1, hRY⟩ := exists_primitive hR0
  have hc0 : ((cont R : ℕ) : ℤ) ≠ 0 := by exact_mod_cast cont_ne_zero hR0
  have hYrep : IsRep g Y := IsRep.of_smul hc0 (hRY ▸ hR)
  have hY0 := hYrep.1
  have hD0 : (diagN N).det ≠ 0 := by rw [det_diagN]; exact_mod_cast hN.ne_zero
  obtain ⟨e, heN, x, y, z, w, he, hYe⟩ := al_shape hN hYrep.det_pos hY1
    (fun p hp hpN => by
      have : Fact p.Prime := ⟨hp⟩
      have := hfix p hp hpN
      rw [Matrix.mul_one, dd_one_left, hRY, dist_smul hc0 hY0] at this
      exact this)
    (fun p hp hpN => by
      have : Fact p.Prime := ⟨hp⟩
      have := hedge p hp hpN
      rwa [hRY, presE_smul hc0 (by simp) hD0 hY0] at this)
  refine ⟨e, heN, ?_⟩
  obtain ⟨c, hc, hg⟩ := hYrep.sq_mul_det
  have hdetY : Y.det = e := by
    rw [hYe, det_fin_two_of]; linear_combination he
  rw [hdetY] at hc
  have he0 : (0 : ℝ) < e := by
    have := hYrep.det_pos
    rw [hdetY] at this
    exact_mod_cast this
  have hs : ((Real.sqrt e)⁻¹) ^ 2 = 1 / (e : ℝ) := by
    rw [inv_pow, Real.sq_sqrt he0.le, one_div]
  have hc2 : c ^ 2 * (e : ℝ) = 1 := by exact_mod_cast hc
  have hc' : c ^ 2 = ((Real.sqrt e)⁻¹) ^ 2 := by
    rw [hs, eq_div_iff he0.ne']; exact hc2
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hc' with h | h
  · refine ⟨x, y, z, w, he, ?_⟩
    rw [hg, h, hYe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · refine ⟨-x, -y, -z, -w, by linear_combination he, ?_⟩
    rw [hg, h, hYe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem mem_gamma0Plus_of_local {N : ℕ} (hN : Squarefree N) {g : SL(2, ℝ)} {R : Matrix (Fin 2) (Fin 2) ℤ}
    (hR : IsRep g R) (hfix : ∀ p, (hp : p.Prime) → ¬ p ∣ N → @dd p 1 (R * 1) = 0)
    (hedge : ∀ p, p.Prime → p ∣ N → PresE p 1 (diagN N) R) : g ∈ Gamma0Plus N := by
  obtain ⟨e, heN, he⟩ := isAtkinLehner_of_local hN hR hfix hedge
  exact Subgroup.subset_closure ⟨e, heN, he⟩

/-! ### The core theorem -/

theorem dd_mul_unit_left {p : ℕ} [Fact p.Prime] {Y U W : Matrix (Fin 2) (Fin 2) ℤ}
    (hU : ¬ (p : ℤ) ∣ U.det) (hY : Y.det ≠ 0) (hW : W.det ≠ 0) : dd p (Y * U) W = dd p Y W := by
  rw [dd, adjugate_mul_distrib, Matrix.mul_assoc,
    dist_unit_mul (by rwa [det_adjugate']) (det_mul_ne_zero (det_adjugate_ne_zero hY) hW), dd]

/-- **The core theorem.** -/
theorem core {G : Subgroup SL(2, ℝ)} (hrep : ∀ g ∈ G, ∃ R, IsRep g R)
    (S : ℕ → Set (Matrix (Fin 2) (Fin 2) ℤ)) (hSdet : ∀ p, ∀ s ∈ S p, s.det ≠ 0)
    (hSne : ∀ p, p.Prime → (S p).Nonempty)
    (hSbdd : ∀ p, (hp : p.Prime) → ∃ B, ∀ s ∈ S p, @dist p s ≤ B)
    (hSinv : ∀ p, p.Prime → ∀ g ∈ G, ∀ R, IsRep g R → ∀ s ∈ S p, R * s ∈ S p)
    (hSfin : ∃ P : Finset ℕ, ∀ p, (hp : p.Prime) → p ∉ P → ∀ s ∈ S p, @dist p s = 0) :
    ∃ (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ), Squarefree N ∧ 0 < A.det ∧
      G.map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))).toMonoidHom ≤ Gamma0Plus N := by
  classical
  set 𝓡 : Set (Matrix (Fin 2) (Fin 2) ℤ) := {R | ∃ g ∈ G, IsRep g R} with h𝓡def
  have h𝓡 : ∀ p, p.Prime → ∀ R ∈ 𝓡, R.det ≠ 0 ∧ (∀ s ∈ S p, R * s ∈ S p) ∧
      (∀ s ∈ S p, R.adjugate * s ∈ S p) := by
    rintro p hp R ⟨g, hg, hR⟩
    exact ⟨hR.1, hSinv p hp g hg R hR, hSinv p hp g⁻¹ (G.inv_mem hg) _ hR.inv⟩
  -- the data at each prime
  have hdata : ∀ p, ∃ z z' : Matrix (Fin 2) (Fin 2) ℤ, p.Prime → z.det ≠ 0 ∧ z'.det ≠ 0 ∧
      ((∀ R ∈ 𝓡, @dd p z (R * z) = 0) ∨ (@dd p z z' = 1 ∧ ∀ R ∈ 𝓡, PresE p z z' R)) := by
    intro p
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨B, hB⟩ := hSbdd p hp
      rcases center_conclusion (hSdet p) (hSne p hp) hB 𝓡 (h𝓡 p hp) with ⟨z, hz, h⟩ | ⟨z, z', hz, hz', h⟩
      · exact ⟨z, z, fun _ => ⟨hz, hz, Or.inl h⟩⟩
      · exact ⟨z, z', fun _ => ⟨hz, hz', Or.inr h⟩⟩
    · exact ⟨1, 1, fun h => absurd h hp⟩
  choose z z' hzz using hdata
  obtain ⟨P₀, hP₀⟩ := hSfin
  set P := P₀.filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  -- outside P, the vertex 1 is fixed
  have hout : ∀ q, (hq : q.Prime) → q ∉ P → ∀ R ∈ 𝓡, @dd q 1 (R * 1) = 0 := by
    intro q hq hqP R hR
    have : Fact q.Prime := ⟨hq⟩
    have hqP₀ : q ∉ P₀ := fun h => hqP (Finset.mem_filter.2 ⟨h, hq⟩)
    obtain ⟨s, hs⟩ := hSne q hq
    obtain ⟨hR0, hRS, -⟩ := h𝓡 q hq R hR
    have h1 : dd q 1 s = 0 := by rw [dd_one_left]; exact hP₀ q hq hqP₀ s hs
    have h2 : dd q 1 (R * s) = 0 := by rw [dd_one_left]; exact hP₀ q hq hqP₀ _ (hRS s hs)
    have h3 := dd_triangle (p := q) (by simp : (1 : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0)
      (det_mul_ne_zero hR0 (hSdet q s hs)) (det_mul_ne_zero hR0 (by simp : (1 : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0))
    rw [h2, dd_mul_left hR0 (hSdet q s hs) (by simp), dd_comm (hSdet q s hs) (by simp), h1] at h3
    omega
  -- glue the vertices
  obtain ⟨Z, hZ, hZP, hZout⟩ := exists_glue P hPprime z (fun p hp => (hzz p (hPprime p hp)).1)
    (Z₀ := 1) (by simp)
  set PB := P.filter (fun p => ¬ ∀ R ∈ 𝓡, @dd p (z p) (R * z p) = 0) with hPBdef
  have hPBP : ∀ p ∈ PB, p ∈ P := fun p hp => (Finset.mem_filter.1 hp).1
  have hPBprime : ∀ p ∈ PB, p.Prime := fun p hp => hPprime p (hPBP p hp)
  have hPBedge : ∀ p ∈ PB, @dd p (z p) (z' p) = 1 ∧ ∀ R ∈ 𝓡, PresE p (z p) (z' p) R := by
    intro p hp
    have h := (hzz p (hPBprime p hp)).2.2
    exact h.resolve_left (Finset.mem_filter.1 hp).2
  obtain ⟨Z', hZ', hZ'PB, hZ'out⟩ := exists_glue PB hPBprime z' (fun p hp => (hzz p (hPBprime p hp)).2.1)
    (Z₀ := Z) hZ
  -- the Smith form of adj(Z)·Z'
  obtain ⟨U, V, hU, hV, e₁, e₂, he₁₂, hX⟩ := exists_snf (Z.adjugate * Z')
  have hXdet : (Z.adjugate * Z').det ≠ 0 := det_mul_ne_zero (det_adjugate_ne_zero hZ) hZ'
  have hDdet : (!![e₁, 0; 0, e₂] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    intro h0; apply hXdet; rw [hX, det_mul, det_mul, h0]; ring
  have he₁ : e₁ ≠ 0 := by intro h0; apply hDdet; simp [det_fin_two_of, h0]
  have he₂ : e₂ ≠ 0 := by intro h0; apply hDdet; simp [det_fin_two_of, h0]
  obtain ⟨m, hm⟩ := he₁₂
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact he₂ hm
  -- v_q(m) = [q ∈ PB]
  have hvm : ∀ q, q.Prime → padicValInt q m = if q ∈ PB then 1 else 0 := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    have hU' := not_dvd_det_of_det_eq_one (p := q) hU
    have hV' := not_dvd_det_of_det_eq_one (p := q) hV
    have hdist : dd q Z Z' = padicValInt q m := by
      rw [dd, hX, dist_mul_unit hV' (det_mul_ne_zero (det_ne_zero_of_not_dvd hU') hDdet),
        dist_unit_mul hU' hDdet, dist_diag he₁ he₂, hm, padicValInt.mul he₁ hm0]
      omega
    rw [← hdist]
    split_ifs with hqPB
    · have h1 := hZP q (hPBP q hqPB)
      have h2 := hZ'PB q hqPB
      rw [dd_congr hZ (hzz q hq).1 hZ' (hzz q hq).2.1 h1 h2]
      exact (hPBedge q hqPB).1
    · exact hZ'out q hq hqPB
  set N := m.natAbs with hNdef
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.2 hm0
  have hvN : ∀ q, q.Prime → padicValNat q N = if q ∈ PB then 1 else 0 := fun q hq => hvm q hq
  have hNsq : Squarefree N := by
    rw [Nat.squarefree_iff_factorization_le_one hN0]
    intro q
    by_cases hq : q.Prime
    · rw [Nat.factorization_def N hq, hvN q hq]; split_ifs <;> omega
    · simp [Nat.factorization_eq_zero_of_not_prime N hq]
  have hdvdN : ∀ q, q.Prime → (q ∣ N ↔ q ∈ PB) := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    have hv := hvN q hq
    constructor
    · intro h
      have := one_le_padicValNat_of_dvd hN0 h
      by_contra h'
      rw [if_neg h'] at hv
      omega
    · intro h
      rw [if_pos h] at hv
      exact dvd_of_one_le_padicValNat (by omega)
  -- Z* = Z·U, with positive determinant
  set J : Matrix (Fin 2) (Fin 2) ℤ := if 0 < Z.det then 1 else !![1, 0; 0, -1] with hJdef
  have hJ : J.det = 1 ∨ J.det = -1 := by
    rw [hJdef]; split_ifs
    · left; simp
    · right; simp [det_fin_two_of]
  have hJu : ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ J.det := by
    intro q hq h
    rcases hJ with h' | h' <;> rw [h'] at h
    · norm_cast at h; exact hq.not_dvd_one h
    · rw [dvd_neg] at h; norm_cast at h; exact hq.not_dvd_one h
  set Zs := Z * U * J with hZs
  have hZsdet : Zs.det = Z.det * J.det := by rw [hZs, det_mul, det_mul, hU, mul_one]
  have hZspos : 0 < Zs.det := by
    rw [hZsdet, hJdef]
    split_ifs with h
    · simpa using h
    · have : Z.det < 0 := lt_of_le_of_ne (not_lt.1 h) hZ
      simp [det_fin_two_of]; linarith
  have hZs0 : Zs.det ≠ 0 := hZspos.ne'
  have hJD : J * diagN N = diagN N * J := by
    rw [hJdef]; split_ifs
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [diagN, mul_apply, Fin.sum_univ_two, vecMul, dotProduct]
  have hD0 : (diagN N).det ≠ 0 := by rw [det_diagN]; exact_mod_cast hN0
  have hZZs : ∀ q, q.Prime → @dd q Z Zs = 0 := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    rw [hZs, dd_mul_unit_right (hJu q hq) hZ (det_mul_ne_zero hZ (by rw [hU]; exact one_ne_zero)),
      dd_mul_unit_right (not_dvd_det_of_det_eq_one hU) hZ hZ, dd_self hZ]
  have hZsD : ∀ q, q.Prime → @dd q (Zs * diagN N) Z' = 0 := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    have hU0 : U.det ≠ 0 := by rw [hU]; exact one_ne_zero
    have e1 : Zs * diagN N = Z * U * diagN N * J := by
      rw [hZs, Matrix.mul_assoc (Z * U), hJD, ← Matrix.mul_assoc]
    rw [e1, dd_mul_unit_left (hJu q hq) (det_mul_ne_zero (det_mul_ne_zero hZ hU0) hD0) hZ']
    have e2 : (Z * U * diagN N).adjugate * Z' = e₁ • (!![(N : ℤ), 0; 0, m] * V) := by
      rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc, hX,
        ← Matrix.mul_assoc U.adjugate, ← Matrix.mul_assoc U.adjugate, adjugate_mul, hU, one_smul,
        Matrix.one_mul, ← Matrix.mul_assoc, diagN, adjugate_fin_two_of, hm, ← smul_mul]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, vecMul, dotProduct] <;> ring
    have hNm : (!![(N : ℤ), 0; 0, m] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
      rw [det_fin_two_of]; simpa using ⟨by exact_mod_cast hN0, hm0⟩
    have hV' := not_dvd_det_of_det_eq_one (p := q) hV
    rw [dd, e2, dist_smul he₁ (det_mul_ne_zero hNm (det_ne_zero_of_not_dvd hV')), dist_mul_unit hV' hNm,
      dist_diag (by exact_mod_cast hN0) hm0]
    have : padicValInt q (N : ℤ) = padicValInt q m := by
      rw [hNdef, padicValInt, Int.natAbs_natCast, padicValInt]
    omega
  -- the local conditions at Zs
  have hfixZs : ∀ q, (hq : q.Prime) → q ∉ PB → ∀ R ∈ 𝓡, @dd q Zs (R * Zs) = 0 := by
    intro q hq hqPB R hR
    have : Fact q.Prime := ⟨hq⟩
    have hR0 := (h𝓡 q hq R hR).1
    by_cases hqP : q ∈ P
    · have hv : ∀ R ∈ 𝓡, dd q (z q) (R * z q) = 0 := by
        by_contra h
        exact hqPB (Finset.mem_filter.2 ⟨hqP, h⟩)
      have hzZs : dd q (z q) Zs = 0 := by
        have := dd_triangle (p := q) (hzz q hq).1 hZ hZs0
        rw [dd_comm (hzz q hq).1 hZ, hZP q hqP, hZZs q hq] at this
        omega
      rw [← dd_mul_congr (hzz q hq).1 hZs0 (hzz q hq).1 hZs0 hR0 hzZs hzZs]
      exact hv R hR
    · have h1Zs : dd q 1 Zs = 0 := by
        have := dd_triangle (p := q) (by simp : (1 : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0) hZ hZs0
        rw [hZout q hq hqP, hZZs q hq] at this
        omega
      rw [← dd_mul_congr (by simp) hZs0 (by simp) hZs0 hR0 h1Zs h1Zs]
      exact hout q hq hqP R hR
  have hedgeZs : ∀ q, q.Prime → q ∈ PB → ∀ R ∈ 𝓡, PresE q Zs (Zs * diagN N) R := by
    intro q hq hqPB R hR
    have : Fact q.Prime := ⟨hq⟩
    have hR0 := (h𝓡 q hq R hR).1
    have hzZs : dd q (z q) Zs = 0 := by
      have := dd_triangle (p := q) (hzz q hq).1 hZ hZs0
      rw [dd_comm (hzz q hq).1 hZ, hZP q (hPBP q hqPB), hZZs q hq] at this
      omega
    have hz'ZsD : dd q (z' q) (Zs * diagN N) = 0 := by
      have := dd_triangle (p := q) (hzz q hq).2.1 hZ' (det_mul_ne_zero hZs0 hD0)
      rw [dd_comm (hzz q hq).2.1 hZ', hZ'PB q hqPB, dd_comm hZ' (det_mul_ne_zero hZs0 hD0),
        hZsD q hq] at this
      omega
    exact presE_congr (hzz q hq).1 hZs0 (hzz q hq).2.1 (det_mul_ne_zero hZs0 hD0) hR0 hzZs hz'ZsD
      ((hPBedge q hqPB).2 R hR)
  -- conjugate
  refine ⟨N, Zs.adjugate, hNsq, by rwa [det_adjugate'], ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨R, hR⟩ := hrep g hg
  have hR𝓡 : R ∈ 𝓡 := ⟨g, hg, hR⟩
  have hA : 0 < Zs.adjugate.det := by rwa [det_adjugate']
  have hrep' : IsRep ((MulAut.conj (projSL (Zs.adjugate.map (Int.cast : ℤ → ℝ)))).toMonoidHom g)
      (Zs.adjugate * R * Zs) := by
    have h1 := (isRep_projSL hA).mul hR
    have h2 := h1.mul (isRep_projSL hA).inv
    rw [adjugate_adjugate'] at h2
    simpa [MulAut.conj_apply] using h2
  apply mem_gamma0Plus_of_local hNsq hrep'
  · intro q hq hqN
    have : Fact q.Prime := ⟨hq⟩
    rw [dd_conj hZs0 hR.1 (by simp) (by simp)]
    simp only [Matrix.mul_one]
    exact hfixZs q hq (fun h => hqN ((hdvdN q hq).2 h)) R hR𝓡
  · intro q hq hqN
    have : Fact q.Prime := ⟨hq⟩
    have h := hedgeZs q hq ((hdvdN q hq).1 hqN) R hR𝓡
    unfold PresE at h ⊢
    rw [dd_conj hZs0 hR.1 (by simp) (by simp), dd_conj hZs0 hR.1 hD0 hD0, dd_conj hZs0 hR.1 hD0 (by simp),
      dd_conj hZs0 hR.1 (by simp) hD0]
    simpa only [Matrix.mul_one] using h

end NormalizerLean.Helling
