module

public import NormalizerDelta.HellingSNF

@[expose] public section

/-!
# Part 9: the centre of a bounded set of vertices of the p-adic tree

Let S be a nonempty set of integral matrices (vertices [sℤ_(p)²]) on which d_p is bounded.  The radius of S seen
from z is r(z) = sup_{s ∈ S} dd_p(z, s); a *centre* is a z with minimal radius (`IsCenter`).

* `dd_le_one_of_isCenter`: two centres are at distance ≤ 1.  Otherwise, by the Smith form and the V shape
  (`dist_diagP_one_lt`), the neighbour of z₁ towards z₂ has a smaller radius.
* `isCenter_mul`: a matrix R that maps S into itself, together with its adjugate, maps centres to centres.
* `center_conclusion`: hence a set 𝓡 of such matrices fixes a vertex, or preserves an edge {z, z′} (each R fixing
  both ends or swapping them: `PresE`).  An R with v_p(det R) even cannot swap (`presE_fix_of_even`).
-/

open Matrix

namespace NormalizerLean.Helling

/-- The radius sup_{s ∈ S} dd_p(z, s) of S seen from z. -/
noncomputable def rad (p : ℕ) (S : Set (Matrix (Fin 2) (Fin 2) ℤ)) (z : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  sSup ((fun s => dd p z s) '' S)

/-- z is a centre of S: its radius is minimal. -/
def IsCenter (p : ℕ) (S : Set (Matrix (Fin 2) (Fin 2) ℤ)) (z : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  z.det ≠ 0 ∧ ∀ w : Matrix (Fin 2) (Fin 2) ℤ, w.det ≠ 0 → rad p S z ≤ rad p S w

/-- R preserves the edge {z, z′}: it fixes both ends or swaps them. -/
def PresE (p : ℕ) (z z' R : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (dd p z (R * z) = 0 ∧ dd p z' (R * z') = 0) ∨ (dd p z' (R * z) = 0 ∧ dd p z (R * z') = 0)

variable {p : ℕ} [hp : Fact p.Prime] {S : Set (Matrix (Fin 2) (Fin 2) ℤ)}

theorem dd_le_dist_add {z s : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hs : s.det ≠ 0) :
    dd p z s ≤ dist p z + dist p s := by
  have := dist_mul_le (p := p) (det_adjugate_ne_zero hz) hs
  rw [dist_adjugate hz] at this
  exact this

theorem bddAbove_dd (hSdet : ∀ s ∈ S, s.det ≠ 0) {B : ℕ} (hB : ∀ s ∈ S, dist p s ≤ B)
    {z : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) : BddAbove ((fun s => dd p z s) '' S) := by
  refine ⟨dist p z + B, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact (dd_le_dist_add hz (hSdet s hs)).trans (by have := hB s hs; omega)

theorem dd_le_rad (hSdet : ∀ s ∈ S, s.det ≠ 0) {B : ℕ} (hB : ∀ s ∈ S, dist p s ≤ B)
    {z s : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hs : s ∈ S) : dd p z s ≤ rad p S z :=
  le_csSup (bddAbove_dd hSdet hB hz) ⟨s, hs, rfl⟩

omit hp in
theorem rad_le (hSne : S.Nonempty) {z : Matrix (Fin 2) (Fin 2) ℤ} {r : ℕ} (h : ∀ s ∈ S, dd p z s ≤ r) :
    rad p S z ≤ r :=
  csSup_le (hSne.image _) (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

omit hp in
theorem exists_isCenter : ∃ z, IsCenter p S z := by
  classical
  have hex : ∃ n, ∃ z : Matrix (Fin 2) (Fin 2) ℤ, z.det ≠ 0 ∧ rad p S z = n := ⟨_, 1, by simp, rfl⟩
  obtain ⟨z, hz, hzn⟩ := Nat.find_spec hex
  refine ⟨z, hz, fun w hw => ?_⟩
  rw [hzn]
  exact Nat.find_min' hex ⟨w, hw, rfl⟩

/-- Two centres are at distance at most 1. -/
theorem dd_le_one_of_isCenter (hSdet : ∀ s ∈ S, s.det ≠ 0) (hSne : S.Nonempty) {B : ℕ}
    (hB : ∀ s ∈ S, dist p s ≤ B) {z₁ z₂ : Matrix (Fin 2) (Fin 2) ℤ} (h₁ : IsCenter p S z₁)
    (h₂ : IsCenter p S z₂) : dd p z₁ z₂ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hz₁ := h₁.1
  have hz₂ := h₂.1
  obtain ⟨U, V, hU, hV, x, y, hxy, hX⟩ := exists_snf (z₁.adjugate * z₂)
  have hXdet : (z₁.adjugate * z₂).det ≠ 0 := det_mul_ne_zero (det_adjugate_ne_zero hz₁) hz₂
  have hDdet : (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    intro h0
    apply hXdet
    rw [hX, det_mul, det_mul, h0]
    ring
  have hx : x ≠ 0 := by
    intro h0; apply hDdet; simp [det_fin_two_of, h0]
  have hy : y ≠ 0 := by
    intro h0; apply hDdet; simp [det_fin_two_of, h0]
  have hUp := not_dvd_det_of_det_eq_one (p := p) hU
  have hVp := not_dvd_det_of_det_eq_one (p := p) hV
  -- write x = p^a x', y = p^b y'
  obtain ⟨x', hx'p, hx'⟩ := exists_eq_pow_mul_not_dvd (p := p) hx
  obtain ⟨y', hy'p, hy'⟩ := exists_eq_pow_mul_not_dvd (p := p) hy
  set a := padicValInt p x
  set b := padicValInt p y
  have hab : a ≤ b := padicValInt_le_of_dvd hy hxy
  set n := b - a with hn
  -- the distance of z₁ and z₂ is n
  have hdist : dd p z₁ z₂ = n := by
    rw [dd, hX, dist_mul_unit hVp (det_mul_ne_zero (det_ne_zero_of_not_dvd hUp) hDdet),
      dist_unit_mul hUp hDdet, dist_diag hx hy]
    omega
  rw [hdist] at hlt
  -- the neighbour m of z₁ towards z₂
  set m := z₁ * U * !![1, 0; 0, (p : ℤ)] with hm
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmdet : m.det ≠ 0 := by
    rw [hm, det_mul, det_mul, hU, det_fin_two_of]
    simpa using ⟨hz₁, hp.out.ne_zero⟩
  have key : ∀ s ∈ S, dd p m s + 1 ≤ max (dd p z₁ s) (dd p z₂ s) := by
    intro s hs
    have hsdet := hSdet s hs
    set Y := U.adjugate * (z₁.adjugate * s) with hY
    have hYdet : Y.det ≠ 0 := det_mul_ne_zero (det_adjugate_ne_zero (det_ne_zero_of_not_dvd hUp))
      (det_mul_ne_zero (det_adjugate_ne_zero hz₁) hsdet)
    have e0 : dd p z₁ s = dist p Y := by
      rw [dd, hY, dist_unit_mul (by rwa [det_adjugate']) (det_mul_ne_zero (det_adjugate_ne_zero hz₁) hsdet)]
    have e1 : dd p m s = dist p (diagP p 1 * Y) := by
      have : m.adjugate * s = diagP p 1 * Y := by
        rw [hm, adjugate_mul_distrib, adjugate_mul_distrib, adjugate_fin_two_of, hY]
        simp only [diagP, pow_one, neg_zero, Matrix.mul_assoc]
      rw [dd, this]
    have e2 : dd p z₂ s = dist p (diagP p n * Y) := by
      -- det z₁ • adj z₂ = adj V * diag(y, x) * adj U * adj z₁
      have hz2 : z₁.det • z₂ = z₁ * U * !![x, 0; 0, y] * V := by
        rw [Matrix.mul_assoc (z₁ * U), Matrix.mul_assoc z₁, ← Matrix.mul_assoc U, ← hX, ← Matrix.mul_assoc,
          mul_adjugate, smul_mul, Matrix.one_mul]
      have hadj := congrArg Matrix.adjugate hz2
      rw [adjugate_smul, show Fintype.card (Fin 2) - 1 = 1 from rfl, pow_one, adjugate_mul_distrib,
        adjugate_mul_distrib, adjugate_mul_distrib, adjugate_fin_two_of] at hadj
      have hs2 : z₁.det • (z₂.adjugate * s) =
          V.adjugate * (!![y, -0; -0, x] * Y) := by
        rw [← smul_mul, hadj, hY]
        simp only [Matrix.mul_assoc]
      have hd : (!![y, -0; -0, x] : Matrix (Fin 2) (Fin 2) ℤ) =
          (p : ℤ) ^ a • (!![y', 0; 0, x'] * diagP p n) := by
        rw [hx', hy', diagP]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
        rw [show b = a + n by omega, pow_add]
        ring
      have hD'p : ¬ (p : ℤ) ∣ (!![y', 0; 0, x'] : Matrix (Fin 2) (Fin 2) ℤ).det := by
        rw [det_fin_two_of, mul_zero, sub_zero]
        exact fun h => (Int.Prime.dvd_mul' hp.out h).elim hy'p hx'p
      have hnY := det_diagP_mul_ne_zero (p := p) n hYdet
      have h3 : ((!![y', 0; 0, x'] * diagP p n) * Y).det ≠ 0 := by
        rw [Matrix.mul_assoc]
        exact det_mul_ne_zero (det_ne_zero_of_not_dvd hD'p) hnY
      have h4 : (!![y, -0; -0, x] * Y).det ≠ 0 := by
        rw [hd, smul_mul]
        exact det_smul_ne_zero (pow_ne_zero _ hp0) h3
      rw [dd, ← dist_smul hz₁ (det_mul_ne_zero (det_adjugate_ne_zero hz₂) hsdet), hs2,
        dist_unit_mul (by rwa [det_adjugate']) h4, hd, smul_mul, dist_smul (pow_ne_zero _ hp0) h3,
        Matrix.mul_assoc, dist_unit_mul hD'p hnY]
    rw [e0, e1, e2]
    exact dist_diagP_one_lt hYdet hlt
  -- so the radius of m is smaller
  have hr : rad p S z₁ = rad p S z₂ := le_antisymm (h₁.2 _ hz₂) (h₂.2 _ hz₁)
  have hmr : rad p S m + 1 ≤ rad p S z₁ := by
    obtain ⟨s₀, hs₀⟩ := hSne
    have : rad p S m ≤ rad p S z₁ - 1 := rad_le ⟨s₀, hs₀⟩ fun s hs => by
      have := key s hs
      have h1 := dd_le_rad hSdet hB hz₁ hs
      have h2 := dd_le_rad hSdet hB hz₂ hs
      rw [← hr] at h2
      omega
    have : 1 ≤ rad p S z₁ := by
      have := key s₀ hs₀
      have h1 := dd_le_rad hSdet hB hz₁ hs₀
      have h2 := dd_le_rad hSdet hB hz₂ hs₀
      rw [← hr] at h2
      omega
    omega
  have := h₁.2 m hmdet
  omega

theorem rad_mul_eq (hSdet : ∀ s ∈ S, s.det ≠ 0) (hSne : S.Nonempty) {B : ℕ} (hB : ∀ s ∈ S, dist p s ≤ B)
    {R z : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.det ≠ 0) (hz : z.det ≠ 0) (hRS : ∀ s ∈ S, R * s ∈ S)
    (hRS' : ∀ s ∈ S, R.adjugate * s ∈ S) : rad p S (R * z) = rad p S z := by
  apply le_antisymm
  · apply rad_le hSne
    intro s hs
    have hs0 := hSdet s hs
    have e : R * (R.adjugate * s) = R.det • s := by
      rw [← Matrix.mul_assoc, mul_adjugate, smul_mul, Matrix.one_mul]
    rw [← dd_smul_right hR (det_mul_ne_zero hR hz) hs0, ← e,
      dd_mul_left hR hz (det_mul_ne_zero (det_adjugate_ne_zero hR) hs0)]
    exact dd_le_rad hSdet hB hz (hRS' s hs)
  · apply rad_le hSne
    intro s hs
    rw [← dd_mul_left hR hz (hSdet s hs)]
    exact dd_le_rad hSdet hB (det_mul_ne_zero hR hz) (hRS s hs)

theorem isCenter_mul (hSdet : ∀ s ∈ S, s.det ≠ 0) (hSne : S.Nonempty) {B : ℕ} (hB : ∀ s ∈ S, dist p s ≤ B)
    {R z : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.det ≠ 0) (hRS : ∀ s ∈ S, R * s ∈ S)
    (hRS' : ∀ s ∈ S, R.adjugate * s ∈ S) (hz : IsCenter p S z) : IsCenter p S (R * z) :=
  ⟨det_mul_ne_zero hR hz.1, fun w hw => by rw [rad_mul_eq hSdet hSne hB hR hz.1 hRS hRS']; exact hz.2 w hw⟩

/-- Parity: if dd(a, b) = 1, no c is at distance exactly 1 from both. -/
theorem dd_eq_zero_or_of_dd_eq_one {a b c : Matrix (Fin 2) (Fin 2) ℤ} (ha : a.det ≠ 0) (hb : b.det ≠ 0)
    (hc : c.det ≠ 0) (hab : dd p a b = 1) (hac : dd p a c ≤ 1) (hbc : dd p b c ≤ 1) :
    dd p a c = 0 ∨ dd p b c = 0 := by
  have h1 := dd_mod_two (p := p) ha hb
  have h2 := dd_mod_two (p := p) ha hc
  have h3 := dd_mod_two (p := p) hb hc
  omega

/-- A set 𝓡 of matrices that map S into itself, with their adjugates, fixes a vertex or preserves an edge. -/
theorem center_conclusion (hSdet : ∀ s ∈ S, s.det ≠ 0) (hSne : S.Nonempty) {B : ℕ}
    (hB : ∀ s ∈ S, dist p s ≤ B) (𝓡 : Set (Matrix (Fin 2) (Fin 2) ℤ))
    (h𝓡 : ∀ R ∈ 𝓡, R.det ≠ 0 ∧ (∀ s ∈ S, R * s ∈ S) ∧ (∀ s ∈ S, R.adjugate * s ∈ S)) :
    (∃ z : Matrix (Fin 2) (Fin 2) ℤ, z.det ≠ 0 ∧ ∀ R ∈ 𝓡, dd p z (R * z) = 0) ∨
      (∃ z z' : Matrix (Fin 2) (Fin 2) ℤ, z.det ≠ 0 ∧ z'.det ≠ 0 ∧ dd p z z' = 1 ∧ ∀ R ∈ 𝓡, PresE p z z' R) := by
  obtain ⟨z, hz⟩ := exists_isCenter (p := p) (S := S)
  by_cases h : ∃ z', IsCenter p S z' ∧ dd p z z' = 1
  · obtain ⟨z', hz', hzz'⟩ := h
    right
    refine ⟨z, z', hz.1, hz'.1, hzz', fun R hR => ?_⟩
    obtain ⟨hR0, hRS, hRS'⟩ := h𝓡 R hR
    have hRz := isCenter_mul hSdet hSne hB hR0 hRS hRS' hz
    have hRz' := isCenter_mul hSdet hSne hB hR0 hRS hRS' hz'
    have e : dd p (R * z) (R * z') = 1 := by rw [dd_mul_left hR0 hz.1 hz'.1, hzz']
    have c1 := dd_eq_zero_or_of_dd_eq_one hz.1 hz'.1 hRz.1 hzz' (dd_le_one_of_isCenter hSdet hSne hB hz hRz)
      (dd_le_one_of_isCenter hSdet hSne hB hz' hRz)
    have c2 := dd_eq_zero_or_of_dd_eq_one hz.1 hz'.1 hRz'.1 hzz'
      (dd_le_one_of_isCenter hSdet hSne hB hz hRz') (dd_le_one_of_isCenter hSdet hSne hB hz' hRz')
    have t1 := dd_triangle (p := p) hRz.1 hz.1 hRz'.1
    have t2 := dd_triangle (p := p) hRz.1 hz'.1 hRz'.1
    rw [dd_comm hRz.1 hz.1] at t1
    rw [dd_comm hRz.1 hz'.1] at t2
    unfold PresE
    omega
  · left
    push Not at h
    refine ⟨z, hz.1, fun R hR => ?_⟩
    obtain ⟨hR0, hRS, hRS'⟩ := h𝓡 R hR
    have hRz := isCenter_mul hSdet hSne hB hR0 hRS hRS' hz
    have h1 := dd_le_one_of_isCenter hSdet hSne hB hz hRz
    have h2 := h (R * z) hRz
    omega

/-- An R with v_p(det R) even cannot swap the ends of an edge. -/
theorem presE_fix_of_even {z z' R : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hz' : z'.det ≠ 0)
    (hR : R.det ≠ 0) (hzz' : dd p z z' = 1) (hP : PresE p z z' R) (heven : vd p R % 2 = 0) :
    dd p z (R * z) = 0 ∧ dd p z' (R * z') = 0 := by
  rcases hP with hP | hP
  · exact hP
  · exfalso
    have h1 := dd_mod_two (p := p) hz hz'
    have h2 := dd_mod_two (p := p) hz' (det_mul_ne_zero hR hz)
    rw [hP.1, vd_mul hR hz] at h2
    rw [hzz'] at h1
    omega

/-- dd is unchanged when its arguments are replaced by equivalent vertices. -/
theorem dd_congr {z Z w W : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hZ : Z.det ≠ 0) (hw : w.det ≠ 0)
    (hW : W.det ≠ 0) (hzZ : dd p z Z = 0) (hwW : dd p w W = 0) : dd p z w = dd p Z W := by
  rw [dd_eq_of_dd_eq_zero hz hw hZ hzZ, dd_comm hZ hw, dd_comm hZ hW]
  exact dd_eq_of_dd_eq_zero hw hZ hW hwW

theorem dd_mul_congr {z Z w W R : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hZ : Z.det ≠ 0)
    (hw : w.det ≠ 0) (hW : W.det ≠ 0) (hR : R.det ≠ 0) (hzZ : dd p z Z = 0) (hwW : dd p w W = 0) :
    dd p z (R * w) = dd p Z (R * W) :=
  dd_congr hz hZ (det_mul_ne_zero hR hw) (det_mul_ne_zero hR hW) hzZ (by rw [dd_mul_left hR hw hW, hwW])

theorem presE_congr {z Z z' Z' R : Matrix (Fin 2) (Fin 2) ℤ} (hz : z.det ≠ 0) (hZ : Z.det ≠ 0)
    (hz' : z'.det ≠ 0) (hZ' : Z'.det ≠ 0) (hR : R.det ≠ 0) (hzZ : dd p z Z = 0) (hzZ' : dd p z' Z' = 0)
    (h : PresE p z z' R) : PresE p Z Z' R := by
  unfold PresE at h ⊢
  rw [← dd_mul_congr hz hZ hz hZ hR hzZ hzZ, ← dd_mul_congr hz' hZ' hz' hZ' hR hzZ' hzZ',
    ← dd_mul_congr hz' hZ' hz hZ hR hzZ' hzZ, ← dd_mul_congr hz hZ hz' hZ' hR hzZ hzZ']
  exact h

end NormalizerLean.Helling
