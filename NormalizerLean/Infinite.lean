import NormalizerLean.Defs

/-!
# Infinite presented groups via affine (wreath) actions — T8(b)

A certificate gives, for each generator x ∈ {w, s}, a permutation σₓ of {0, …, n−1} and integers tₓ(i).
The generator x acts on ℕ × ℤ on the right by (i, m) ↦ (σₓ(i), m + tₓ(i)) for i < n, and trivially
for i ≥ n.  If every relator acts trivially, this is a homomorphism from the presented group to
(Perm (ℕ × ℤ))ᵐᵒᵖ; if moreover some word fixes the first coordinate 0 and translates by c ≠ 0, its
image has infinite order, so the presented group is infinite.  All conditions are decidable and are
checked by `decide`; the data come from `certs/infinite_cert.py` (Magma + Reidemeister–Schreier).
-/

namespace NormalizerLean

/-- Affine action data. -/
structure AffCert where
  n : ℕ
  σ : LGen → List ℕ
  σinv : LGen → List ℕ
  t : LGen → List ℤ

namespace AffCert

variable (D : AffCert)

def sg (x : LGen) (i : ℕ) : ℕ := (D.σ x).getD i i
def sgi (x : LGen) (i : ℕ) : ℕ := (D.σinv x).getD i i
def tr (x : LGen) (i : ℕ) : ℤ := (D.t x).getD i 0

def fwd (x : LGen) (p : ℕ × ℤ) : ℕ × ℤ :=
  if p.1 < D.n then (D.sg x p.1, p.2 + D.tr x p.1) else p

def bwd (x : LGen) (p : ℕ × ℤ) : ℕ × ℤ :=
  if p.1 < D.n then (D.sgi x p.1, p.2 - D.tr x (D.sgi x p.1)) else p

def step (p : ℕ × ℤ) (a : LGen × Bool) : ℕ × ℤ := if a.2 then D.fwd a.1 p else D.bwd a.1 p

/-- The right action of a word. -/
def wordAct (L : List (LGen × Bool)) (p : ℕ × ℤ) : ℕ × ℤ := L.foldl D.step p

/-- σₓ is a permutation of {0, …, n−1} with inverse σinvₓ. -/
def valid : Bool :=
  (List.range D.n).all fun i => [LGen.w, LGen.s].all fun x =>
    decide (D.sg x i < D.n) && decide (D.sgi x i < D.n) && (D.sgi x (D.sg x i) == i) &&
      (D.sg x (D.sgi x i) == i)

/-- The word acts trivially on every (i, 0), i < n. -/
def fixesAll (L : List (LGen × Bool)) : Bool :=
  (List.range D.n).all fun i => D.wordAct L (i, 0) == (i, 0)

/-- The word maps (0, 0) to (0, c) with c ≠ 0. -/
def translates (L : List (LGen × Bool)) : Bool :=
  decide (0 < D.n) && ((D.wordAct L (0, 0)).1 == 0) && ((D.wordAct L (0, 0)).2 != 0)

variable {D}

theorem valid_spec (hD : D.valid = true) (x : LGen) {i : ℕ} (hi : i < D.n) :
    D.sg x i < D.n ∧ D.sgi x i < D.n ∧ D.sgi x (D.sg x i) = i ∧ D.sg x (D.sgi x i) = i := by
  unfold valid at hD
  rw [List.all_eq_true] at hD
  have := hD i (List.mem_range.2 hi)
  rw [List.all_eq_true] at this
  have hx := this x (by cases x <;> simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
  exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

theorem bwd_fwd (hD : D.valid = true) (x : LGen) (p : ℕ × ℤ) : D.bwd x (D.fwd x p) = p := by
  obtain ⟨i, m⟩ := p
  unfold fwd bwd
  by_cases hi : i < D.n
  · obtain ⟨h1, -, h3, -⟩ := valid_spec hD x hi
    simp [hi, h1, h3]
  · simp [hi]

theorem fwd_bwd (hD : D.valid = true) (x : LGen) (p : ℕ × ℤ) : D.fwd x (D.bwd x p) = p := by
  obtain ⟨i, m⟩ := p
  unfold fwd bwd
  by_cases hi : i < D.n
  · obtain ⟨-, h2, -, h4⟩ := valid_spec hD x hi
    simp [hi, h2, h4]
  · simp [hi]

/-- The permutation of ℕ × ℤ given by a generator. -/
def equiv (hD : D.valid = true) (x : LGen) : Equiv.Perm (ℕ × ℤ) where
  toFun := D.fwd x
  invFun := D.bwd x
  left_inv := bwd_fwd hD x
  right_inv := fwd_bwd hD x

/-- The generator images, in the opposite group (so that the right action becomes a hom). -/
def gen (hD : D.valid = true) (x : LGen) : (Equiv.Perm (ℕ × ℤ))ᵐᵒᵖ :=
  MulOpposite.op (equiv hD x)

theorem lift_mk_apply (hD : D.valid = true) (L : List (LGen × Bool)) (p : ℕ × ℤ) :
    (MulOpposite.unop (FreeGroup.lift (gen hD) (FreeGroup.mk L))) p = D.wordAct L p := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih =>
    have hmk : FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L := by
      rw [FreeGroup.mul_mk]; rfl
    rw [hmk, map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply]
    obtain ⟨x, b⟩ := a
    have hstep : (MulOpposite.unop (FreeGroup.lift (gen hD) (FreeGroup.mk [(x, b)]))) p =
        D.step p (x, b) := by
      cases b
      · have : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := rfl
        rw [this, map_inv, FreeGroup.lift_apply_of]
        rfl
      · have : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
        rw [this, FreeGroup.lift_apply_of]
        rfl
    rw [hstep, ih]
    rfl

/-- Translating the ℤ-coordinate commutes with the action. -/
theorem step_shift (a : LGen × Bool) (i : ℕ) (m c : ℤ) :
    D.step (i, m + c) a = ((D.step (i, m) a).1, (D.step (i, m) a).2 + c) := by
  obtain ⟨x, b⟩ := a
  cases b <;> simp only [step, fwd, bwd] <;> split_ifs <;> simp <;> ring

theorem wordAct_shift (L : List (LGen × Bool)) (i : ℕ) (m c : ℤ) :
    D.wordAct L (i, m + c) = ((D.wordAct L (i, m)).1, (D.wordAct L (i, m)).2 + c) := by
  induction L generalizing i m with
  | nil => rfl
  | cons a L ih =>
    simp only [wordAct, List.foldl_cons] at ih ⊢
    rw [step_shift]
    exact ih _ _

theorem wordAct_large (L : List (LGen × Bool)) (p : ℕ × ℤ) (hp : D.n ≤ p.1) :
    D.wordAct L p = p := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [wordAct, List.foldl_cons] at ih ⊢
    have : D.step p a = p := by
      obtain ⟨x, b⟩ := a
      cases b <;> simp [step, fwd, bwd, not_lt.2 hp]
    rw [this]
    exact ih

theorem lift_eq_one_of_fixesAll (hD : D.valid = true) (ρ : FreeGroup LGen)
    (h : D.fixesAll ρ.toWord = true) : FreeGroup.lift (gen hD) ρ = 1 := by
  apply MulOpposite.unop_injective
  ext p : 1
  rw [← FreeGroup.mk_toWord (x := ρ), lift_mk_apply, MulOpposite.unop_one, Equiv.Perm.one_apply]
  obtain ⟨i, m⟩ := p
  by_cases hi : i < D.n
  · unfold fixesAll at h
    rw [List.all_eq_true] at h
    have h0 := h i (List.mem_range.2 hi)
    rw [beq_iff_eq] at h0
    have := wordAct_shift (D := D) ρ.toWord i 0 m
    rw [zero_add] at this
    rw [this, h0]
    simp
  · exact wordAct_large _ _ (not_lt.1 hi)

/-- **Main lemma**: a valid certificate with trivially acting relators and a translating word proves
the presented group infinite. -/
theorem infinite_of_cert {rels : Set (FreeGroup LGen)} (hD : D.valid = true)
    (hrels : ∀ r ∈ rels, D.fixesAll r.toWord = true) (u : List (LGen × Bool))
    (hu : D.translates u = true) : Infinite (PresentedGroup rels) := by
  let φ := PresentedGroup.toGroup (f := gen hD) (rels := rels)
    (fun r hr => lift_eq_one_of_fixesAll hD r (hrels r hr))
  simp only [translates, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    ne_eq] at hu
  obtain ⟨⟨hn, h1⟩, h2⟩ := hu
  set c := (D.wordAct u (0, 0)).2
  let g : PresentedGroup rels := PresentedGroup.mk rels (FreeGroup.mk u)
  have hφg : ∀ m : ℤ, (MulOpposite.unop (φ g)) (0, m) = (0, m + c) := by
    intro m
    have : φ g = FreeGroup.lift (gen hD) (FreeGroup.mk u) := rfl
    rw [this, lift_mk_apply, show ((0 : ℕ), m) = (0, 0 + m) by simp, wordAct_shift, h1]
    simp [c, add_comm]
  have hpow : ∀ k : ℕ, (MulOpposite.unop (φ g ^ k)) (0, 0) = (0, k * c) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulOpposite.unop_mul, Equiv.Perm.mul_apply, ih, hφg]
      push_cast
      ring_nf
  rw [← not_finite_iff_infinite]
  intro hfin
  obtain ⟨k, hk, hgk⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  have := hpow k
  rw [← map_pow, hgk, map_one, MulOpposite.unop_one, Equiv.Perm.one_apply] at this
  have hk' : (k : ℤ) * c = 0 := (Prod.ext_iff.1 this).2.symm
  rcases mul_eq_zero.1 hk' with h | h
  · omega
  · exact h2 h

end AffCert

end NormalizerLean
