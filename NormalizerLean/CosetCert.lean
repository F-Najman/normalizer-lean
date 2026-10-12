import NormalizerLean.Defs

/-!
# Verified coset-enumeration certificates: `Nat.card (PresentedGroup R) = n`

A certificate for a presentation on the generators `LGen = {w, s}` consists of
* a right action of w, s on {0, …, n−1} (with inverses), in which every relator fixes every point;
* representative words `reps i` with `reps 0 = []` and 0 · reps i = i;
* a list of *deductions* (v, k, p): reading relator k from vertex v, every edge of the cycle except
  the one at position p is already known; that edge becomes known.  Initially the tree edges
  (reps (i · x) = reps i ++ [x], or reps i = reps (i · x) ++ [x⁻¹]) are known.
If finally every edge (i, x) is known, then i ↦ [reps i] is a bijection {0, …, n−1} → G:
* surjective, because the set of [reps i] is closed under right multiplication by the generators
  (every edge is a valid equation [reps i]·x = [reps (i·x)] in G, by induction over the deductions);
* injective, because the action is a homomorphism G → (Perm ℕ)ᵐᵒᵖ and [reps i] sends 0 to i.
The checker is a `Bool` function evaluated by `decide`; the data come from `certs/coset_cert.py`.
-/

namespace NormalizerLean

structure CosetCert where
  n : ℕ
  act : LGen → List ℕ
  actInv : LGen → List ℕ
  reps : List (List (LGen × Bool))
  deds : List (ℕ × ℕ × ℕ)

namespace CosetCert

/-- Index of the edge (i, x). -/
def edge (i : ℕ) (x : LGen) : ℕ := 2 * i + (match x with | .w => 0 | .s => 1)

theorem edge_inj {i j : ℕ} {x y : LGen} (h : edge i x = edge j y) : i = j ∧ x = y := by
  cases x <;> cases y <;> simp only [edge] at h <;> refine ⟨by omega, ?_⟩ <;>
    first | rfl | (exfalso; omega)

variable (C : CosetCert)

def ac (x : LGen) (i : ℕ) : ℕ := (C.act x).getD i i
def aci (x : LGen) (i : ℕ) : ℕ := (C.actInv x).getD i i
def stepI (i : ℕ) (a : LGen × Bool) : ℕ := if a.2 then C.ac a.1 i else C.aci a.1 i
def trace (i : ℕ) (L : List (LGen × Bool)) : ℕ := L.foldl C.stepI i
def letterEdge (i : ℕ) (a : LGen × Bool) : ℕ :=
  if a.2 then edge i a.1 else edge (C.aci a.1 i) a.1
def rep (i : ℕ) : List (LGen × Bool) := C.reps.getD i []

def pathKnown (K : ℕ) : ℕ → List (LGen × Bool) → Bool
  | _, [] => true
  | i, a :: L => K.testBit (C.letterEdge i a) && pathKnown K (C.stepI i a) L

def dedStep (RW : List (List (LGen × Bool))) (K : ℕ) (d : ℕ × ℕ × ℕ) : Option ℕ :=
  match (RW.getD d.2.1 []).drop d.2.2 with
  | [] => none
  | a :: L₂ =>
    if C.pathKnown K d.1 ((RW.getD d.2.1 []).take d.2.2) &&
        C.pathKnown K (C.stepI (C.trace d.1 ((RW.getD d.2.1 []).take d.2.2)) a) L₂ &&
        (C.trace (C.stepI (C.trace d.1 ((RW.getD d.2.1 []).take d.2.2)) a) L₂ == d.1) then
      some (K ||| (1 <<< C.letterEdge (C.trace d.1 ((RW.getD d.2.1 []).take d.2.2)) a))
    else none

def treeEdge (i : ℕ) (x : LGen) : Bool :=
  (C.rep (C.ac x i) == C.rep i ++ [(x, true)]) || (C.rep i == C.rep (C.ac x i) ++ [(x, false)])

def treeEdges : List (ℕ × LGen) :=
  (List.range C.n).flatMap fun i => ([LGen.w, LGen.s].filter fun x => C.treeEdge i x).map (i, ·)

def initKnown : ℕ := C.treeEdges.foldl (fun K e => K ||| (1 <<< edge e.1 e.2)) 0

def permOK : Bool :=
  [LGen.w, LGen.s].all fun x => ((C.act x).length == C.n) && ((C.actInv x).length == C.n) &&
    (List.range C.n).all fun i => decide (C.ac x i < C.n) && decide (C.aci x i < C.n) &&
      (C.aci x (C.ac x i) == i) && (C.ac x (C.aci x i) == i)

def allKnown (K : ℕ) : Bool :=
  (List.range C.n).all fun i => K.testBit (edge i .w) && K.testBit (edge i .s)

/-- The checker. -/
def check (RL : List (FreeGroup LGen)) : Bool :=
  decide (0 < C.n) && C.permOK && (C.rep 0 == []) &&
    ((List.range C.n).all fun i => C.trace 0 (C.rep i) == i) &&
    ((RL.map FreeGroup.toWord).all fun L => (List.range C.n).all fun i => C.trace i L == i) &&
    match C.deds.foldlM (C.dedStep (RL.map FreeGroup.toWord)) C.initKnown with
    | some K => C.allKnown K
    | none => false

/-! ### The permutation part -/

variable {C}

theorem permOK_spec (h : C.permOK = true) (x : LGen) :
    (C.act x).length = C.n ∧ (C.actInv x).length = C.n ∧ ∀ i < C.n,
      C.ac x i < C.n ∧ C.aci x i < C.n ∧ C.aci x (C.ac x i) = i ∧ C.ac x (C.aci x i) = i := by
  unfold permOK at h
  rw [List.all_eq_true] at h
  have hx := h x (by cases x <;> simp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hx
  exact ⟨hx.1.1, hx.1.2, fun i hi => ⟨(hx.2 i hi).1.1.1, (hx.2 i hi).1.1.2, (hx.2 i hi).1.2,
    (hx.2 i hi).2⟩⟩

theorem ac_large (h : C.permOK = true) (x : LGen) {i : ℕ} (hi : C.n ≤ i) : C.ac x i = i :=
  List.getD_eq_default _ _ (by rw [(permOK_spec h x).1]; exact hi)

theorem aci_large (h : C.permOK = true) (x : LGen) {i : ℕ} (hi : C.n ≤ i) : C.aci x i = i :=
  List.getD_eq_default _ _ (by rw [(permOK_spec h x).2.1]; exact hi)

theorem aci_ac (h : C.permOK = true) (x : LGen) (i : ℕ) : C.aci x (C.ac x i) = i := by
  by_cases hi : i < C.n
  · exact ((permOK_spec h x).2.2 i hi).2.2.1
  · rw [ac_large h x (not_lt.1 hi), aci_large h x (not_lt.1 hi)]

theorem ac_aci (h : C.permOK = true) (x : LGen) (i : ℕ) : C.ac x (C.aci x i) = i := by
  by_cases hi : i < C.n
  · exact ((permOK_spec h x).2.2 i hi).2.2.2
  · rw [aci_large h x (not_lt.1 hi), ac_large h x (not_lt.1 hi)]

theorem trace_large (h : C.permOK = true) (L : List (LGen × Bool)) {i : ℕ} (hi : C.n ≤ i) :
    C.trace i L = i := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [trace, List.foldl_cons] at ih ⊢
    have : C.stepI i a = i := by
      unfold stepI
      split_ifs
      · exact ac_large h _ hi
      · exact aci_large h _ hi
    rw [this]
    exact ih

/-! ### Soundness of the deductions -/

variable {R : Set (FreeGroup LGen)}

/-- The image of a letter in the presented group. -/
def gl (R : Set (FreeGroup LGen)) (a : LGen × Bool) : PresentedGroup R :=
  if a.2 then PresentedGroup.of a.1 else (PresentedGroup.of a.1)⁻¹

theorem mk_mk_eq_prod (L : List (LGen × Bool)) :
    PresentedGroup.mk R (FreeGroup.mk L) = (L.map (gl R)).prod := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [show FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L by rw [FreeGroup.mul_mk]; rfl,
      map_mul, ih, List.map_cons, List.prod_cons]
    obtain ⟨x, b⟩ := a
    cases b
    · rw [show FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ from rfl, map_inv]; rfl
    · rfl

variable (C R)

/-- The representatives in the presented group. -/
def f (i : ℕ) : PresentedGroup R := PresentedGroup.mk R (FreeGroup.mk (C.rep i))

/-- The edge (i, x) is a valid equation in the presented group. -/
def Valid (i : ℕ) (x : LGen) : Prop := C.f R i * PresentedGroup.of x = C.f R (C.ac x i)

/-- All known edges are valid. -/
def Inv (K : ℕ) : Prop := ∀ i x, K.testBit (edge i x) = true → C.Valid R i x

variable {C R}

theorem step_valid (h : C.permOK = true) {K : ℕ} (hK : C.Inv R K) {c : ℕ} {a : LGen × Bool}
    (he : K.testBit (C.letterEdge c a) = true) : C.f R c * gl R a = C.f R (C.stepI c a) := by
  obtain ⟨x, b⟩ := a
  cases b
  · have hv := hK _ _ he
    unfold Valid at hv
    rw [ac_aci h] at hv
    simp only [gl, stepI, Bool.false_eq_true, ↓reduceIte]
    rw [← hv, mul_inv_cancel_right]
  · exact hK _ _ he

theorem path_valid (h : C.permOK = true) {K : ℕ} (hK : C.Inv R K) :
    ∀ (L : List (LGen × Bool)) (i : ℕ), C.pathKnown K i L = true →
      C.f R i * (L.map (gl R)).prod = C.f R (C.trace i L)
  | [], i, _ => by simp [trace]
  | a :: L, i, hp => by
    simp only [pathKnown, Bool.and_eq_true] at hp
    rw [List.map_cons, List.prod_cons, ← mul_assoc, step_valid h hK hp.1,
      path_valid h hK L _ hp.2]
    rfl

theorem valid_of_step (h : C.permOK = true) {c : ℕ} {a : LGen × Bool}
    (hs : C.f R c * gl R a = C.f R (C.stepI c a)) :
    ∀ i x, edge i x = C.letterEdge c a → C.Valid R i x := by
  intro i x hix
  obtain ⟨y, b⟩ := a
  cases b
  · simp only [letterEdge, Bool.false_eq_true, ↓reduceIte] at hix
    obtain ⟨rfl, rfl⟩ := edge_inj hix
    simp only [gl, stepI, Bool.false_eq_true, ↓reduceIte] at hs
    unfold Valid
    rw [ac_aci h, ← hs, inv_mul_cancel_right]
  · simp only [letterEdge, ↓reduceIte] at hix
    obtain ⟨rfl, rfl⟩ := edge_inj hix
    exact hs

theorem inv_or {C : CosetCert} {K : ℕ} (hK : C.Inv R K) {e : ℕ}
    (he : ∀ i x, edge i x = e → C.Valid R i x) : C.Inv R (K ||| (1 <<< e)) := by
  intro i x hb
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at hb
  rcases hb with hb | hb
  · exact hK i x hb
  · exact he i x hb.symm

theorem dedStep_inv (h : C.permOK = true) {RL : List (FreeGroup LGen)}
    (hRL : ∀ r ∈ RL, r ∈ R) {K K' : ℕ} (hK : C.Inv R K) {d : ℕ × ℕ × ℕ}
    (hd : C.dedStep (RL.map FreeGroup.toWord) K d = some K') : C.Inv R K' := by
  obtain ⟨v, k, p⟩ := d
  unfold dedStep at hd
  set L := (RL.map FreeGroup.toWord).getD k [] with hL
  split at hd
  · simp at hd
  · rename_i a L₂ hdrop
    simp only at hd
    split_ifs at hd with hc
    simp only [Option.some.injEq] at hd
    subst hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    set L₁ := L.take p
    set c := C.trace v L₁
    -- the relator is trivial in the group
    have hrel : (L.map (gl R)).prod = 1 := by
      by_cases hk : k < RL.length
      · have hLk : L = (RL[k]).toWord := by
          rw [hL, List.getD_eq_getElem _ _ (by simpa using hk)]
          simp
        rw [← mk_mk_eq_prod, hLk, FreeGroup.mk_toWord]
        exact PresentedGroup.one_of_mem (hRL _ (List.getElem_mem hk))
      · rw [hL, List.getD_eq_default _ _ (by simpa using hk)]
        rfl
    have hsplit : L = L₁ ++ a :: L₂ := by rw [← hdrop, List.take_append_drop]
    have hP₁ := path_valid h hK L₁ v h1
    have hP₂ := path_valid h hK L₂ _ h2
    rw [h3] at hP₂
    have hprod : (L₁.map (gl R)).prod * gl R a * (L₂.map (gl R)).prod = 1 := by
      rw [← hrel, hsplit, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
        mul_assoc]
    have hs : C.f R c * gl R a = C.f R (C.stepI c a) := by
      have e1 : (L₁.map (gl R)).prod * gl R a = ((L₂.map (gl R)).prod)⁻¹ :=
        eq_inv_of_mul_eq_one_left hprod
      calc C.f R c * gl R a = C.f R v * (L₁.map (gl R)).prod * gl R a := by rw [hP₁]
        _ = C.f R v * ((L₂.map (gl R)).prod)⁻¹ := by rw [mul_assoc, e1]
        _ = C.f R (C.stepI c a) := by rw [← hP₂, mul_inv_cancel_right]
    exact inv_or hK (valid_of_step h hs)

theorem foldlM_inv (h : C.permOK = true) {RL : List (FreeGroup LGen)}
    (hRL : ∀ r ∈ RL, r ∈ R) :
    ∀ (ds : List (ℕ × ℕ × ℕ)) (K K' : ℕ), C.Inv R K →
      ds.foldlM (C.dedStep (RL.map FreeGroup.toWord)) K = some K' → C.Inv R K'
  | [], K, K', hK, hf => by
    simp only [List.foldlM_nil] at hf
    cases hf
    exact hK
  | d :: ds, K, K', hK, hf => by
    rw [List.foldlM_cons] at hf
    cases hd : C.dedStep (RL.map FreeGroup.toWord) K d with
    | none => rw [hd] at hf; cases hf
    | some K₁ =>
      rw [hd] at hf
      exact foldlM_inv h hRL ds K₁ K' (dedStep_inv h hRL hK hd) hf

theorem testBit_foldl {β : Type*} (g : β → ℕ) :
    ∀ (L : List β) (K₀ b : ℕ),
      (L.foldl (fun K e => K ||| (1 <<< g e)) K₀).testBit b = true →
        K₀.testBit b = true ∨ ∃ e ∈ L, g e = b
  | [], K₀, b, hb => Or.inl hb
  | e :: L, K₀, b, hb => by
    rcases testBit_foldl g L _ b hb with h1 | ⟨e', he', h2⟩
    · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨e, List.mem_cons_self .., h1⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h2⟩

theorem init_inv : C.Inv R C.initKnown := by
  intro i x hb
  rcases testBit_foldl (fun e : ℕ × LGen => edge e.1 e.2) _ 0 _ hb with h0 | ⟨⟨j, y⟩, hmem, he⟩
  · simp at h0
  obtain ⟨rfl, rfl⟩ := edge_inj he
  simp only [treeEdges, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Prod.mk.injEq] at hmem
  obtain ⟨i', -, x', ⟨-, htree⟩, rfl, rfl⟩ := hmem
  unfold treeEdge at htree
  simp only [Bool.or_eq_true, beq_iff_eq] at htree
  unfold Valid f
  rcases htree with ht | ht
  · rw [ht, ← FreeGroup.mul_mk, map_mul]
    rfl
  · rw [ht, ← FreeGroup.mul_mk, map_mul, mul_assoc]
    rw [show FreeGroup.mk [(x', false)] = (FreeGroup.of x')⁻¹ from rfl, map_inv]
    simp [PresentedGroup.of]

/-! ### The lower bound: the action -/

def permGen (h : C.permOK = true) (x : LGen) : (Equiv.Perm ℕ)ᵐᵒᵖ :=
  MulOpposite.op ⟨C.ac x, C.aci x, aci_ac h x, ac_aci h x⟩

theorem lift_mk_apply (h : C.permOK = true) (L : List (LGen × Bool)) (i : ℕ) :
    (MulOpposite.unop (FreeGroup.lift (permGen h) (FreeGroup.mk L))) i = C.trace i L := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih =>
    rw [show FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L by rw [FreeGroup.mul_mk]; rfl,
      map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply]
    obtain ⟨x, b⟩ := a
    have hstep : (MulOpposite.unop (FreeGroup.lift (permGen h) (FreeGroup.mk [(x, b)]))) i =
        C.stepI i (x, b) := by
      cases b
      · rw [show FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        rfl
      · rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl, FreeGroup.lift_apply_of]
        rfl
    rw [hstep, ih]
    rfl

/-! ### Main theorem -/

theorem card_eq_of_check {RL : List (FreeGroup LGen)} (hR : ∀ r, r ∈ R ↔ r ∈ RL)
    (hC : C.check RL = true) : Nat.card (PresentedGroup R) = C.n := by
  unfold check at hC
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.mem_map] at hC
  obtain ⟨⟨⟨⟨⟨hn, hperm⟩, hrep0⟩, hreps⟩, hrels⟩, hfold⟩ := hC
  -- all edges valid
  have hall : ∀ i < C.n, ∀ x, C.Valid R i x := by
    split at hfold
    · rename_i K hK
      have hinv := foldlM_inv (R := R) hperm (fun r hr => (hR r).2 hr) C.deds _ K init_inv hK
      unfold allKnown at hfold
      simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hfold
      intro i hi x
      cases x
      · exact hinv _ _ (hfold i hi).1
      · exact hinv _ _ (hfold i hi).2
    · simp at hfold
  -- the action
  let ψ := PresentedGroup.toGroup (f := permGen hperm) (rels := R) (fun r hr => by
    apply MulOpposite.unop_injective
    ext i : 1
    rw [← FreeGroup.mk_toWord (x := r), lift_mk_apply, MulOpposite.unop_one, Equiv.Perm.one_apply]
    by_cases hi : i < C.n
    · exact hrels _ ⟨r, (hR r).1 hr, rfl⟩ i hi
    · exact trace_large hperm _ (not_lt.1 hi))
  have hψf : ∀ i < C.n, (MulOpposite.unop (ψ (C.f R i))) 0 = i := by
    intro i hi
    rw [show ψ (C.f R i) = FreeGroup.lift (permGen hperm) (FreeGroup.mk (C.rep i)) from rfl,
      lift_mk_apply]
    exact hreps i hi
  -- f restricted to Fin n is a bijection
  let F : Fin C.n → PresentedGroup R := fun i => C.f R i
  have hinj : Function.Injective F := by
    intro i j hij
    have := congrArg (fun g => (MulOpposite.unop (ψ g)) 0) hij
    simp only [F, hψf i i.2, hψf j j.2] at this
    exact Fin.ext this
  have hsurj : Function.Surjective F := by
    intro g
    have key : ∀ z : FreeGroup LGen, ∀ i < C.n, ∃ j < C.n,
        C.f R i * PresentedGroup.mk R z = C.f R j := by
      intro z
      induction z using FreeGroup.induction_on with
      | one => exact fun i hi => ⟨i, hi, by simp⟩
      | of x =>
        intro i hi
        exact ⟨C.ac x i, ((permOK_spec hperm x).2.2 i hi).1, hall i hi x⟩
      | inv_of x _ =>
        intro i hi
        refine ⟨C.aci x i, ((permOK_spec hperm x).2.2 i hi).2.1, ?_⟩
        have hv := hall _ ((permOK_spec hperm x).2.2 i hi).2.1 x
        unfold Valid at hv
        rw [ac_aci hperm] at hv
        rw [map_inv, ← hv, show PresentedGroup.mk R (FreeGroup.of x) = PresentedGroup.of x from rfl,
          mul_inv_cancel_right]
      | mul z₁ z₂ h₁ h₂ =>
        intro i hi
        obtain ⟨j, hj, e₁⟩ := h₁ i hi
        obtain ⟨k, hk, e₂⟩ := h₂ j hj
        exact ⟨k, hk, by rw [map_mul, ← mul_assoc, e₁, e₂]⟩
    induction g using PresentedGroup.induction_on with
    | H z =>
      obtain ⟨j, hj, e⟩ := key z 0 hn
      have hf0 : C.f R 0 = 1 := by
        unfold f
        rw [hrep0]
        rfl
      rw [hf0, one_mul] at e
      exact ⟨⟨j, hj⟩, e.symm⟩
  rw [← Nat.card_eq_of_bijective F ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card, Fintype.card_fin]

end CosetCert

end NormalizerLean
