module

public import NormalizerDelta.HellingComm
public import NormalizerDelta.Gamma1Basic
public import NormalizerLean.Statements

@[expose] public section

/-!
# Part 9: proofs of the statements

* `rep_bounds`: d_p of the representatives of a group K with K ∩ SL₂(ℤ) of finite index in K depends only on the
  coset modulo SL₂(ℤ), hence is bounded, and is 0 for almost all p.
* `helling'`: the core theorem for S_p = the representatives of G.
* `gamma0Plus_maximal'`: if Γ₀(N)⁺ ≤ H, the centre of H at p is fixed by [[1, 1], [0, 1]] and [[1, 0], [N, 1]], so it
  lies in {1} (p ∤ N) or {1, diag(1, N)} (p ∣ N); w_p (det p) fixes no vertex at p ∣ N.  So H fixes 1 at p ∤ N and
  preserves {1, diag(1, N)} at p ∣ N, and H ≤ Γ₀(N)⁺.
* `normG_conj_le_gamma0Plus'`: the core theorem for Nor(Γ) with S_p = the vertices fixed by Γ⁰ = {γ ∈ Γ whose
  representative has square determinant}, which is normal in Nor(Γ).
-/

open Matrix MatrixGroups Pointwise

namespace NormalizerLean.Helling

theorem isRep_one : IsRep 1 (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨by simp, 1, by simp⟩

/-- The representatives of a group K, with K ∩ SL₂(ℤ) of finite index in K, have bounded d_p, and d_p = 0 for
almost all p. -/
theorem rep_bounds {K : Subgroup SL(2, ℝ)} (hK : SL2ZR.relIndex K ≠ 0) (hrep : ∀ g ∈ K, ∃ R, IsRep g R) :
    (∀ p, (hp : p.Prime) → ∃ B, ∀ g ∈ K, ∀ R, IsRep g R → @dist p R ≤ B) ∧
    ∃ P : Finset ℕ, ∀ p, (hp : p.Prime) → p ∉ P → ∀ g ∈ K, ∀ R, IsRep g R → @dist p R = 0 := by
  classical
  have : (SL2ZR.subgroupOf K).FiniteIndex := ⟨hK⟩
  have hfin : Finite (K ⧸ SL2ZR.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (K ⧸ SL2ZR.subgroupOf K)
  choose Rq hRq using fun q : K ⧸ SL2ZR.subgroupOf K => hrep _ (q.out).2
  have key : ∀ p, p.Prime → ∀ g (hg : g ∈ K) R, IsRep g R →
      @dist p R = @dist p (Rq (QuotientGroup.mk ⟨g, hg⟩)) := by
    intro p hp g hg R hR
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (SL2ZR.subgroupOf K) ⟨g, hg⟩
    have hh' : (((QuotientGroup.mk ⟨g, hg⟩ : K ⧸ SL2ZR.subgroupOf K).out : K) : SL(2, ℝ)) =
        g * ((h : K) : SL(2, ℝ)) := by
      rw [hh]; rfl
    obtain ⟨γ, hγ⟩ := mem_SL2ZR_iff.1 (Subgroup.mem_subgroupOf.1 h.2)
    have hrep2 : IsRep (((QuotientGroup.mk ⟨g, hg⟩ : K ⧸ SL2ZR.subgroupOf K).out : K) : SL(2, ℝ))
        (R * γ) := by
      rw [hh', ← hγ]; exact hR.mul (isRep_ofZ γ)
    obtain ⟨a, b, ha, hb, hab⟩ := (hRq (QuotientGroup.mk ⟨g, hg⟩)).prop hrep2
    have hγ1 : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
    rw [← dist_smul ha (hRq _).1, hab, dist_smul hb (det_mul_ne_zero hR.1 (by rw [hγ1]; exact one_ne_zero)),
      dist_mul_unit (not_dvd_det_of_det_eq_one hγ1) hR.1]
  constructor
  · intro p hp
    refine ⟨Finset.univ.sup fun q => @dist p (Rq q), fun g hg R hR => ?_⟩
    rw [key p hp g hg R hR]
    exact Finset.le_sup (f := fun q => @dist p (Rq q)) (Finset.mem_univ _)
  · refine ⟨Finset.univ.biUnion fun q => (Rq q).det.natAbs.primeFactors, fun p hp hpP g hg R hR => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    rw [key p hp g hg R hR]
    apply dist_eq_zero_of_not_dvd
    intro hdvd
    apply hpP
    rw [Finset.mem_biUnion]
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, Finset.mem_univ _, Nat.mem_primeFactors.2
      ⟨hp, Int.natCast_dvd.1 hdvd, Int.natAbs_ne_zero.2 (hRq _).1⟩⟩

theorem relIndex_ne_zero_of_commensurable {G : Subgroup SL(2, ℝ)} (hG : G.Commensurable SL2ZR) :
    G.relIndex SL2ZR ≠ 0 ∧ SL2ZR.relIndex G ≠ 0 :=
  ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.1 hG.1,
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.1 hG.2⟩

theorem exists_isRep_of_commensurable {G : Subgroup SL(2, ℝ)} (hG : G.Commensurable SL2ZR) :
    ∀ g ∈ G, ∃ R, IsRep g R := fun g hg =>
  exists_isRep_of_normalizes (relIndex_ne_zero_of_commensurable hG).1
    (relIndex_ne_zero_of_commensurable hG).2 fun x hx => G.mul_mem (G.mul_mem hg hx) (G.inv_mem hg)

theorem presE_symm {p : ℕ} {z z' R : Matrix (Fin 2) (Fin 2) ℤ} (h : PresE p z z' R) : PresE p z' z R := by
  unfold PresE at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

theorem conj_commensurable {H : Subgroup SL(2, ℝ)} (hH : H.Commensurable SL2ZR) {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : 0 < A.det) :
    (H.map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))).toMonoidHom).Commensurable SL2ZR :=
  (hH.map _).trans (commensurable_conj_SL2ZR hA)

theorem conj_inv_commensurable {H : Subgroup SL(2, ℝ)} (hH : H.Commensurable SL2ZR)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) :
    (H.map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))⁻¹).toMonoidHom).Commensurable SL2ZR := by
  rw [← projSL_adjugate hA]
  exact conj_commensurable hH (by rwa [det_adjugate'])

theorem map_conj_inv_map_conj (g : SL(2, ℝ)) (H : Subgroup SL(2, ℝ)) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_map_conj_inv (g : SL(2, ℝ)) (H : Subgroup SL(2, ℝ)) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  have := map_conj_inv_map_conj g⁻¹ H
  rwa [inv_inv] at this

end NormalizerLean.Helling

namespace NormalizerLean

open Helling

noncomputable section

/-! ## §H -/

theorem helling' {G : Subgroup SL(2, ℝ)} (hG : G.Commensurable SL2ZR) :
    ∃ (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ), Squarefree N ∧ 0 < A.det ∧
      G.map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))).toMonoidHom ≤ Gamma0Plus N := by
  have hrep := exists_isRep_of_commensurable hG
  obtain ⟨hB, P, hP⟩ := rep_bounds (relIndex_ne_zero_of_commensurable hG).2 hrep
  apply core hrep (fun _ => {R | ∃ g ∈ G, IsRep g R})
  · rintro p s ⟨g, -, hs⟩; exact hs.1
  · intro p _; exact ⟨1, 1, G.one_mem, isRep_one⟩
  · intro p hp
    obtain ⟨B, hB⟩ := hB p hp
    exact ⟨B, fun s ⟨g, hg, hs⟩ => hB g hg s hs⟩
  · rintro p _ g hg R hR s ⟨h, hh, hs⟩
    exact ⟨g * h, G.mul_mem hg hh, hR.mul hs⟩
  · exact ⟨P, fun p hp hpP s ⟨g, hg, hs⟩ => hP p hp hpP g hg s hs⟩

theorem gamma0R_le_gamma0Plus (N : ℕ) [NeZero N] : Gamma0R N ≤ Gamma0Plus N := fun g hg =>
  Subgroup.subset_closure ⟨1, one_dvd N, (isAtkinLehner_one_iff' N g).2 hg⟩

theorem gamma0Plus_le_norm0 (N : ℕ) [NeZero N] : Gamma0Plus N ≤ Norm0 N :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hQ, hg⟩ => isAtkinLehner_mem_normalizer hQ hg

theorem gamma0R_le_SL2ZR (N : ℕ) : Gamma0R N ≤ SL2ZR :=
  Subgroup.map_mono le_top

theorem relIndex_gamma0R_SL2ZR (N : ℕ) [NeZero N] : (Gamma0R N).relIndex SL2ZR ≠ 0 := by
  rw [show Gamma0R N = toR (CongruenceSubgroup.Gamma0 N) from rfl, SL2ZR, relIndex_toR,
    Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero

theorem relIndex_gamma0R_norm0 (N : ℕ) [NeZero N] : (Gamma0R N).relIndex (Norm0 N) ≠ 0 := by
  have := finite_B N
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_gamma0R_gamma0Plus (N : ℕ) [NeZero N] : (Gamma0R N).relIndex (Gamma0Plus N) ≠ 0 :=
  fun h0 => relIndex_gamma0R_norm0 N (Subgroup.relIndex_eq_zero_of_le_right (gamma0Plus_le_norm0 N) h0)

theorem commensurable_of_le {K L : Subgroup SL(2, ℝ)} (N : ℕ) [NeZero N] (hK : Gamma0R N ≤ K)
    (hKL : K ≤ L) (hL : (Gamma0R N).relIndex L ≠ 0) : K.Commensurable SL2ZR := by
  constructor
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    intro h
    have := Subgroup.relIndex_dvd_of_le_left SL2ZR hK
    rw [h] at this
    exact relIndex_gamma0R_SL2ZR N (Nat.eq_zero_of_zero_dvd this)
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    intro h
    have := Subgroup.relIndex_dvd_of_le_left K (gamma0R_le_SL2ZR N)
    rw [h] at this
    exact hL (Subgroup.relIndex_eq_zero_of_le_right hKL (Nat.eq_zero_of_zero_dvd this))

theorem commensurable_gamma0Plus' (N : ℕ) [NeZero N] : (Gamma0Plus N).Commensurable SL2ZR :=
  commensurable_of_le N (gamma0R_le_gamma0Plus N) le_rfl (relIndex_gamma0R_gamma0Plus N)

theorem commensurable_norm0 (N : ℕ) [NeZero N] : (Norm0 N).Commensurable SL2ZR :=
  commensurable_of_le N Subgroup.le_normalizer le_rfl (relIndex_gamma0R_norm0 N)

theorem ofZ_upZ_one_mem_gamma0Plus (N : ℕ) [NeZero N] : ofZ (upZ 1) ∈ Gamma0Plus N :=
  gamma0R_le_gamma0Plus N ⟨upZ 1, CongruenceSubgroup.Gamma0_mem.2 (by simp [upM]), rfl⟩

theorem ofZ_loZ_mem_gamma0Plus (N : ℕ) [NeZero N] : ofZ (loZ N) ∈ Gamma0Plus N :=
  gamma0R_le_gamma0Plus N ⟨loZ N, CongruenceSubgroup.Gamma0_mem.2 (by simp [loM]), rfl⟩

/-- An Atkin–Lehner element w_p has a representative of determinant p. -/
theorem exists_rep_of_isAtkinLehner {N Q : ℕ} (hQ : 0 < Q) {g : SL(2, ℝ)} (hg : IsAtkinLehner N Q g) :
    ∃ R, IsRep g R ∧ R.det = Q := by
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  refine ⟨!![(Q : ℤ) * x, y; N * z, Q * w], ⟨?_, (Real.sqrt Q)⁻¹, ?_⟩, ?_⟩
  · rw [det_fin_two_of]
    have : (Q : ℤ) * x * (Q * w) - y * (N * z) = Q := by linear_combination hdet
    rw [this]; exact_mod_cast hQ.ne'
  · rw [hgm]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [det_fin_two_of]; linear_combination hdet

/-- The local analysis of `gamma0Plus_maximal`. -/
theorem gamma0Plus_maximal_local {N : ℕ} (hN : Squarefree N) {H : Subgroup SL(2, ℝ)}
    (hH : H.Commensurable SL2ZR) (hle : Gamma0Plus N ≤ H) {p : ℕ} (hp : p.Prime) :
    (¬ p ∣ N → ∀ g ∈ H, ∀ R, IsRep g R → @dd p 1 (R * 1) = 0) ∧
      (p ∣ N → ∀ g ∈ H, ∀ R, IsRep g R → PresE p 1 (diagN N) R) := by
  have : NeZero N := ⟨hN.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hrep := exists_isRep_of_commensurable hH
  obtain ⟨hB, -⟩ := rep_bounds (relIndex_ne_zero_of_commensurable hH).2 hrep
  obtain ⟨B, hB⟩ := hB p hp
  set S : Set (Matrix (Fin 2) (Fin 2) ℤ) := {R | ∃ g ∈ H, IsRep g R} with hSdef
  have hSdet : ∀ s ∈ S, s.det ≠ 0 := fun s ⟨_, _, hs⟩ => hs.1
  have hSne : S.Nonempty := ⟨1, 1, H.one_mem, isRep_one⟩
  have hSB : ∀ s ∈ S, dist p s ≤ B := fun s ⟨g, hg, hs⟩ => hB g hg s hs
  have hS𝓡 : ∀ R ∈ S, R.det ≠ 0 ∧ (∀ s ∈ S, R * s ∈ S) ∧ (∀ s ∈ S, R.adjugate * s ∈ S) := by
    rintro R ⟨g, hg, hR⟩
    exact ⟨hR.1, fun s ⟨h, hh, hs⟩ => ⟨g * h, H.mul_mem hg hh, hR.mul hs⟩,
      fun s ⟨h, hh, hs⟩ => ⟨g⁻¹ * h, H.mul_mem (H.inv_mem hg) hh, hR.inv.mul hs⟩⟩
  have hT : upM 1 ∈ S := ⟨ofZ (upZ 1), hle (ofZ_upZ_one_mem_gamma0Plus N), isRep_ofZ (upZ 1)⟩
  have hL : loM N ∈ S := ⟨ofZ (loZ N), hle (ofZ_loZ_mem_gamma0Plus N), isRep_ofZ (loZ N)⟩
  have hvdT : vd p (upM 1) % 2 = 0 := by simp [vd, det_upT]
  have hvdL : vd p (loM N) % 2 = 0 := by simp [vd, det_loT]
  have hT0 : (upM 1).det ≠ 0 := by rw [det_upT]; exact one_ne_zero
  have hL0 : (loM N).det ≠ 0 := by rw [det_loT]; exact one_ne_zero
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by simp
  have hD0 : (diagN N).det ≠ 0 := by rw [det_diagN]; exact_mod_cast hN.ne_zero
  -- vertices fixed by T and L
  have hfixTL : ∀ z, z.det ≠ 0 → dd p z (upM 1 * z) = 0 → dd p z (loM N * z) = 0 →
      dd p 1 z = 0 ∨ (p ∣ N ∧ dd p (diagN N) z = 0) := fun z hz h1 h2 => dd_eq_zero_of_fix hN hz h1 h2
  -- w_p for p ∣ N
  have hW : p ∣ N → ∃ RW ∈ S, vd p RW = 1 := by
    intro hpN
    have hcop : Nat.Coprime p (N / p) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have : p * p ∣ N := by
        rw [← Nat.mul_div_cancel' hpN]; exact Nat.mul_dvd_mul_left p h
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hN p this))
    obtain ⟨W, hW⟩ := exists_isAtkinLehner hpN hcop
    obtain ⟨RW, hRW, hdet⟩ := exists_rep_of_isAtkinLehner hp.pos hW
    refine ⟨RW, ⟨W, hle (Subgroup.subset_closure ⟨p, hpN, hW⟩), hRW⟩, ?_⟩
    rw [vd, hdet, padicValInt.self hp.one_lt]
  rcases center_conclusion hSdet hSne hSB S hS𝓡 with ⟨z, hz, hfix⟩ | ⟨z, z', hz, hz', hzz', hpres⟩
  · -- a fixed vertex
    have hpN : ¬ p ∣ N := by
      intro hpN
      obtain ⟨RW, hRW, hvd⟩ := hW hpN
      have h1 := dd_mod_two (p := p) hz (det_mul_ne_zero (hS𝓡 RW hRW).1 hz)
      rw [hfix RW hRW, vd_mul (hS𝓡 RW hRW).1 hz, hvd] at h1
      omega
    have h1z : dd p 1 z = 0 := by
      rcases hfixTL z hz (hfix _ hT) (hfix _ hL) with h | h
      · exact h
      · exact absurd h.1 hpN
    refine ⟨fun _ g hg R hR => ?_, fun h => absurd h hpN⟩
    rw [dd_mul_congr h10 hz h10 hz hR.1 h1z h1z]
    exact hfix R ⟨g, hg, hR⟩
  · -- a preserved edge
    have fz := presE_fix_of_even hz hz' hT0 hzz' (hpres _ hT) hvdT
    have fz' := presE_fix_of_even hz hz' hL0 hzz' (hpres _ hL) hvdL
    have c := hfixTL z hz fz.1 fz'.1
    have c' := hfixTL z' hz' fz.2 fz'.2
    have tri : ∀ {a b : Matrix (Fin 2) (Fin 2) ℤ}, a.det ≠ 0 → b.det ≠ 0 → dd p a z = 0 → dd p a z' = 0 →
        False := fun ha hb h1 h2 => by
      have := dd_triangle (p := p) hz ha hz'
      rw [dd_comm hz ha, h1, h2, hzz'] at this
      omega
    rcases c with c | ⟨hpN, c⟩ <;> rcases c' with c' | ⟨hpN', c'⟩
    · exact (tri h10 h10 c c').elim
    · refine ⟨fun h => absurd hpN' h, fun _ g hg R hR => ?_⟩
      have e1 : dd p z 1 = 0 := by rw [dd_comm hz h10]; exact c
      have e2 : dd p z' (diagN N) = 0 := by rw [dd_comm hz' hD0]; exact c'
      have hP : PresE p z z' R := hpres R ⟨g, hg, hR⟩
      exact presE_congr hz h10 hz' hD0 hR.1 e1 e2 hP
    · refine ⟨fun h => absurd hpN h, fun _ g hg R hR => ?_⟩
      have e1 : dd p z' 1 = 0 := by rw [dd_comm hz' h10]; exact c'
      have e2 : dd p z (diagN N) = 0 := by rw [dd_comm hz hD0]; exact c
      have hP : PresE p z' z R := presE_symm (hpres R ⟨g, hg, hR⟩)
      exact presE_congr hz' h10 hz hD0 hR.1 e1 e2 hP
    · exact (tri hD0 hD0 c c').elim

theorem gamma0Plus_maximal' {N : ℕ} (hN : Squarefree N) {H : Subgroup SL(2, ℝ)}
    (hH : H.Commensurable SL2ZR) (hle : Gamma0Plus N ≤ H) : H = Gamma0Plus N := by
  refine le_antisymm (fun g hg => ?_) hle
  obtain ⟨R, hR⟩ := exists_isRep_of_commensurable hH g hg
  exact mem_gamma0Plus_of_local hN hR
    (fun p hp hpN => (gamma0Plus_maximal_local hN hH hle hp).1 hpN g hg R hR)
    (fun p hp hpN => (gamma0Plus_maximal_local hN hH hle hp).2 hpN g hg R hR)

theorem maximal_commensurable_iff' {H : Subgroup SL(2, ℝ)} :
    Maximal (fun K : Subgroup SL(2, ℝ) => K.Commensurable SL2ZR) H ↔
      H.Commensurable SL2ZR ∧ ∃ (N : ℕ) (g : SL(2, ℝ)), Squarefree N ∧
        H = (Gamma0Plus N).map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hmax
    refine ⟨hmax.1, ?_⟩
    obtain ⟨N, A, hN, hA, hle⟩ := helling' hmax.1
    have : NeZero N := ⟨hN.ne_zero⟩
    set g := projSL (A.map (Int.cast : ℤ → ℝ))
    refine ⟨N, g⁻¹, hN, ?_⟩
    have hK := conj_inv_commensurable (commensurable_gamma0Plus' N) hA
    have hHK : H ≤ (Gamma0Plus N).map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      exact ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact le_antisymm hHK (hmax.2 hK hHK)
  · rintro ⟨hH, N, g, hN, rfl⟩
    have : NeZero N := ⟨hN.ne_zero⟩
    refine ⟨hH, fun K hK hle => ?_⟩
    have hK' : (K.map (MulAut.conj g⁻¹).toMonoidHom).Commensurable SL2ZR := by
      have h1 : (K.map (MulAut.conj g⁻¹).toMonoidHom).Commensurable
          (((Gamma0Plus N).map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom) :=
        (hK.trans hH.symm).map _
      rw [map_conj_inv_map_conj] at h1
      exact h1.trans (commensurable_gamma0Plus' N)
    have hle' : Gamma0Plus N ≤ K.map (MulAut.conj g⁻¹).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
      rwa [map_conj_inv_map_conj] at this
    have := gamma0Plus_maximal' hN hK' hle'
    rw [← this, map_conj_map_conj_inv]

theorem mem_commensurator_SL2ZR_iff' {g : SL(2, ℝ)} :
    g ∈ Subgroup.Commensurable.commensurator SL2ZR ↔
      ∃ A : Matrix (Fin 2) (Fin 2) ℤ, 0 < A.det ∧ g = projSL (A.map (Int.cast : ℤ → ℝ)) := by
  have hsmul : MulAut.conj g • SL2ZR = SL2ZR.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    rfl
  rw [Subgroup.Commensurable.commensurator_mem_iff, hsmul]
  constructor
  · intro hc
    have h2 : SL2ZR.relIndex (SL2ZR.map (MulAut.conj g).toMonoidHom) ≠ 0 :=
      Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.1 hc.2
    have hmem : ∀ γ : SL(2, ℤ), g * ofZ γ * g⁻¹ ∈ SL2ZR.map (MulAut.conj g).toMonoidHom :=
      fun γ => ⟨ofZ γ, ofZ_mem_SL2ZR γ, by simp [MulAut.conj_apply]⟩
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem h2 (hmem (upZ 1))
    obtain ⟨n, hn, hn'⟩ := exists_pow_mem h2 (hmem (loZ 1))
    obtain ⟨R, hR⟩ : ∃ R, IsRep g R := by
      apply exists_isRep_of_conj (k := m * n) (Nat.mul_pos hm hn)
      · have := SL2ZR.pow_mem hm' n
        rw [← pow_mul, conj_pow, ← map_pow, upZ_pow, mul_one] at this
        exact this
      · have := SL2ZR.pow_mem hn' m
        rw [← pow_mul, conj_pow, ← map_pow, loZ_pow, mul_one, mul_comm] at this
        exact this
    obtain ⟨c, hc2, hcg⟩ := hR.sq_mul_det
    have hD := hR.det_pos
    have hDr : (0 : ℝ) < R.det := by exact_mod_cast hD
    have hs : ((Real.sqrt R.det)⁻¹) ^ 2 = 1 / (R.det : ℝ) := by
      rw [inv_pow, Real.sq_sqrt hDr.le, one_div]
    have hc' : c ^ 2 = ((Real.sqrt R.det)⁻¹) ^ 2 := by
      rw [hs, eq_div_iff hDr.ne']; exact hc2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hc' with h | h
    · refine ⟨R, hD, Subtype.ext ?_⟩
      rw [hcg, coe_projSL_int hD, h]
    · have hD' : 0 < (-R).det := by simpa [det_neg] using hD
      refine ⟨-R, hD', Subtype.ext ?_⟩
      rw [hcg, coe_projSL_int hD', h, show (-R).det = R.det by simp [det_neg]]
      ext i j
      simp
  · rintro ⟨A, hA, rfl⟩
    exact commensurable_conj_SL2ZR hA

/-! ## §N -/

/-- Γ⁰: the elements of Γ with a representative of square determinant. -/
def gammaSq (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) where
  carrier := {γ | γ ∈ Γ ∧ ∃ Q, IsRep γ Q ∧ IsSquare Q.det}
  one_mem' := ⟨Γ.one_mem, 1, isRep_one, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, Q, hQ, hQs⟩ ⟨hb, Q', hQ', hQ's⟩
    exact ⟨Γ.mul_mem ha hb, Q * Q', hQ.mul hQ', by rw [det_mul]; exact hQs.mul hQ's⟩
  inv_mem' := by
    rintro a ⟨ha, Q, hQ, hQs⟩
    exact ⟨Γ.inv_mem ha, Q.adjugate, hQ.inv, by rwa [det_adjugate']⟩

theorem vd_even_of_mem_gammaSq {Γ : Subgroup SL(2, ℝ)} {γ : SL(2, ℝ)} (hγ : γ ∈ gammaSq Γ) {R}
    (hR : IsRep γ R) (p : ℕ) [Fact p.Prime] : vd p R % 2 = 0 := by
  obtain ⟨-, Q, hQ, m, hm⟩ := hγ
  obtain ⟨a, b, ha, hb, hab⟩ := hR.prop hQ
  have e := congrArg Matrix.det hab
  rw [det_smul, det_smul, Fintype.card_fin, hm] at e
  have hm0 : m ≠ 0 := by
    rintro rfl; apply hQ.1; rw [hm]; ring
  have h := congrArg (padicValInt p) e
  rw [padicValInt.mul (pow_ne_zero _ ha) hR.1, padicValInt.mul (pow_ne_zero _ hb) (mul_ne_zero hm0 hm0),
    padicValInt.mul hm0 hm0, pow_two, pow_two, padicValInt.mul ha ha, padicValInt.mul hb hb] at h
  rw [vd]
  omega

theorem normG_conj_le_gamma0Plus' {Γ : Subgroup SL(2, ℝ)} (hΓ : Γ.Commensurable SL2ZR) :
    ∃ (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ), Squarefree N ∧ 0 < A.det ∧
      (NormG Γ).map (MulAut.conj (projSL (A.map (Int.cast : ℤ → ℝ)))).toMonoidHom ≤ Gamma0Plus N := by
  obtain ⟨h1, h2⟩ := relIndex_ne_zero_of_commensurable hΓ
  have hrep : ∀ n ∈ NormG Γ, ∃ R, IsRep n R := fun n hn =>
    exists_isRep_of_normalizes h1 h2 fun x hx => (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  set Γ₀ := gammaSq Γ
  have hΓ₀ : Γ₀ ≤ Γ := fun _ h => h.1
  have hΓ₀2 : SL2ZR.relIndex Γ₀ ≠ 0 := fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right hΓ₀ h0)
  have hrep₀ : ∀ γ ∈ Γ₀, ∃ R, IsRep γ R := fun γ hγ => ⟨_, hγ.2.choose_spec.1⟩
  -- the unipotent elements of Γ₀
  obtain ⟨k, hk, hTk, hLk⟩ := exists_unipotent_pow_mem h1
  have hTk₀ : ofZ (upZ k) ∈ Γ₀ := ⟨hTk, upM k, isRep_ofZ (upZ k), by rw [det_upT]; exact ⟨1, by ring⟩⟩
  have hLk₀ : ofZ (loZ k) ∈ Γ₀ := ⟨hLk, loM k, isRep_ofZ (loZ k), by rw [det_loT]; exact ⟨1, by ring⟩⟩
  set S : ℕ → Set (Matrix (Fin 2) (Fin 2) ℤ) := fun p =>
    {z | z.det ≠ 0 ∧ ∀ γ ∈ Γ₀, ∀ Q, IsRep γ Q → @dd p z (Q * z) = 0} with hSdef
  apply core hrep S
  · intro p s hs; exact hs.1
  · -- S_p is nonempty: the centre of the orbit of Γ₀
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hB, -⟩ := rep_bounds hΓ₀2 hrep₀
    obtain ⟨B, hB⟩ := hB p hp
    set S' : Set (Matrix (Fin 2) (Fin 2) ℤ) := {R | ∃ γ ∈ Γ₀, IsRep γ R}
    have hS'det : ∀ s ∈ S', s.det ≠ 0 := fun s ⟨_, _, hs⟩ => hs.1
    have hS'𝓡 : ∀ R ∈ S', R.det ≠ 0 ∧ (∀ s ∈ S', R * s ∈ S') ∧ (∀ s ∈ S', R.adjugate * s ∈ S') := by
      rintro R ⟨g, hg, hR⟩
      exact ⟨hR.1, fun s ⟨h, hh, hs⟩ => ⟨g * h, Γ₀.mul_mem hg hh, hR.mul hs⟩,
        fun s ⟨h, hh, hs⟩ => ⟨g⁻¹ * h, Γ₀.mul_mem (Γ₀.inv_mem hg) hh, hR.inv.mul hs⟩⟩
    rcases center_conclusion hS'det ⟨1, 1, Γ₀.one_mem, isRep_one⟩ (fun s ⟨g, hg, hs⟩ => hB g hg s hs) S'
        hS'𝓡 with ⟨z, hz, hfix⟩ | ⟨z, z', hz, hz', hzz', hpres⟩
    · exact ⟨z, hz, fun γ hγ Q hQ => hfix Q ⟨γ, hγ, hQ⟩⟩
    · exact ⟨z, hz, fun γ hγ Q hQ => (presE_fix_of_even hz hz' hQ.1 hzz' (hpres Q ⟨γ, hγ, hQ⟩)
        (vd_even_of_mem_gammaSq hγ hQ p)).1⟩
  · -- bounded
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨padicValInt p k, fun z hz => ?_⟩
    exact dist_le_of_fix hz.1 (by exact_mod_cast hk.ne') (hz.2 _ hTk₀ _ (isRep_ofZ (upZ k)))
      (hz.2 _ hLk₀ _ (isRep_ofZ (loZ k)))
  · -- invariant
    intro p hp n hn R hR z hz
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨det_mul_ne_zero hR.1 hz.1, fun γ hγ Q hQ => ?_⟩
    have hn' : n⁻¹ ∈ NormG Γ := (NormG Γ).inv_mem hn
    obtain ⟨hγΓ, Q', hQ', m, hm⟩ := hγ
    have hconj : n⁻¹ * γ * n ∈ Γ₀ := by
      refine ⟨?_, R.adjugate * Q' * R, (hR.inv.mul hQ').mul hR, ⟨R.det * m, ?_⟩⟩
      · have := (Subgroup.mem_normalizer_iff.1 hn' γ).1 hγΓ
        rwa [inv_inv] at this
      · rw [det_mul, det_mul, det_adjugate', hm]; ring
    have h1 := hz.2 _ hconj _ ((hR.inv.mul hQ').mul hR)
    rw [dd_conj hR.1 hQ'.1 hz.1 hz.1] at h1
    obtain ⟨a, b, ha, hb, hab⟩ := hQ.prop hQ'
    have hRz := det_mul_ne_zero hR.1 hz.1
    rw [← dd_smul_mul ha hRz hQ.1 hRz, hab, dd_smul_mul hb hRz hQ'.1 hRz]
    exact h1
  · -- almost all zero
    refine ⟨k.primeFactors, fun p hp hpk z hz => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have := dist_le_of_fix hz.1 (by exact_mod_cast hk.ne') (hz.2 _ hTk₀ _ (isRep_ofZ (upZ k)))
      (hz.2 _ hLk₀ _ (isRep_ofZ (loZ k)))
    have hpk' : ¬ p ∣ k := fun h => hpk (Nat.mem_primeFactors.2 ⟨hp, h, hk.ne'⟩)
    rw [padicValInt, Int.natAbs_natCast, padicValNat.eq_zero_of_not_dvd hpk'] at this
    omega

theorem commensurable_normG' {Γ : Subgroup SL(2, ℝ)} (hΓ : Γ.Commensurable SL2ZR) :
    (NormG Γ).Commensurable SL2ZR := by
  obtain ⟨N, A, hN, hA, hle⟩ := normG_conj_le_gamma0Plus' hΓ
  have : NeZero N := ⟨hN.ne_zero⟩
  set g := projSL (A.map (Int.cast : ℤ → ℝ))
  have hK := conj_inv_commensurable (commensurable_gamma0Plus' N) hA
  have hNK : NormG Γ ≤ (Gamma0Plus N).map (MulAut.conj g⁻¹).toMonoidHom := fun x hx =>
    ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨h1, -⟩ := relIndex_ne_zero_of_commensurable hΓ
  obtain ⟨-, h4⟩ := relIndex_ne_zero_of_commensurable hK
  constructor
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    intro h
    have := Subgroup.relIndex_dvd_of_le_left SL2ZR (Subgroup.le_normalizer : Γ ≤ NormG Γ)
    rw [h] at this
    exact h1 (Nat.eq_zero_of_zero_dvd this)
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    exact fun h => h4 (Subgroup.relIndex_eq_zero_of_le_right hNK h)

theorem finite_BG_of_commensurable' {Γ : Subgroup SL(2, ℝ)} (hΓ : Γ.Commensurable SL2ZR) :
    Finite (BG Γ) := by
  have h := hΓ.trans (commensurable_normG' hΓ).symm
  have h' : Γ.relIndex (NormG Γ) ≠ 0 := Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.1 h.1
  have : (Γ.subgroupOf (NormG Γ)).FiniteIndex := ⟨h'⟩
  exact Subgroup.finite_quotient_of_finiteIndex

/-! ## §S -/

theorem not_maximal_gamma0Plus_four' :
    ¬ Maximal (fun K : Subgroup SL(2, ℝ) => K.Commensurable SL2ZR) (Gamma0Plus 4) := by
  intro hmax
  have hle := hmax.2 (commensurable_norm0 4) (gamma0Plus_le_norm0 4)
  have hS : S 2 ∈ Gamma0Plus 4 := hle (S_mem_normalizer (by rw [hPart_four]))
  rw [mem_Gamma0Plus] at hS
  obtain ⟨Q, -, hQ⟩ := hS
  exact not_isAtkinLehner_S2 hQ

end

end NormalizerLean
