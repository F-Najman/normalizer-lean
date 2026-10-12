import NormalizerLean.Global

/-!
# T7: the direct-product criterion

With Φ : G → B(N) the global presentation map, B_p = ⟨Φ(w_p), Φ(s_p)⟩, and for p ≠ q
Φ(w_p) Φ(w_q) = Φ(w_q) Φ(w_p), Φ(s_p) Φ(s_q) = Φ(s_q) Φ(s_p), Φ(w_p) Φ(s_q) Φ(w_p)⁻¹ = Φ(s_q)^{m_p},
and Φ(s_q) has order exactly h(m_q) (S_k^j ∈ Γ₀(N) iff k ∣ j).

* (⇒) In a direct product B_p and B_q commute, so Φ(s_q)^{m_p − 1} = 1, i.e. h(m_q) ∣ m_p − 1.
* (⇐) Then all generators of B_p and B_q commute; `Subgroup.noncommPiCoprod` gives
  ∏_p B_p → B(N), onto by T4, and |∏_p B_p| = ∏_p |B(m_p)| = |B(N)| by T6 and T3.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem commute_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, Commute x y := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (h1 hb)) a ha).symm
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hx)) y hy).symm

theorem S_pow_mem_dvd {N k j : ℕ} (hk : k ≠ 0) (h : S k ^ j ∈ Gamma0R N) : k ∣ j := by
  obtain ⟨b, hb⟩ := upperRight_of_mem h
  have hb' : (j : ℝ) * (k : ℝ)⁻¹ = b := by
    rw [coe_S_pow] at hb
    simpa using hb
  have hkr : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hjr : (j : ℝ) = b * k := by
    rw [← hb']
    field_simp
  have hjz : (j : ℤ) = b * k := by exact_mod_cast hjr
  exact Int.natCast_dvd_natCast.1 ⟨b, by rw [hjz]; ring⟩

variable (N : ℕ) [NeZero N]

theorem Bloc_eq_closure (p : N.primeFactors) :
    Bloc N p = Subgroup.closure {PhiG N (gen N p .w), PhiG N (gen N p .s)} := by
  apply le_antisymm
  · rw [Bloc, Subgroup.closure_le]
    rintro x (hAL | hS)
    · obtain ⟨hmem, rfl⟩ := hAL.2 _ (wgC_spec N p)
      exact Subgroup.subset_closure (Or.inl (PhiG_w N p).symm)
    · obtain ⟨hmem, rfl⟩ := hS
      exact Subgroup.subset_closure (Or.inr (PhiG_s N p).symm)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, PhiG_w]
      exact Subgroup.subset_closure (Or.inl (isALClass_mk (mPart_dvd N p) (wgC_spec N p)))
    · rw [SetLike.mem_coe, PhiG_s]
      exact Subgroup.subset_closure (Or.inr (B.isClassOf_mk _))

theorem B_w_comm {p q : N.primeFactors} (hpq : p ≠ q) :
    Commute (PhiG N (gen N p .w)) (PhiG N (gen N q .w)) := by
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, gen_w_comm N hpq]

theorem B_s_comm {p q : N.primeFactors} (hpq : p ≠ q) :
    Commute (PhiG N (gen N p .s)) (PhiG N (gen N q .s)) := by
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, gen_s_comm N hpq]

theorem B_ws_conj {p q : N.primeFactors} (hpq : p ≠ q) :
    PhiG N (gen N p .w) * PhiG N (gen N q .s) * (PhiG N (gen N p .w))⁻¹ =
      PhiG N (gen N q .s) ^ mPart N p := by
  rw [← map_inv, ← map_mul, ← map_mul, gen_w_s_conj N hpq, map_pow]

theorem B_s_pow (q : N.primeFactors) : PhiG N (gen N q .s) ^ hPart (mPart N q) = 1 := by
  rw [← map_pow, gen_s_pow, map_one]

theorem dvd_of_B_s_pow (q : N.primeFactors) {j : ℕ} (h : PhiG N (gen N q .s) ^ j = 1) :
    hPart (mPart N q) ∣ j := by
  rw [PhiG_s, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow] at h
  exact S_pow_mem_dvd (hPart_pos _).ne' h

theorem commute_ws_iff {p q : N.primeFactors} (hpq : p ≠ q) :
    Commute (PhiG N (gen N p .w)) (PhiG N (gen N q .s)) ↔
      mPart N p ≡ 1 [MOD hPart (mPart N q)] := by
  have hm1 : 1 ≤ mPart N p := Nat.one_le_iff_ne_zero.2 (mPart_ne_zero
    (Nat.prime_of_mem_primeFactors p.2))
  have hconj := B_ws_conj N hpq
  set x := PhiG N (gen N p .w)
  set y := PhiG N (gen N q .s)
  constructor
  · intro hc
    have h1 : y ^ mPart N p = y := by
      rw [← hconj, hc.eq, mul_inv_cancel_right]
    have h2 : y ^ (mPart N p - 1) = 1 := by
      have : y ^ (mPart N p - 1) * y = 1 * y := by
        rw [← pow_succ, Nat.sub_add_cancel hm1, h1, one_mul]
      exact mul_right_cancel this
    exact ((Nat.modEq_iff_dvd' hm1).2 (dvd_of_B_s_pow N q h2)).symm
  · intro hmod
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hm1).1 hmod.symm
    have h1 : y ^ mPart N p = y := by
      rw [show mPart N p = hPart (mPart N q) * k + 1 by omega, pow_succ, pow_mul, B_s_pow,
        one_pow, one_mul]
    change x * y = y * x
    rw [← mul_inv_eq_iff_eq_mul, hconj, h1]

/-- **T7.** -/
theorem internalDirectProduct_iff' :
    (∃ φ : ((p : N.primeFactors) → Bloc N p) ≃* B N,
        ∀ (p : N.primeFactors) (x : Bloc N p), φ (Pi.mulSingle p x) = x) ↔
      ∀ p ∈ N.primeFactors, ∀ q ∈ N.primeFactors, p ≠ q →
        mPart N p ≡ 1 [MOD hPart (mPart N q)] := by
  constructor
  · rintro ⟨φ, hφ⟩ p hp q hq hpq
    have hpq' : (⟨p, hp⟩ : N.primeFactors) ≠ ⟨q, hq⟩ := fun h => hpq (congrArg Subtype.val h)
    have hx : PhiG N (gen N ⟨p, hp⟩ .w) ∈ Bloc N p := by
      show _ ∈ Bloc N ((⟨p, hp⟩ : N.primeFactors) : ℕ)
      rw [Bloc_eq_closure]
      exact Subgroup.subset_closure (Or.inl rfl)
    have hy : PhiG N (gen N ⟨q, hq⟩ .s) ∈ Bloc N q := by
      show _ ∈ Bloc N ((⟨q, hq⟩ : N.primeFactors) : ℕ)
      rw [Bloc_eq_closure]
      exact Subgroup.subset_closure (Or.inr rfl)
    have hc := (Pi.mulSingle_commute (f := fun p : N.primeFactors => Bloc N p) hpq'
      (⟨_, hx⟩ : Bloc N p) (⟨_, hy⟩ : Bloc N q)).map φ
    rw [hφ, hφ] at hc
    exact (commute_ws_iff N hpq').1 hc
  · intro hcong
    have hgen : ∀ p q : N.primeFactors, p ≠ q →
        ∀ a ∈ ({PhiG N (gen N p .w), PhiG N (gen N p .s)} : Set (B N)),
        ∀ b ∈ ({PhiG N (gen N q .w), PhiG N (gen N q .s)} : Set (B N)), Commute a b := by
      intro p q hpq a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact B_w_comm N hpq
      · exact (commute_ws_iff N hpq).2 (hcong p p.2 q q.2 (fun h => hpq (Subtype.ext h)))
      · exact ((commute_ws_iff N hpq.symm).2
          (hcong q q.2 p p.2 (fun h => hpq (Subtype.ext h.symm)))).symm
      · exact B_s_comm N hpq
    have hcomm : Pairwise fun p q : N.primeFactors =>
        ∀ x y : B N, x ∈ Bloc N p → y ∈ Bloc N q → Commute x y := by
      intro p q hpq x y hx hy
      rw [Bloc_eq_closure] at hx hy
      exact commute_closure (hgen p q hpq) x hx y hy
    have := finite_B' N
    have hsurj : Function.Surjective (Subgroup.noncommPiCoprod hcomm) := by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range, eq_top_iff,
        ← closure_localGens' N, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨q, hq, hx⟩ := hx
      exact (le_iSup (fun p : N.primeFactors => Bloc N p) ⟨q, hq⟩)
        (Subgroup.subset_closure hx)
    have hcard : Nat.card ((p : N.primeFactors) → Bloc N p) = Nat.card (B N) := by
      rw [Nat.card_pi, ← prod_card_B_mPart N]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      obtain ⟨φp, -⟩ := localEmbedding' N p p.2
      exact Nat.card_congr φp.toEquiv
    have hbij := hsurj.bijective_of_nat_card_le hcard.le
    refine ⟨MulEquiv.ofBijective _ hbij, fun p x => ?_⟩
    rw [MulEquiv.ofBijective_apply]
    exact Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) p x

end

end NormalizerLean
