"""Write palomar/<entry>/formalization.yaml, the Palomar metadata (formalization.yaml v0.4) of each entry.

The entries are the challenges of `make_challenge.py` except Part 4 and Part 3 §B (B₀(N)), which are not Palomar
entries. Parts 7, 8 and 9 have their own automation and review notes, and Part 9 its own scope, divergences and
acknowledgements (`OVERRIDES`). The fields are below. The `alignment` section, a plain-language account of every compared theorem, is generated from the tables in
README.md, so the two cannot drift apart; its theorem names must be exactly those of the entry's Comparator
configuration.
Run: python3 scripts/make_formalization.py            (writes the files)
     python3 scripts/make_formalization.py --check    (checks that they are up to date and valid)
"""
import copy
import json
import os
import re
import sys

import yaml

SOURCES = {
    'Ne': {'title': 'Conjugacy, genus, and class numbers', 'authors': ['Morris Newman'], 'type': 'article',
           'location': 'Math. Ann. 196 (1972), 198–217'},
    'AL': {'title': 'Hecke operators on Γ₀(m)', 'authors': ['A. O. L. Atkin', 'J. Lehner'], 'type': 'article',
           'location': 'Math. Ann. 185 (1970), 134–160'},
    'AS': {'title': 'The normalizer of Γ₀(N) in PSL(2, ℝ)', 'authors': ['M. Akbaş', 'D. Singerman'],
           'type': 'article', 'location': 'Glasgow Math. J. 32 (1990), 317–327'},
    'Ba': {'title': 'The group structure of the normalizer of Γ₀(N) after Atkin–Lehner', 'authors': ['F. Bars'],
           'id': 'arXiv:math/0701636', 'type': 'article', 'location': 'Comm. Algebra 36 (2008), 2160–2170'},
    'KK': {'title': 'The normalizer of Γ₁(N) in PSL₂(ℝ)', 'authors': ['C. H. Kim', 'J. K. Koo'], 'type': 'article',
           'location': 'Comm. Algebra 28 (2000), 5303–5310'},
    'L': {'title': 'Normalizer of Γ₁(m)', 'authors': ['M.-L. Lang'], 'type': 'article',
          'location': 'J. Number Theory 86 (2001), 50–60'},
    'DLM22': {'title': 'Automorphisms of Cartan modular curves of prime and composite level',
              'authors': ['V. Dose', 'G. Lido', 'P. Mercuri'], 'id': 'arXiv:2005.09009v2', 'type': 'article',
              'location': 'Algebra Number Theory 16 (2022), 1423–1461'},
    'DLM26': {'title': 'Automorphisms of general modular curves', 'authors': ['V. Dose', 'G. M. Lido', 'P. Mercuri'],
              'id': 'arXiv:2610.08998v1', 'type': 'preprint', 'location': 'https://arxiv.org/abs/2610.08998v1'},
    'Ze': {'title': 'Normalizers of congruence groups in SL₂(ℝ) and automorphisms of lattices',
           'authors': ['Shaul Zemel'], 'id': 'doi:10.1142/S1793042117500701', 'type': 'article',
           'location': 'Int. J. Number Theory 13 (2017), 1275–1300; arXiv:1512.07547'},
    'Bo': {'title': 'Computing models for quotients of modular curves', 'authors': ['Josha Box'],
           'id': 'doi:10.1007/s40993-021-00276-8', 'type': 'article',
           'location': 'Res. Number Theory 7 (2021), no. 3, Paper No. 51; arXiv:2101.03797'},
    'Fe': {'title': 'A moduli approach to quadratic Q-curves realizing projective mod p Galois representations',
           'authors': ['Julio Fernández'], 'id': 'doi:10.4171/rmi/527', 'type': 'article',
           'location': 'Rev. Mat. Iberoam. 24 (2008), no. 1, 1–30; arXiv:math/0506070'},
    'ORIG8': {'title': 'Normalizers at mixed level: results first presented with this formalization',
              'type': 'original-proof'},
    'DN': {'title': 'Sporadic points on X₀(N)', 'authors': ['M. Derickx', 'F. Najman'], 'id': 'arXiv:2511.09015',
           'type': 'preprint', 'location': 'https://arxiv.org/abs/2511.09015'},
    'He': {'title': 'Bestimmung der Kommensurabilitätsklasse der Hilbertschen Modulgruppe', 'authors': ['Heinz Helling'],
           'id': 'doi:10.1007/BF01112194', 'type': 'article', 'location': 'Math. Z. 92 (1966), 269–280'},
    'Du': {'title': 'Arithmetic groups and the affine E₈ Dynkin diagram', 'authors': ['John F. Duncan'],
           'id': 'arXiv:0810.1465v2', 'type': 'article',
           'location': 'in Groups and Symmetries: From Neolithic Scots to John McKay, CRM Proc. Lecture Notes 47, '
                       'Amer. Math. Soc., 2009, 135–163; doi:10.1090/crmp/047/10'},
    'Co': {'title': 'Understanding groups like Γ₀(N)', 'authors': ['J. H. Conway'],
           'id': 'doi:10.1515/9783110893106.327', 'type': 'article',
           'location': 'in Groups, Difference Sets, and the Monster (Columbus, OH, 1993), Ohio State Univ. Math. Res. '
                       'Inst. Publ. 4, de Gruyter, 1996, 327–343'},
}

NEWMAN_PROOF = ('The formal proof is a new, self-contained one: conjugation by a matrix of Newman\'s form preserves '
                'Γ₀(N) by direct computation; a normalizing element is a real multiple of a primitive integral '
                'matrix, because the ℤ-span of Γ₀(N) is preserved; and that matrix has Newman\'s form, prime by '
                'prime, by an argument on p-adic valuations (NormalizerLean/NewmanLocal.lean).')

SCOPE = ('Only modular automorphisms are treated: the quotient Nor(Γ)/Γ of the normalizer in SL₂(ℝ). Results saying '
         'that every automorphism of a given modular curve is modular need algebraic geometry that Mathlib does not '
         'have, and are not formalized.')

# README table rows left out of an entry, by their tag: Part 3 §B (B₀(N)) is not part of the Palomar entry.
SKIP_TAGS = {'part3': ('B₀(N)',)}

ZEMEL_NOTE = ("Zemel's Corollary 2.6 (with Proposition 1.9) determines the normalizer of Γ_Δ(N) for every N and Δ: "
              'it lies in Γ₀^{∗,σ}(N) = D_σ⁻¹Γ₀(N/σ²)⁺D_σ for his σ = σ_H, which divides h_Δ. ')

# folder -> (project name, description, README parts, MSC 2020, extra scope, [(source, relationship, note)])
ENTRIES = {
    'part1': (
        "The normalizer of Γ₀(N): Newman's theorem, and the order and presentations of B(N)",
        ("Formal statements and proofs, in Lean 4 with Mathlib, about B(N) = Nor(Γ₀(N))/Γ₀(N), the normalizer of "
         "Γ₀(N) in SL₂(ℝ) modulo Γ₀(N), for every N ≥ 1: Newman's theorem describing the normalizer, in both "
         'directions; the order |B(N)| = 2^ω(n) ψ(N)/ψ(n), where h is the largest divisor of 24 with h² ∣ N and '
         'n = N/h²; generators and complete presentations of B(N) for every N; a criterion for B(N) to be the '
         'internal direct product of its local factors; B(18) ≅ S₄; and the errors in the published '
         'presentations: the Akbaş–Singerman relation fails in B(256), and Bars\'s presentations at levels 32, 64 '
         'and 128 define infinite groups, while completed presentations present B(32) and B(64) and Bars\'s '
         'presentation at level 256 presents B(256). 36 theorems, no sorry, only the axioms propext, '
         'Classical.choice and Quot.sound.'),
        [1], ['11F06', '20H05', '20F05', '68V20'],
        ' B(N) is defined as a quotient group, not as a presented group; a presentation is stated as an '
        'isomorphism PresentedGroup … ≃* B N that sends each generator to a specified class.',
        [('Ne', 'independently-proves', "Newman's theorem: the normalizer of Γ₀(N) consists of the matrices of "
          "Newman's form. " + NEWMAN_PROOF),
         ('AL', 'background', 'The Atkin–Lehner elements.'),
         ('AS', 'other', 'The formalization proves that one of the relations of their presentation fails in '
          'B(256).'),
         ('Ba', 'other', 'The formalization proves that the presentations at levels 32, 64 and 128 define '
          'infinite groups, that completed presentations present B(32) and B(64), and that the presentation at '
          'level 256 presents B(256).')]),
    'part2': (
        'Normalizers of Γ_Δ(N), Γ(N) and ±Γ₁(N)',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizers in SL₂(ℝ) of the groups '
         'Γ_Δ(N) between Γ₁(N) and Γ₀(N), and the quotients Nor(Γ)/Γ, the modular automorphism groups of the '
         'curves X_Δ(N): a generalization of Newman\'s description of the normalizer to Γ_Δ(N); Nor(Γ(N)) = '
         'SL₂(ℤ), so the modular automorphism group of X(N) is SL₂(ℤ/N)/{±1}; and, for N ≠ 4, Nor(±Γ₁(N)) is '
         'generated by Γ₀(N) and the Atkin–Lehner elements, so X₁(N) has 2^ω(N) φ(N)/2 modular automorphisms '
         'for N ≥ 3 (N = 4 is an exception). 34 theorems, no sorry, only the axioms propext, Classical.choice and '
         'Quot.sound.'),
        [2], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('KK', 'formalizes', 'The normalizer of ±Γ₁(N) for N ≠ 4.'),
         ('Ze', 'independently-proves', ZEMEL_NOTE + 'This implies the generalized Newman bound and, for h_Δ = '
          'h(N), the inclusion Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) and the index. The formal proofs were found independently; '
          'the author learned of the paper after this formalization was registered.'),
         ('L', 'formalizes', 'The normalizer of ±Γ₁(N) for N ≠ 4.'),
         ('AL', 'background', 'The Atkin–Lehner elements.'),
         ('Ne', 'background', "Newman's description of the normalizer of Γ₀(N), which Part 2 generalizes to "
          'Γ_Δ(N).')]),
    'part3': (
        'Normalizers of Γ_Δ(N): the group M_Δ, finiteness, and a coset count',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizers in SL₂(ℝ) of the groups '
         'Γ_Δ(N) between Γ₁(N) and Γ₀(N), and the quotients Nor(Γ_Δ(N))/Γ_Δ(N), which for −1 ∈ Δ are the '
         'modular automorphism groups of the curves X_Δ(N): the matrices allowed by the generalized Newman bound '
         'h_Δ form a group '
         'M_Δ = D⁻¹Γ₀(n_Δ)⁺D, D = diag(h_Δ, 1), which contains Nor(Γ_Δ(N)) and contains Γ₀(N) with finite index, so '
         'Nor(Γ_Δ(N))/Γ_Δ(N) is finite for every Δ; its order is [(ℤ/N)ˣ : Δ] times the number of pairs (σ, H), '
         'with σ in a fixed set of representatives of Γ₀(N)\\SL₂(ℤ) and H a Hermite normal form, such that σH '
         'normalizes Γ_Δ(N); and h_Δ = h(N) except under three explicit conditions on N and Δ. 11 theorems, no '
         'sorry, only the axioms propext, Classical.choice and Quot.sound.'),
        [3], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('Ze', 'independently-proves', ZEMEL_NOTE + 'This implies, in a sharper form, the inclusion of '
          'Nor(Γ_Δ(N)) in M_Δ and the finiteness of Nor(Γ_Δ(N))/Γ_Δ(N). The formal proofs were found independently; '
          'the author learned of the paper after this formalization was registered. The σH coset description and '
          'count and the criterion for h_Δ = h(N) are not stated in that paper; no systematic literature search '
          'has been made for them, so whether they appear earlier is unknown.'),
         ('Ne', 'background', "Newman's description of the normalizer of Γ₀(N), with the bound h(N) that the "
          'generalized bound h_Δ extends to Γ_Δ(N).')]),
    'part5': (
        'Modular automorphisms of Cartan modular curves of prime level',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizers in SL₂(ℝ) of the groups '
         'defining the split and non-split Cartan modular curves and their normalizer curves: for any level N, '
         'every element of the normalizer of a group containing Γ(N) is a rational matrix of a restricted form; '
         'X_sp(N) ≅ X₀(N²); X_sp(p) (p ≥ 5) and X_ns(p) (p odd) have exactly 2 modular automorphisms; X_sp⁺(p) '
         '(p ≥ 7) and X_ns⁺(p) (p ≥ 5) have none, and both bounds on p are sharp. 17 theorems, no sorry, only the '
         'axioms propext, Classical.choice and Quot.sound.'),
        [5], ['11F06', '14G35', '14H37', '11G18', '68V20'], ' The non-split curves, and X_sp⁺, are treated at prime '
        'level only.',
        [('DLM22', 'formalizes', 'The indices (Table 3.1), X_sp(N) ≅ X₀(N²) (Prop. 3.6), the normalizers of the '
          'Cartan groups of prime level and the exceptions p = 5 and p = 3 (Prop. 5.6, Lemma 5.10, Table 5.1); '
          'numbering of arXiv v2.'),
         ('DLM26', 'formalizes', 'The first two statements: Proposition 4.3 (1), (2) and Proposition 4.5 (1); '
          'numbering of arXiv v1.')]),
    'part6': (
        'Normalizers of the congruence subgroups Γ_H',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizers in SL₂(ℝ) of every '
         'congruence subgroup Γ ⊇ Γ(N), that is, of every Γ_H for H ≤ SL₂(ℤ/N): Nor(Γ)/Γ is finite, of order at '
         'most [SL₂(ℤ) : Γ]·Σ_{D ∣ N} ψ(D); the local restrictions of Dose–Lido–Mercuri on the determinants of '
         'normalizing matrices; if, at every p ∣ N, H mod p fixes no line or H mod p^{v_p(N)} lies in a split '
         'Cartan subgroup, then Nor(Γ_H)/Γ_H ≅ N(H)/H; and at prime level the order is always [N(H) : H], or '
         '2·[N(H) : H] when H fixes exactly one line. 21 theorems, no sorry, only the axioms propext, '
         'Classical.choice and Quot.sound.'),
        [6], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('DLM26', 'formalizes', 'Proposition 4.3, Proposition 4.5 (1), (2), (4), Algorithm 4.9, Step 3 with its '
          'correctness proof, and Table 3 as sanity checks. The finiteness bound, the general theorem '
          'Nor(Γ_H)/Γ_H ≅ N(H)/H and the result at prime level are not stated there; they are derived from these '
          'propositions. Numbering of arXiv v1.'),
         ('DLM22', 'background', 'Proposition 5.6 proves the case of Cartan groups and their normalizers of the '
          'general theorem by the same argument; numbering of arXiv v2.')]),
    'part7': (
        'The normalizer of Γ_Δ(N) for every N and every Δ',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizer in SL₂(ℝ) of Γ_Δ(N) for every '
         'N ≥ 1 and every subgroup Δ ≤ (ℤ/N)ˣ, with or without −1. Let h* be the largest h with h² ∣ N, d² ≡ 1 '
         '(mod h) for every d ∈ Δ, and Δ ⊇ ker((ℤ/N)ˣ → (ℤ/(N/h))ˣ); let n* = N/h*² and D* = diag(h*, 1). Then '
         'D*⁻¹Γ₀(n*)D* ≤ Nor(Γ_Δ(N)) ≤ D*⁻¹Γ₀(n*)⁺D*; an Atkin–Lehner element w_Q of level n* (conjugated by D*) '
         'normalizes Γ_Δ(N) iff ι*_Q(Δ̄) = Δ̄, where ι*_Q inverts the components of (ℤ/(N/h*))ˣ at the primes of '
         'Q; so Nor(Γ_Δ(N)) is described exactly, its index over Γ_Δ(N) is [(ℤ/N)ˣ : Δ]·ψ(N)/ψ(n*)·#{Q ∥ n* : '
         'ι*_Q(Δ̄) = Δ̄}, and Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) iff h* ∣ h(N). This is Zemel\'s determination of these '
         'normalizers, restated in closed form. 20 theorems, no sorry, only the axioms propext, Classical.choice '
         'and Quot.sound.'),
        [7], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('Ze', 'independently-proves', "Corollary 2.6, with Lemma 2.4, Proposition 2.7 and Proposition 1.9(iii): "
          "h* is Zemel's σ_H, and D*⁻¹Γ₀(n*)⁺D* is his Γ₀^{∗,σ_H}(N) (Remark 1.10). The order formula is not "
          'stated there in this form but follows directly. The proof formalized here was found independently, '
          'from numerical data, before the author learned of the paper; the Lean proofs follow that proof.'),
         ('Ne', 'background', "Newman's description of the normalizer of Γ₀(N), the case Δ = (ℤ/N)ˣ."),
         ('AL', 'background', 'The Atkin–Lehner elements.'),
         ('KK', 'background', 'The case Δ = {±1}, N ≠ 4 (the normalizer of ±Γ₁(N)).'),
         ('L', 'background', 'The case Δ = {±1}, N ≠ 4 (the normalizer of ±Γ₁(N)).')]),
    'part8': (
        'Normalizers of congruence subgroups at mixed level: Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂)',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizer in SL₂(ℝ) of '
         'Γ = Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) for coprime N₁ and N₂, the group of the fibre product X_{H₁} ×_{X(1)} X_{H₂}, '
         'where H₁ ≤ SL₂(ℤ/N₁) is such that, at every p ∣ N₁, H₁ mod p fixes no line or H₁ mod p^{v_p(N₁)} lies in '
         'a split Cartan subgroup, and H₂ ≤ SL₂(ℤ/N₂) is arbitrary. Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)); an element '
         '(det m)^{−1/2}·m of Nor(Γ_{H₂}(N₂)) normalizes Γ iff m mod N₁ normalizes H₁; and |Nor(Γ)/Γ| is [N(H₁) : '
         'H₁] times the number of classes of Nor(Γ_{H₂})/Γ_{H₂} whose determinant mod N₁ is the determinant of an '
         'element of the normalizer of H₁ in GL₂(ℤ/N₁). Explicit forms follow for Γ_Δ(N₂) (the class of an '
         'Atkin–Lehner involution w_Q contains an element of Nor(Γ) iff Q mod N₁ is such a determinant) and for H₂ '
         'of prime level fixing exactly '
         'one line; corollaries for Γ(N₁), Γ_ns⁺(p) and Γ_sp⁺(p); and an example: for the quaternion group Q₈ ≤ '
         'SL₂(F₇), the determinants are the squares, and Γ_{Q₈}(7) ∩ Γ₀(3) has 6 modular automorphisms, not 12, '
         'because the Fricke involution of X₀(3) does not lift. 18 theorems, no sorry, only the axioms propext, '
         'Classical.choice and Quot.sound.'),
        [8], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('ORIG8', 'other', 'The statements, in particular Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)) and the order formula with '
          'the determinant condition, are first presented with this formalization. A literature '
          'search (October 2026: arXiv, journals and web search; books and MathSciNet were not searched) found the '
          'ingredients and special cases below, but not these statements; whether they appear earlier is '
          'unknown.'),
         ('DLM26', 'background', 'Proposition 4.5 (1), (4): the local restrictions on det m that make det m prime '
          'to N₁; Algorithm 4.9 computes the normalizer of any Γ_H. Numbering of arXiv v1.'),
         ('Bo', 'background', 'Lemma 2.7 and Definition 2.8: an element of GL₂(ℤ/N₁) normalizing H₁ whose '
          'determinant is det m mod N₁ lifts the automorphism given by m. This is the "if" direction of the coset '
          'criterion; the converse, the inclusion Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)) and the order are not stated there.'),
         ('DLM22', 'other', 'Proposition 5.6 treats Cartan and Cartan-plus groups of composite level, including the '
          'case n ≡ 2 mod 4 with a Cartan-plus group split at 2, where one more element, of determinant 2, '
          'normalizes; numbering of arXiv v2.'),
         ('Fe', 'other', 'Proposition 3.1: on the fibre product of X₀(N) and X(p), the automorphisms extending the '
          'Atkin–Lehner involution w_N, and the structure of the group they generate, which depends on whether N '
          'is a square mod p.'),
         ('Ze', 'background', 'The normalizer of Γ_Δ(N₂), used for the explicit form for Γ_Δ(N₂) (Part 7).')]),
    'part9': (
        "Helling's theorem: the maximal subgroups of SL₂(ℝ) commensurable with SL₂(ℤ)",
        ('Formal statements and proofs, in Lean 4 with Mathlib, of Helling\'s theorem and of consequences for '
         'normalizers. A subgroup G ≤ SL₂(ℝ) is commensurable with SL₂(ℤ) if G ∩ SL₂(ℤ) has finite index in G and '
         'in SL₂(ℤ); Γ₀(N)⁺ is the group generated by the Atkin–Lehner elements of level N, and contains Γ₀(N). '
         'Every G commensurable with SL₂(ℤ) is conjugate into Γ₀(N)⁺ for some squarefree N, by (det A)^{−1/2}·A '
         'for an integral matrix A with det A > 0. For every N ≥ 1, Γ₀(N)⁺ is commensurable with SL₂(ℤ), and for '
         'squarefree N it is maximal among such groups; so the maximal subgroups of SL₂(ℝ) commensurable with '
         'SL₂(ℤ) are the conjugates of the Γ₀(N)⁺, N squarefree, that are commensurable with SL₂(ℤ) (Duncan\'s '
         'Theorem 2.11, in SL₂(ℝ)), and Γ₀(4)⁺ is not maximal. The commensurator of SL₂(ℤ) in SL₂(ℝ) consists of '
         'the (det A)^{−1/2}·A. For every Γ commensurable with SL₂(ℤ), the normalizer of Γ in SL₂(ℝ) is '
         'commensurable with SL₂(ℤ), so Nor(Γ)/Γ is finite, and Nor(Γ) is conjugate into Γ₀(N)⁺ for some '
         'squarefree N. The proof is the argument with p-adic trees that Duncan attributes to Conway, with an '
         'integral matrix for each vertex and distances computed from p-adic valuations of determinants and of '
         'the gcd of the entries; the vertices and edges fixed at the different primes are glued with the Smith '
         'normal form. 9 theorems, no sorry, only the axioms propext, Classical.choice and Quot.sound.'),
        [9], ['11F06', '20H05', '20E28', '22E40', '68V20'], '',
        [('He', 'formalizes', "Helling's theorem for SL₂(ℤ): every subgroup of SL₂(ℝ) commensurable with SL₂(ℤ) is "
          'conjugate into Γ₀(N)⁺ for some squarefree N. The paper (its title concerns the Hilbert modular group) '
          'was not consulted; the statement formalized is the one of Duncan\'s Theorem 2.11, which cites it.'),
         ('Du', 'formalizes', 'Theorem 2.11: the maximal arithmetic subgroups of PSL₂(ℝ) are the conjugates of '
          'G_(1,N)+ (Γ₀(N)⁺ here) for squarefree N. It is maximal_commensurable_iff, stated in SL₂(ℝ) (see the '
          'divergences). The formal proof follows Duncan\'s outline: Proposition 2.10 (a group commensurable with '
          'PSL₂(ℤ) stabilizes a cell, after Conway), then a conjugation that moves two lattices of the cell at '
          'maximal hyperdistance to L₁ and L_N. It works with integral matrices and p-adic valuations instead of '
          'lattices and trees, and uses the Smith normal form instead of the transitivity of Proposition 2.8. '
          'mem_commensurator_SL2ZR_iff implies Proposition 2.14 (a group commensurable with PSL₂(ℤ) consists of '
          'rational matrices up to scalars); its proof is different, from the conjugates of powers of the '
          'unipotent matrices. Numbering of arXiv v2.'),
         ('Co', 'other', 'The method: lattices in ℚ² and p-adic trees, and the result that a group commensurable '
          'with PSL₂(ℤ) stabilizes a cell (Duncan\'s Proposition 2.10, attributed to this paper), which the formal '
          'proof follows. The paper itself was not consulted.'),
         ('AL', 'background', 'The Atkin–Lehner elements, which generate Γ₀(N)⁺.')]),
}

COMMON = {
    'automation': {
        'methods': [{
            'method': 'agent',
            'models': ['Claude Opus 5.5'],
            'framework': 'Claude Code',
            'tool_setup': (
                'Claude Code agents wrote the Lean definitions, statements and proofs, following written '
                'mathematical notes (blueprints), ran the Lean builds, and generated the certificates and the '
                'numerical cross-checks (Python, Magma). Separate agents reviewed the statements.'),
            'cost': {
                'wall_time': 'about one week',
                'spend_usd': 'not tracked',
                'hardware': 'a 32-core workstation for builds and computations; models through the API',
            },
            'prompting_notes': (
                'Staged workflow. In each part the definitions and statements were written first (all sorry), '
                'reviewed by the author and by fresh reviewer agents, and frozen; only then were they proved. The '
                'frozen statements are checked mechanically by scripts/check_*_frozen.py.'),
        }],
        'spend_usd': 'not tracked',
        'notes': (
            'The author chose the results and reviewed and approved every definition and statement before it was '
            'frozen. After freezing, no statement changed (one definition was renamed, fricke to frickeP, to avoid '
            'a name clash). The Lean code, proofs included, was written by AI agents.'),
    },
    'fidelity': {
        'divergences': (
            'Normalizers are taken in SL₂(ℝ), not PSL₂(ℝ). If −1 ∉ Γ, the curve X_Γ depends only on ±Γ, and the '
            'order of Nor(Γ)/Γ is twice that of Nor(Γ)/±Γ, which can be smaller than the modular automorphism '
            'group of X_Γ, because Nor(Γ) ≤ Nor(±Γ) can be strict (Γ₁(4): 4, against 6 for ±Γ₁(4) = Γ₀(4)); so '
            'X(N) and X₁(N) appear through ±Γ(N) and ±Γ₁(N). Rational matrices A enter '
            'as (det A)^{−1/2}·A; Parts 3, 4 and 6 also prove the description as the normalizer in GL₂⁺(ℚ) modulo '
            'Γ·ℚ^×. In the presentations [x, y] = x⁻¹y⁻¹xy. Theorem numbers of Dose–Lido–Mercuri refer to '
            'arXiv:2005.09009v2 and arXiv:2610.08998v1.'),
    },
    'review': {
        'status': 'statements reviewed by the author; proofs machine-checked',
        'reviewers': ['Filip Najman'],
        'notes': (
            'Every definition and statement was reviewed by the author, and by AI reviewer agents, before it was '
            'frozen. Numerical cross-checks (scripts/check_*_statements.py and others) test the statements on '
            'small cases. Comparator checks each challenge against its solution, definitions included.'),
    },
}

# Parts 7 and 8 (added 2026-10-19) and Part 9 (2026-10-21) had a different workflow from Parts 1–6: their own
# automation and review notes. Part 9 also has its own tool setup, models, scope, divergences and acknowledgements.
OVERRIDES = {
    'part7': {
        'prompting_notes': (
            'Staged workflow. The theorem was found by an AI agent from numerical data and proved on paper; the '
            'definitions and statements were then written first (all sorry), checked numerically '
            '(scripts/check_star_statements.py), reviewed by two fresh reviewer agents (blind and adversarial; '
            'statements they suggested were added), approved by the author, and frozen; only then were they '
            'proved. The frozen statements are checked mechanically by scripts/check_star_frozen.py.'),
        'wall_time': 'about one day',
        'automation_notes': (
            'The author chose to formalize this result and approved every definition and statement before it was '
            'frozen. After freezing, no statement changed. The mathematics on paper and the Lean code, proofs '
            'included, were written by AI agents.'),
        'review_status': 'statements approved by the author; proofs machine-checked',
        'review_notes': (
            'The definitions and statements were checked numerically against a brute-force computation of the '
            'normalizer, reviewed by two AI reviewer agents before freezing, and approved by the author. '
            'Comparator checks the challenge against its solution, definitions included.'),
    },
    'part8': {
        'prompting_notes': (
            'Staged workflow. At the author\'s request, an AI agent proposed the case of mixed level, which the author chose, found the theorem '
            'from numerical experiments, proved it on paper and checked the literature; the definitions and '
            'statements were then written first (all sorry), checked numerically '
            '(scripts/check_mixed_statements.py), approved by the author, and frozen; only then were they proved. '
            'The frozen statements are checked mechanically by scripts/check_mixed_frozen.py.'),
        'wall_time': 'about one day',
        'automation_notes': (
            'The author chose to formalize this result and approved the definitions and statements before they '
            'were frozen. After freezing, no statement changed. The theorem, its proof on paper and the Lean code, '
            'proofs included, were found and written by AI agents.'),
        'review_status': 'statements approved by the author; proofs machine-checked',
        'review_notes': (
            'The definitions and statements were checked numerically against a brute-force computation of the '
            'normalizer (3716 cases and 143 for the corollaries) and approved by the author before freezing. '
            'After freezing, two AI reviewer agents (blind and adversarial) reviewed them and found no statement '
            'whose meaning differs from its description; their wording remarks (the statements give orders, and '
            '"w_Q survives" means that its class meets the normalizer) were applied to the README and to this '
            'metadata, not to the frozen Lean files. Comparator checks the challenge against its solution, '
            'definitions included.'),
    },
    'part9': {
        'prompting_notes': (
            'Staged workflow. At the author\'s request, an AI agent wrote a proof on paper for the formalization, '
            'from Duncan\'s account of the argument, with integral matrices and p-adic valuations in place of '
            'lattices and trees; the statements were then written first (all sorry), approved by the author, and '
            'frozen; only then were they proved. Part 9 adds no definitions. The frozen statements are checked '
            'mechanically by scripts/check_helling_frozen.py.'),
        'tool_setup': (
            'Claude Code agents wrote the proof on paper and the Lean statements and proofs, and ran the Lean builds '
            'and Comparator. After freezing, two separate reviewer agents (Claude Fable 5.1) reviewed the '
            'statements.'),
        'models': ['Claude Opus 5.5', 'Claude Fable 5.1'],
        'wall_time': 'about one day',
        'automation_notes': (
            'The author chose to formalize this result, on the suggestion of Maarten Derickx, and approved the '
            'statements before they were frozen. After freezing, no statement changed. The proof on paper and the '
            'Lean code, proofs included, were written by AI agents.'),
        'review_status': 'statements approved by the author; proofs machine-checked',
        'review_notes': (
            'The statements were approved by the author before freezing. They are about infinite groups, so there '
            'is no numerical check; the sanity statement not_maximal_gamma0Plus_four shows that gamma0Plus_maximal '
            'needs N squarefree. After freezing, two AI reviewer agents (blind and adversarial) reviewed them '
            'against the definitions, Mathlib\'s notions and Duncan\'s text, with Lean probes, and found no '
            'statement whose meaning differs from its description and no reachable junk value. Their wording '
            'remark (the docstring of not_maximal_gamma0Plus_four says that the squarefreeness in helling is '
            'needed, but there it is part of the conclusion; it is needed in gamma0Plus_maximal and '
            'maximal_commensurable_iff) was applied to the README and to this metadata, not to the frozen Lean '
            'files. Comparator checks the challenge against its solution, definitions included.'),
        'scope': (
            'Subgroups of SL₂(ℝ) commensurable with SL₂(ℤ). The description of the normalizer of a congruence '
            'subgroup that normG_conj_le_gamma0Plus suggests (its normalizer at finite level, extended by '
            'Atkin–Lehner elements) is not formalized.'),
        'divergences': (
            'The groups are subgroups of SL₂(ℝ), not of PSL₂(ℝ) as in Duncan\'s Theorem 2.11. Γ₀(N)⁺ contains −1, '
            'and adjoining −1 to a group commensurable with SL₂(ℤ) keeps it commensurable, so the maximal such '
            'groups contain −1 and correspond to Duncan\'s maximal arithmetic subgroups of PSL₂(ℝ); this '
            'translation is not formalized. Duncan\'s "conjugates of G_(1,N)+" are read as the conjugates that are '
            'again commensurable with SL₂(ℤ): maximal_commensurable_iff states this condition, since a conjugate by '
            'an arbitrary element of SL₂(ℝ) need not be commensurable with SL₂(ℤ). Commensurability is Mathlib\'s '
            'Subgroup.Commensurable, the strong sense used by Duncan (finite index in both groups). Rational '
            'matrices A enter as (det A)^{−1/2}·A, for integral A with det A > 0. Normalizers are taken in SL₂(ℝ). '
            'Theorem numbers of Duncan refer to arXiv:0810.1465v2.'),
    },
}

ACK = ('Mathlib. Comparator (leanprover/comparator). David Kurniadi Angdinata made the challenge self-contained '
       '(pull request #1), so that Comparator also checks the definitions.')
OVERRIDES['part9']['ack'] = ACK + " Maarten Derickx suggested formalizing Helling's theorem."

REFS = {'AL': 'Atkin–Lehner', 'AS': 'Akbaş–Singerman', 'Ba': 'Bars', 'KK': 'Kim–Koo', 'L': 'Lang',
        'Ne': 'Newman', 'DLM22': 'Dose–Lido–Mercuri 2022', 'DLM26': 'Dose–Lido–Mercuri 2026',
        'DN': 'Derickx–Najman', 'Ze': 'Zemel', 'Bo': 'Box', 'Du': 'Duncan', 'He': 'Helling', 'Co': 'Conway'}

ROW = re.compile(r'^\| *(?P<tag>[^|]*?) *\| *\[`(?P<name>[^`]+)`\]\((?P<file>[^)#]+)#L\d+\) *\| *(?P<stmt>.*?) *\|$')


def plain(md):
    md = md.replace('\\|', '|')
    md = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', md)
    return md.replace('**', '').replace('`', '')


def alignment(parts, skip_tags=()):
    stmts, part, tag = [], None, ''
    for line in open('README.md'):
        m = re.match(r'^## Part (\d+)\. (.*)$', line)
        if m:
            part, tag = (int(m.group(1)), m.group(2).strip()), ''
            continue
        if line.startswith('## '):
            part = None
            continue
        m = ROW.match(line.rstrip('\n'))
        if not (part and m and part[0] in parts):
            continue
        tag = m.group('tag') or tag
        if tag in skip_tags:
            continue
        refs = [REFS[r] for r in re.findall(r'\[([A-Za-z0-9]+)\]', m.group('stmt')) if r in REFS]
        source = f'Part {part[0]} ({plain(part[1])}), {tag}' if tag else f'Part {part[0]} ({plain(part[1])})'
        if refs:
            source += '; ' + ', '.join(dict.fromkeys(refs))
        stmts.append({'source': source, 'lean': 'NormalizerLean.' + m.group('name'),
                      'module': m.group('file')[:-len('.lean')].replace('/', '.'), 'status': 'proved',
                      'note': plain(m.group('stmt'))})
    return {'namespace': 'NormalizerLean', 'statements': stmts}


def common(folder):
    """COMMON, with the notes of `OVERRIDES` for Parts 7, 8 and 9."""
    doc = copy.deepcopy(COMMON)
    o = OVERRIDES.get(folder)
    if o:
        method = doc['automation']['methods'][0]
        method['prompting_notes'] = o['prompting_notes']
        method['cost']['wall_time'] = o['wall_time']
        if 'models' in o:
            method['models'] = o['models']
        if 'tool_setup' in o:
            method['tool_setup'] = o['tool_setup']
        doc['automation']['notes'] = o['automation_notes']
        doc['review']['status'] = o['review_status']
        doc['review']['notes'] = o['review_notes']
        if 'divergences' in o:
            doc['fidelity']['divergences'] = o['divergences']
    return doc


def document(folder):
    name, description, parts, msc, scope_extra, sources = ENTRIES[folder]
    return {
        'version': 'v0.4',
        'project': {'name': name, 'description': description, 'authors': ['Filip Najman'],
                    'responsible_maintainers': ['Filip Najman'], 'license': 'Apache-2.0'},
        'classification': {'arxiv': ['math.NT', 'math.GR'], 'msc2020': msc},
        'sources': [dict(SOURCES[k], relationship=rel, note=note) for k, rel, note in sources],
        'related_formalizations': [],
        'status': {'scope': OVERRIDES.get(folder, {}).get('scope', SCOPE + scope_extra), 'sorry_count': 0,
                   'sorry_in_definitions': 0, 'axioms': []},
        **common(folder),
        'alignment': alignment(parts, SKIP_TAGS.get(folder, ())),
        'acknowledgements': OVERRIDES.get(folder, {}).get('ack', ACK),
    }


def render(doc):
    head = ('# Palomar metadata (formalization.yaml v0.4), generated by scripts/make_formalization.py from that\n'
            '# script and the tables in README.md. Edit those, not this file.\n')
    return head + yaml.safe_dump(doc, allow_unicode=True, sort_keys=False, width=120)


def validate(folder, doc):
    """The checks of Palomar's template validator, the Palomar provenance rules, and the Comparator names."""
    errors = []
    if doc.get('version') != 'v0.4':
        errors.append('version must be v0.4')
    if doc['project'].get('license') != 'Apache-2.0':
        errors.append('project.license must be Apache-2.0')
    desc = doc['project'].get('description', '')
    if not desc.strip() or len(desc.strip()) > 10000:
        errors.append('project.description must be nonempty, at most 10000 characters')
    for section in ('project', 'classification', 'automation', 'review'):
        if not isinstance(doc.get(section), dict):
            errors.append(f'{section} must be a mapping')
    if not doc['project'].get('responsible_maintainers'):
        errors.append('project.responsible_maintainers must be nonempty')
    if 'TEMPLATE' in json.dumps(doc, ensure_ascii=False):
        errors.append('a TEMPLATE value is left')
    rels = {s.get('relationship') for s in doc['sources']}
    original = any(s.get('type') == 'original-proof' for s in doc['sources'])
    if original and not rels <= {'background', 'other'}:
        errors.append('an original result allows only background or other relationships')
    if not original and not {'formalizes', 'adapts', 'independently-proves'} & rels:
        errors.append('a source-based result needs a formalizes, adapts or independently-proves source')
    names = [s['lean'] for s in doc['alignment']['statements']]
    config = json.load(open(f'palomar/{folder}/comparator.json'))
    if sorted(names) != sorted(config['theorem_names']):
        errors.append('the alignment names differ from the Comparator configuration: %s' % sorted(
            set(names) ^ set(config['theorem_names'])))
    if re.search(r'\d+ theorems', doc['project']['description']).group(0) != f'{len(names)} theorems':
        errors.append('the number of theorems in the description is wrong')
    return [f'{folder}: {e}' for e in errors]


if __name__ == '__main__':
    errors, total = [], 0
    for folder in ENTRIES:
        doc = document(folder)
        text = render(doc)
        errors += validate(folder, yaml.safe_load(text))
        out = f'palomar/{folder}/formalization.yaml'
        if '--check' in sys.argv:
            if not os.path.exists(out) or open(out).read() != text:
                errors.append(out + ' is not up to date')
        else:
            open(out, 'w').write(text)
        total += len(doc['alignment']['statements'])
    print('\n'.join(errors) if errors else f'OK: {len(ENTRIES)} entries, {total} compared theorems')
    sys.exit(1 if errors else 0)
