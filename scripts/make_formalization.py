"""Write palomar/<entry>/formalization.yaml, the Palomar metadata (formalization.yaml v0.4) of each entry.

The entries are the challenges of `make_challenge.py` except Part 4, which is not a Palomar entry. The fields are
below. The `alignment` section, a plain-language account of every compared theorem, is generated from the tables in
README.md, so the two cannot drift apart; its theorem names must be exactly those of the entry's Comparator
configuration.
Run: python3 scripts/make_formalization.py            (writes the files)
     python3 scripts/make_formalization.py --check    (checks that they are up to date and valid)
"""
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
    'ORIG3': {'title': 'Normalizers of Γ_Δ(N): results first presented with this formalization',
              'type': 'original-proof'},
    'DN': {'title': 'Sporadic points on X₀(N)', 'authors': ['M. Derickx', 'F. Najman'], 'id': 'arXiv:2511.09015',
           'type': 'preprint', 'location': 'https://arxiv.org/abs/2511.09015'},
}

NEWMAN_PROOF = ('The formal proof is a new, self-contained one: conjugation by a matrix of Newman\'s form preserves '
                'Γ₀(N) by direct computation; a normalizing element is a real multiple of a primitive integral '
                'matrix, because the ℤ-span of Γ₀(N) is preserved; and that matrix has Newman\'s form, prime by '
                'prime, by an argument on p-adic valuations (NormalizerLean/NewmanLocal.lean).')

SCOPE = ('Only modular automorphisms are treated: the quotient Nor(Γ)/Γ of the normalizer in SL₂(ℝ). Results saying '
         'that every automorphism of a given modular curve is modular need algebraic geometry that Mathlib does not '
         'have, and are not formalized.')

PRIORITY_NOTE = ('The results on M_Δ, the finiteness of Nor(Γ_Δ(N))/Γ_Δ(N), the coset count and h_Δ are first '
                 'presented with this formalization, by its author. No systematic literature search has been made, '
                 'so whether these results, or equivalent ones, appear earlier in the literature is unknown. The '
                 'description of the centre of GL₂⁺(ℚ), used for B₀(N), is standard.')

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
         ('L', 'formalizes', 'The normalizer of ±Γ₁(N) for N ≠ 4.'),
         ('AL', 'background', 'The Atkin–Lehner elements.'),
         ('Ne', 'background', "Newman's description of the normalizer of Γ₀(N), which Part 2 generalizes to "
          'Γ_Δ(N).')]),
    'part3': (
        'Normalizers of Γ_Δ(N): the group M_Δ, finiteness, a coset count, and B₀(N)',
        ('Formal statements and proofs, in Lean 4 with Mathlib, about the normalizers in SL₂(ℝ) of the groups '
         'Γ_Δ(N) between Γ₁(N) and Γ₀(N), and the quotients Nor(Γ_Δ(N))/Γ_Δ(N), which are the modular automorphism '
         'groups of the curves X_Δ(N) when −1 ∈ Δ, and twice as large otherwise: the matrices allowed by the '
         'generalized Newman bound h_Δ form a group '
         'M_Δ = D⁻¹Γ₀(n_Δ)⁺D, D = diag(h_Δ, 1), which contains Nor(Γ_Δ(N)) and contains Γ₀(N) with finite index, so '
         'Nor(Γ_Δ(N))/Γ_Δ(N) is finite for every Δ; its order is [(ℤ/N)ˣ : Δ] times the number of pairs (σ, H), '
         'with σ in a fixed set of representatives of Γ₀(N)\\SL₂(ℤ) and H a Hermite normal form, such that σH '
         'normalizes Γ_Δ(N); h_Δ = h(N) except under three explicit conditions on N and Δ; and the group B₀(N) of '
         'Derickx–Najman, the normalizer of Γ₀(N) in GL₂⁺(ℚ) modulo Γ₀(N)·ℚ^×, is isomorphic to '
         'B(N) = Nor(Γ₀(N))/Γ₀(N), while without the scalars the quotient is infinite. 14 theorems, no sorry, only '
         'the axioms propext, Classical.choice and Quot.sound.'),
        [3], ['11F06', '20H05', '14G35', '14H37', '68V20'], '',
        [('ORIG3', 'other', PRIORITY_NOTE),
         ('Ne', 'background', "Newman's description of the normalizer of Γ₀(N), with the bound h(N) that the "
          'generalized bound h_Δ extends to Γ_Δ(N).'),
         ('DN', 'background', 'The group B₀(N), which the formalization proves isomorphic to B(N).')]),
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
            'Normalizers are taken in SL₂(ℝ), not PSL₂(ℝ). If −1 ∉ Γ the quotient is twice the modular '
            'automorphism group, so X(N) and X₁(N) appear through ±Γ(N) and ±Γ₁(N). Rational matrices A enter '
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

ACK = ('Mathlib. Comparator (leanprover/comparator). David Kurniadi Angdinata made the challenge self-contained '
       '(pull request #1), so that Comparator also checks the definitions.')

REFS = {'AL': 'Atkin–Lehner', 'AS': 'Akbaş–Singerman', 'Ba': 'Bars', 'KK': 'Kim–Koo', 'L': 'Lang',
        'Ne': 'Newman', 'DLM22': 'Dose–Lido–Mercuri 2022', 'DLM26': 'Dose–Lido–Mercuri 2026',
        'DN': 'Derickx–Najman'}

ROW = re.compile(r'^\| *(?P<tag>[^|]*?) *\| *\[`(?P<name>[^`]+)`\]\((?P<file>[^)#]+)#L\d+\) *\| *(?P<stmt>.*?) *\|$')


def plain(md):
    md = md.replace('\\|', '|')
    md = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', md)
    return md.replace('**', '').replace('`', '')


def alignment(parts):
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
        refs = [REFS[r] for r in re.findall(r'\[([A-Za-z0-9]+)\]', m.group('stmt')) if r in REFS]
        source = f'Part {part[0]} ({plain(part[1])}), {tag}' if tag else f'Part {part[0]} ({plain(part[1])})'
        if refs:
            source += '; ' + ', '.join(dict.fromkeys(refs))
        stmts.append({'source': source, 'lean': 'NormalizerLean.' + m.group('name'),
                      'module': m.group('file')[:-len('.lean')].replace('/', '.'), 'status': 'proved',
                      'note': plain(m.group('stmt'))})
    return {'namespace': 'NormalizerLean', 'statements': stmts}


def document(folder):
    name, description, parts, msc, scope_extra, sources = ENTRIES[folder]
    return {
        'version': 'v0.4',
        'project': {'name': name, 'description': description, 'authors': ['Filip Najman'],
                    'responsible_maintainers': ['Filip Najman'], 'license': 'Apache-2.0'},
        'classification': {'arxiv': ['math.NT', 'math.GR'], 'msc2020': msc},
        'sources': [dict(SOURCES[k], relationship=rel, note=note) for k, rel, note in sources],
        'related_formalizations': [],
        'status': {'scope': SCOPE + scope_extra, 'sorry_count': 0, 'sorry_in_definitions': 0, 'axioms': []},
        **COMMON,
        'alignment': alignment(parts),
        'acknowledgements': ACK,
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
