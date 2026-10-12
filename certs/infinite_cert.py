"""Build affine (wreath) action data for T8(b) from Magma's coset actions.

For G = <w,s | w^2, s^h, (ws)^k> and H = Stab(coset 0) with infinite abelianization:
Schreier generators y_(i,x) for non-tree edges; relators of H by Reidemeister rewriting of
every relator at every coset; psi : H -> Z an integer vector killing all of them.
The action of G on Fin n x Z:  (i, m) . x = (i.x, m + t_x(i)),  t_x(i) = psi(y_(i,x)).
Run: python3 infinite_cert.py  (reads infinite_data_output.txt).
"""
import re, json
from fractions import Fraction
from sympy import Matrix

def parse():
    txt = open('infinite_data_output.txt').read()
    out = []
    for blk in re.finditer(r'DATA h=(\d+) k=(\d+) index=(\d+).*?\nPERM_W \[(.*?)\]\nPERM_S \[(.*?)\]', txt, re.S):
        h, k, n = map(int, blk.group(1, 2, 3))
        pw = [int(x) - 1 for x in blk.group(4).split(',')]
        ps = [int(x) - 1 for x in blk.group(5).split(',')]
        out.append((h, k, n, {'w': pw, 's': ps}))
    return out

def relators(h, k):
    return [[('w', 1)] * 2, [('s', 1)] * h, [('w', 1), ('s', 1)] * k]

def build(h, k, n, perm):
    inv = {x: [perm[x].index(i) for i in range(n)] for x in perm}
    # BFS spanning tree from coset 0
    tree, seen, order, parent = set(), {0}, [0], {0: None}
    for i in order:
        for x in ('w', 's'):
            for (j, e, sg) in ((perm[x][i], (i, x), 1), (inv[x][i], (inv[x][i], x), -1)):
                if j not in seen:
                    seen.add(j); order.append(j); tree.add(e); parent[j] = (i, x, sg)
    assert len(seen) == n
    edges = [(i, x) for i in range(n) for x in ('w', 's') if (i, x) not in tree]
    idx = {e: c for c, e in enumerate(edges)}
    rows = []
    for i in range(n):
        for r in relators(h, k):
            v = [0] * len(edges); c = i
            for (x, sgn) in r:
                if sgn == 1:
                    if (c, x) in idx: v[idx[(c, x)]] += 1
                    c = perm[x][c]
                else:
                    c = inv[x][c]
                    if (c, x) in idx: v[idx[(c, x)]] -= 1
            assert c == i
            rows.append(v)
    ns = Matrix(rows).nullspace()
    assert ns, 'no infinite abelian quotient'
    vec = ns[0]
    den = 1
    for q in vec: den = den * Fraction(str(q)).denominator // __import__('math').gcd(den, Fraction(str(q)).denominator)
    psi = [int(q * den) for q in vec]
    t = {x: [0] * n for x in ('w', 's')}
    for (e, c) in idx.items():
        t[e[1]][e[0]] = psi[c]
    # pick an edge with nonzero translation; witness word tau_i x tau_j^-1
    def tau(i):
        word = []
        while parent[i] is not None:
            a, x, sg = parent[i]; word.append((x, sg)); i = a
        return word[::-1]
    e = next(e for e in edges if t[e[1]][e[0]] != 0)
    i, x = e; j = perm[x][i]
    witness = tau(i) + [(x, 1)] + [(y, -sg) for (y, sg) in reversed(tau(j))]
    return {'h': h, 'k': k, 'n': n, 'sigma_w': perm['w'], 'sigma_s': perm['s'],
            'sigmainv_w': inv['w'], 'sigmainv_s': inv['s'], 't_w': t['w'], 't_s': t['s'],
            'witness': witness}

def act(D, word, i, m):
    for (x, sg) in word:
        if sg == 1:
            m += D['t_' + x][i]; i = D['sigma_' + x][i]
        else:
            i = D['sigmainv_' + x][i]; m -= D['t_' + x][i]
    return i, m

certs = []
for (h, k, n, perm) in parse():
    D = build(h, k, n, perm)
    for r in relators(h, k):
        for i in range(n):
            assert act(D, r, i, 0) == (i, 0)
    i, m = act(D, D['witness'], 0, 0)
    assert i == 0 and m != 0
    print(f"h={h} k={k} n={n} t_w={D['t_w']} t_s={D['t_s']} witness={D['witness']} translation={m}")
    certs.append(D)
json.dump(certs, open('infinite_certs.json', 'w'), indent=1)
