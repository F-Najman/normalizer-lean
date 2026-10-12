"""Numerical checks for the Cartan statements (NormalizerDelta/StatementsCartan.lean).

For a prime p and the image Hbar <= SL2(F_p) of Gamma_sp(p), Gamma_sp+(p), Gamma_ns(p), Gamma_ns+(p)
(C_ns = {[[a, e b], [b, a]]}, e the least non-square; C_ns+ = C_ns u C_ns.diag(1,-1)):
1. |Hbar| and [SL2(Z) : Gamma] = |SL2(F_p)| / |Hbar| (expect p(p+1) for sp, p(p-1) for ns);
2. whether Hbar has a common invariant line in F_p^2 (DLM26 Prop 4.5(1): if not, every normalizer element has
   determinant prime to p, hence (det | p, Prop 4.3(2)) lies in SL2(Z));
3. [N_{SL2(F_p)}(Hbar) : Hbar]: for groups without invariant line this is |Nor(Gamma)/Gamma|.
   Expected: ns: 2 (p odd); ns+: 1 (p >= 5), 3 (p = 3); sp+: 1 (p >= 7), 3 (p = 5); sp: 2 (p >= 5), where
   sp has invariant lines (handled by X_sp(p) = X_0(p^2) and |B(p^2)| = 2 for p >= 5).
4. Witnesses g in SL2(F_p) normalizing but not in Hbar for sp+(5), ns+(3).
Run: python3 scripts/check_cartan_statements.py
"""
from itertools import product

def sl2(p):
    return [(a, b, c, d) for a, b, c, d in product(range(p), repeat=4) if (a * d - b * c) % p == 1]

def mul(x, y, p):
    a, b, c, d = x; e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)

def inv(x, p):
    a, b, c, d = x
    return (d % p, (-b) % p, (-c) % p, a % p)

def nonsq(p):
    sq = {x * x % p for x in range(p)}
    return min(e for e in range(1, p) if e not in sq)

def groups(p):
    S = sl2(p)
    G = {}
    G['sp'] = [x for x in S if x[1] == 0 and x[2] == 0]
    G['sp+'] = [x for x in S if (x[1] == 0 and x[2] == 0) or (x[0] == 0 and x[3] == 0)]
    if p > 2:
        e = nonsq(p)
        G['ns'] = [x for x in S if x[3] == x[0] and x[1] == e * x[2] % p]
        G['ns+'] = G['ns'] + [x for x in S if x[3] == (-x[0]) % p and x[1] == (-e * x[2]) % p]
    return S, G

def invariant_line(H, p):
    lines = [(1, t) for t in range(p)] + [(0, 1)]
    for (u, v) in lines:
        ok = True
        for (a, b, c, d) in H:
            w = ((a * u + b * v) % p, (c * u + d * v) % p)
            if (w[0] * v - w[1] * u) % p != 0:
                ok = False; break
        if ok:
            return (u, v)
    return None

def normalizer(S, H, p):
    Hs = set(H)
    return [g for g in S if all(mul(mul(g, h, p), inv(g, p), p) in Hs for h in H)]

fails = 0
expect = {'ns': lambda p: 2, 'ns+': lambda p: 1 if p >= 5 else 3,
          'sp+': lambda p: 1 if p >= 7 else (3 if p == 5 else None), 'sp': lambda p: 2 if p >= 5 else None}
for p in [2, 3, 5, 7, 11, 13]:
    S, G = groups(p)
    for name, H in G.items():
        Nn = normalizer(S, H, p)
        line = invariant_line(H, p)
        idx = len(S) // len(H)
        q = len(Nn) // len(H)
        exp = expect[name](p)
        idx_exp = p * (p + 1) if name == 'sp' else (p * (p - 1) if name == 'ns' else None)
        ok = (exp is None or q == exp) and (idx_exp is None or idx == idx_exp) and \
             (name == 'sp' or p < 5 and name == 'sp+' or line is None)
        fails += not ok
        print(f"p={p:2d} {name:4s} |H|={len(H):4d} [SL2:Gamma]={idx:5d} invariant line={line} "
              f"[N(H):H]={q} expected={exp} {'ok' if ok else 'FAIL'}")
# witnesses
for p, name in [(5, 'sp+'), (3, 'ns+')]:
    S, G = groups(p)
    H = set(G[name])
    W = [g for g in normalizer(S, G[name], p) if g not in H]
    print(f"witness for {name}({p}): {W[0]} (one of {len(W)})")
print("failures:", fails)
