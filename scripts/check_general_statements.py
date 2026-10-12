"""Numerical checks for the general statements (NormalizerDelta/StatementsGeneral.lean).

For each level N in LEVELS and every subgroup H <= SL2(Z/N) up to conjugacy, compute
Nor_{SL2(R)}(Gamma_H)/Gamma_H by brute force (DLM26 = arXiv:2610.08998, Prop. 4.3):
elements of Nor are m/sqrt(det m), m primitive integral, det m = D | N; left cosets m*Gamma(N) are
(beta, sigma mod N), beta = [[a,0],[c,d]], ad = D, 0 <= c < d, gcd(a,c,d) = 1 (right SL2(Z)-cosets of primitive
det-D matrices; psi(D) of them), sigma in SL2(Z/N); m normalizes Gamma_H iff m g adj(m) = D g' with g' in Gamma_H
for g in generators of Gamma_H/Gamma(N^2) (lifts of generators of H, and generators of Gamma(N)/Gamma(N^2)),
and the same for adj(m); all of this only depends on m and g mod N^2.  |MAut| = #(normalizing cosets)/|H|.
Checks:
 G   (normG_GammaH, card_BG_GammaH): if for all p | N, H mod p fixes no line or H mod p^{v_p(N)} is split,
     then |MAut| = [N(H):H] and every normalizing m has det 1;
 P   (card_BG_GammaH_prime[_unique]): N = p prime: |MAut| = [N(H):H] * (2 if H fixes exactly one line else 1);
 P0  (fixesUniqueLine_iff): for H <= standard Borel of SL2(F_p): (1,0) is the only fixed line iff U <= H;
 P2  (normG_GammaH_prime_unique): then W_p = [[0,-1],[p,0]] normalizes Gamma_H;
 B1  (isBorelMod_of_dvd_det, Prop. 4.5(1)): p^k | det m  =>  H mod p^k fixes a unimodular line;
 B2  (borel_shape, Prop. 4.5(2)): H mod p fixes exactly one line L and p | det m => columns of m and of adj m
     mod p span L (for L = <(1,0)> this is m = [[0,*],[0,0]] mod p);
 B4  (le_of_isSplitMod, Prop. 4.5(4)): H mod p^k split, p^k | N => v_p(det m) + k <= v_p(N);
 F4  (projSL_inv_mul_mem_GammaR, Prop. 4.3(4)): distinct cosets have representatives that differ mod N*D;
 F   (card_BG_le): |MAut| <= [SL2(Z):Gamma_H] * sum_{D|N} psi(D);
 S   (card_BG_GammaH_pmOne): |SL2(Z/N)|/2 for N = 37, 38, 39.
The pipeline is validated on known values: |B(4)| = 6, |B(6)| = 4, |B(9)| = 12 (also as X_sp(3)), X_0(p): 2 and
±X_1(p): p - 1 for p = 5, 7, 11 (Atkin-Lehner; Kim-Koo / Lang).
Run: python3 scripts/check_general_statements.py  (about 5 minutes)
"""
import sys, math
from itertools import product
from fractions import Fraction

LEVELS = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def mul(x, y, M):
    a, b, c, d = x; e, f, g, h = y
    return ((a*e+b*g) % M, (a*f+b*h) % M, (c*e+d*g) % M, (c*f+d*h) % M)

def adj(x, M):
    a, b, c, d = x
    return (d % M, (-b) % M, (-c) % M, a % M)

def red(x, M):
    return tuple(v % M for v in x)

def factor(n):
    f = {}; q = 2
    while q * q <= n:
        while n % q == 0:
            f[q] = f.get(q, 0) + 1; n //= q
        q += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def psi(D):
    r = Fraction(D)
    for p in factor(D): r *= Fraction(p + 1, p)
    return r

def sl2(N):
    L = N * N
    S = (0, L - 1, 1, 0); T = (1, 1, 0, 1); I = (1 % L, 0, 0, 1 % L)
    lift = {red(I, N): I}; frontier = [I]
    while frontier:
        nf = []
        for x in frontier:
            for g in (S, T):
                y = mul(x, g, L); k = red(y, N)
                if k not in lift:
                    lift[k] = y; nf.append(y)
        frontier = nf
    return sorted(lift), lift

def stable_vectors(els, H, q):
    """vectors v mod q with h v in (Z/q) v for all h in H (h reduced mod q)"""
    out = []
    for v in product(range(q), repeat=2):
        ok = True
        for i in H:
            a, b, c, d = els[i]
            w = ((a*v[0]+b*v[1]) % q, (c*v[0]+d*v[1]) % q)
            if not any((t*v[0]-w[0]) % q == 0 and (t*v[1]-w[1]) % q == 0 for t in range(q)):
                ok = False; break
        if ok: out.append(v)
    return out

def unimodular(v, q):
    return math.gcd(math.gcd(v[0], v[1]), q) == 1

def is_borel(els, H, q):
    return any(unimodular(v, q) for v in stable_vectors(els, H, q))

def is_split(els, H, q):
    st = stable_vectors(els, H, q)
    return any(math.gcd((v[0]*w[1]-v[1]*w[0]) % q, q) == 1 for v in st for w in st)

def lines_mod_p(els, H, p):
    st = [v for v in stable_vectors(els, H, p) if v != (0, 0)]
    return {(1, v[1]*pow(v[0], -1, p) % p) if v[0] % p else (0, 1) for v in st}

def colspan_line(x, p):
    """the line spanned mod p by the columns of a rank-1 matrix x (a,b,c,d) = [[a,b],[c,d]]"""
    a, b, c, d = (t % p for t in x)
    for v in ((a, c), (b, d)):
        if v != (0, 0):
            return (1, v[1]*pow(v[0], -1, p) % p) if v[0] else (0, 1)
    return None

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        print("FAIL", msg, flush=True)

def run(N):
    L = N * N
    els, lift = sl2(N)
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    mt = [[idx[mul(els[i], els[j], N)] for j in range(n)] for i in range(n)]
    inv = [idx[adj(e, N)] for e in els]
    conj = [[mt[mt[x][i]][inv[x]] for i in range(n)] for x in range(n)]
    e0 = idx[red((1, 0, 0, 1), N)]
    def closure(gens):
        S = {e0}; fr = [e0]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    y = mt[x][g]
                    if y not in S:
                        S.add(y); nf.append(y)
            fr = nf
        return frozenset(S)
    def key(K):
        return min(tuple(sorted(conj[x][i] for i in K)) for x in range(n))
    triv = frozenset([e0]); reps = {key(triv): (triv, [])}; fr = [(triv, [])]
    while fr:
        nf = []
        for K, gens in fr:
            seen = set()
            for g in range(n):
                if g in K: continue
                K2 = closure(gens + [g])
                if K2 in seen: continue
                seen.add(K2)
                k = key(K2)
                if k not in reps:
                    reps[k] = (K2, gens + [g]); nf.append((K2, gens + [g]))
        fr = nf
    fac = factor(N)
    divs = [D for D in range(1, N + 1) if N % D == 0]
    betas = []
    for D in divs:
        for a in range(1, D + 1):
            if D % a: continue
            d = D // a
            for c in range(d):
                if math.gcd(math.gcd(a, c), d) == 1:
                    betas.append((D, (a % L, 0, c % L, d % L)))
    kern = [(1, N % L, 0, 1), (1, 0, N % L, 1), ((1 + N) % L, 0, 0, (1 - N) % L)]
    def normalizes(m, D, hg, Hs):
        ma = adj(m, L)
        for g in hg:
            for (u, v) in ((m, ma), (ma, m)):
                X = mul(mul(u, g, L), v, L)
                if any(t % D for t in X): return False
                if idx.get(red(tuple(t // D for t in X), N)) not in Hs: return False
        return True
    # F4: representatives of distinct cosets differ mod N*D
    for D in divs:
        seen = set()
        for D2, beta in betas:
            if D2 != D: continue
            for s in range(n):
                r = red(mul(beta, lift[els[s]], L), N * D)
                check(r not in seen, f"F4 N={N} D={D}")
                seen.add(r)
    stats = {'G': 0, 'P': 0, 'B1': 0, 'B2': 0, 'B4': 0}
    results = {}
    for kH, (H, gens) in sorted(reps.items(), key=lambda kv: len(kv[1][0])):
        Hs = set(H)
        hg = [lift[els[g]] for g in gens] + kern
        Nor = [x for x in range(n) if all(conj[x][i] in Hs for i in H)]
        idxNH = len(Nor) // len(H)
        normal = []
        for D, beta in betas:
            for s in range(n):
                m = mul(beta, lift[els[s]], L)
                if normalizes(m, D, hg, Hs):
                    normal.append((D, m))
        check(len(normal) % len(H) == 0, f"divisibility N={N}")
        maut = len(normal) // len(H)
        results[kH] = maut
        check(maut <= Fraction(n, len(H)) * sum(psi(D) for D in divs), f"F bound N={N}")
        # local data
        borel = {}; split = {}
        for p, e in fac.items():
            for k in range(1, e + 1):
                borel[(p, k)] = is_borel(els, H, p**k)
                split[(p, k)] = is_split(els, H, p**k)
        hloc = all((not borel[(p, 1)]) or split[(p, e)] for p, e in fac.items())
        if hloc:
            stats['G'] += 1
            check(maut == idxNH and all(D == 1 for D, _ in normal), f"G N={N} |H|={len(H)}")
        if len(fac) == 1 and list(fac.values())[0] == 1:
            p = N; nl = len(lines_mod_p(els, H, p))
            stats['P'] += 1
            check(maut == idxNH * (2 if nl == 1 else 1), f"P p={p} |H|={len(H)}")
        for D, m in normal:
            for p, e in fac.items():
                vD = 0; t = D
                while t % p == 0: t //= p; vD += 1
                for k in range(1, vD + 1):
                    stats['B1'] += 1
                    check(borel[(p, k)], f"B1 N={N} p={p} k={k}")
                for k in range(1, e + 1):
                    if split[(p, k)]:
                        stats['B4'] += 1
                        check(vD + k <= e, f"B4 N={N} p={p} k={k}")
                if vD >= 1:
                    ls = lines_mod_p(els, H, p)
                    if len(ls) == 1:
                        stats['B2'] += 1
                        Lp = next(iter(ls))
                        check(colspan_line(m, p) == Lp and colspan_line(adj(m, L), p) == Lp, f"B2 N={N} p={p}")
    print(f"N={N}: {len(reps)} classes, checks G={stats['G']} P={stats['P']} B1={stats['B1']} "
          f"B2={stats['B2']} B4={stats['B4']}", flush=True)
    # known values (validation of the pipeline on known positives)
    def maut_of(pred):
        return results[key(frozenset(i for i, e in enumerate(els) if pred(e)))]
    known = []
    borel0 = lambda e: e[2] % N == 0                       # Gamma_0(N)
    pm1 = lambda e: e[2] % N == 0 and e[0] % N in (1 % N, (N - 1) % N)   # +-Gamma_1(N)
    if N == 4: known += [("|B(4)| (Gamma_0(4))", maut_of(borel0), 6)]
    if N == 6: known += [("|B(6)| (Gamma_0(6))", maut_of(borel0), 4)]
    if N == 9: known += [("|B(9)| (Gamma_0(9))", maut_of(borel0), 12)]
    if N == 3: known += [("|B(9)| (X_sp(3) = X_0(9), H = +-1)", maut_of(lambda e: e[1] == 0 and e[2] == 0), 12)]
    if N in (5, 7, 11): known += [(f"X_0({N})", maut_of(borel0), 2)]
    if N in (5, 7, 11): known += [(f"X_1({N}) (+-Gamma_1)", maut_of(pm1), N - 1)]
    for name, got, want in known:
        check(got == want, f"known value {name}: got {got}, want {want}")
        print(f"  known value {name}: {got} (expected {want})", flush=True)

def check_P0_P2(p):
    """all subgroups of the standard Borel of SL2(F_p)"""
    els, lift = sl2(p)
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    mt = [[idx[mul(els[i], els[j], p)] for j in range(n)] for i in range(n)]
    B = [i for i, e in enumerate(els) if e[2] == 0]
    e0 = idx[(1, 0, 0, 1)]
    def closure(gens):
        S = {e0}; fr = [e0]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    y = mt[x][g]
                    if y not in S: S.add(y); nf.append(y)
            fr = nf
        return frozenset(S)
    subs = {frozenset([e0])}; fr = [frozenset([e0])]
    while fr:
        nf = []
        for K in fr:
            for g in B:
                K2 = closure(list(K) + [g])
                if K2 not in subs: subs.add(K2); nf.append(K2)
        fr = nf
    U = {idx[(1, b, 0, 1)] for b in range(p)}
    L = p * p
    W = (0, L - 1, p, 0)
    cnt = 0
    for H in subs:
        Hs = set(H)
        unique_e1 = lines_mod_p(els, H, p) == {(1, 0)}
        check(unique_e1 == U.issubset(Hs), f"P0 p={p} |H|={len(H)}")
        if unique_e1:
            cnt += 1
            gens = [lift[els[i]] for i in H] + [(1, p % L, 0, 1), (1, 0, p % L, 1), ((1 + p) % L, 0, 0, (1 - p) % L)]
            Wa = adj(W, L); ok = True
            for g in gens:
                for (u, v) in ((W, Wa), (Wa, W)):
                    X = mul(mul(u, g, L), v, L)
                    if any(t % p for t in X) or idx.get(red(tuple(t // p for t in X), p)) not in Hs:
                        ok = False
            check(ok, f"P2 p={p} |H|={len(H)}")
    print(f"p={p}: {len(subs)} subgroups of the Borel, {cnt} with a unique fixed line: P0, P2 checked", flush=True)

if __name__ == '__main__':
    for N in LEVELS:
        run(N)
    for p in [2, 3, 5, 7, 11, 13]:
        check_P0_P2(p)
    for N, val in [(37, 25308), (38, 20520), (39, 26208)]:
        order = N**3
        for p in factor(N): order = order * (p*p - 1) // (p*p)
        check(order // 2 == val, f"S N={N}")
        print(f"S: |SL2(Z/{N})|/2 = {order // 2} (statement: {val})")
    print("TOTAL FAILURES:", fails)
