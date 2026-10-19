#!/usr/bin/env python3
"""Numerical check of the Part 8 statements (NormalizerDelta/StatementsMixed.lean), with the definitions of
NormalizerLean/Defs.lean (Parts 6-8) implemented literally.

Setting: N = N1*N2, gcd(N1, N2) = 1, H1 <= SL_2(Z/N1), H2 <= SL_2(Z/N2), Gamma = Gamma_{H1}(N1) cap Gamma_{H2}(N2)
= Gamma_H with H = H1 x H2 (CRT).  No -1 is added anywhere: the quotients are Nor_{SL_2(R)}(Gamma)/Gamma.
Brute force (DLM26, Prop. 4.3): the classes of Nor(Gamma)/Gamma are the primitive integral m = s*h (h in Hermite
form (a b; 0 d), ad = D | N, s a representative of Gamma \\ SL_2(Z)) such that m t adj(m)/D is integral and lies in
Gamma for t in lifts of generators of H and generators of Gamma(N)/Gamma(N D).

For every H1 of type I (hloc: for p | N1, H1 mod p fixes no line, or H1 mod p^v lies in a split Cartan) up to
SL_2-conjugacy and every H2 (all subgroups up to conjugacy, or H_Delta for every Delta), the script checks:
  isUnit_det_of_mem_normG_inf  every normalizing primitive m of Gamma has gcd(det m, N1) = 1;
  normG_inf_le                 ... and normalizes Gamma_{H2}(N2);
  mem_normG_inf_iff            for m in Nor(Gamma_{H2}) (all class representatives times all lifts of
                               SL_2(Z/N1)/H1 into Gamma(N2), and twice those when 2 does not divide N1):
                               m normalizes Gamma iff NormalizesMat H1 (m mod N1)  [for every H1, also not type I];
  normG_inf_inf_eq, relIndex_inf_normG   #{classes of Nor(Gamma) inside Gamma_{H2}} = [N(H1) : H1];
  exists_mul_mem_normG_inf_iff  a class of Nor(Gamma_{H2}) contains an element of Nor(Gamma) iff
                               IsNormDet H1 (det m) [for every H1];
  card_BG_inf, card_BG_inf_of_isNormDet, card_BG_inf_GammaDelta (with Part 7's hStar, nStar, IsIotaStable),
  card_BG_inf_prime_unique(_of_not) (N2 = p prime, H2 fixing exactly one line);
  card_BG_Gamma_inf, card_BG_GammaNsPlus_inf (p = 5, 7), card_BG_GammaSpPlus_inf (p = 7);
  isNormDet_Q8mod7_iff, card_BG_Q8mod7 = 6, card_BG_Q8mod7_inf_two = 12, card_BG_Q8mod7_inf_three = 6.
IsNormDet H u (u a unit) is computed as: some g in GL_2(Z/N1) with det g = u has g h g^-1 in H for all h in H
(NormalizesMat for invertible g; a matrix with unit determinant is invertible).
Usage: python3 scripts/check_mixed_statements.py [NMAX_DELTA NMAX_GENERAL [JOBS]]   (default 30 36 6)
"""
import sys
from fractions import Fraction
from itertools import product
from math import gcd
from multiprocessing import Pool

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from aut_orders import factor, divisors, psi  # noqa: E402
from check_star_statements import units, all_subgroups, hstar, is_iota_stable, exact_divisors  # noqa: E402


def mul(A, B, n=None):
    a, b, c, d = A
    e, f, g, h = B
    r = (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)
    return tuple(x % n for x in r) if n else r


def adj(M):
    a, b, c, d = M
    return (d, -b, -c, a)


def det(M):
    return M[0] * M[3] - M[1] * M[2]


def inv_mod(M, n):
    t = pow(det(M) % n, -1, n)
    return tuple((x * t) % n for x in adj(M))


def egcd(a, b):
    if b == 0:
        return (abs(a), 1 if a >= 0 else -1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)


def lift_sl2(M, n):
    """A lift of M in SL_2(Z/n) to SL_2(Z)."""
    if n == 1:
        return (1, 0, 0, 1)
    a, b, c, d = [x % n for x in M]
    if c == 0:
        c = n
    t = 0
    while gcd(c, d + t * n) != 1:
        t += 1
    d = d + t * n
    g, x, y = egcd(d, -c)
    for k in range(n):
        if (x + k * c - a) % n == 0 and (y + k * d - b) % n == 0:
            A = (x + k * c, y + k * d, c, d)
            assert det(A) == 1
            return A
    raise ValueError('no lift')


def closure(gens, n):
    I = (1 % n, 0, 0, 1 % n)
    S, frontier = {I}, [I]
    gens = [tuple(x % n for x in g) for g in gens]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g, n)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


_SL = {}


def sl2(n):
    if n not in _SL:
        _SL[n] = sorted(closure([(1, 1, 0, 1), (0, n - 1, 1, 0)], n)) if n > 1 else [(0, 0, 0, 0)]
    return _SL[n]


_GL = {}


def gl2(n):
    if n not in _GL:
        _GL[n] = [M for M in product(range(n), repeat=4) if gcd(det(M) % n, n) == 1] if n > 1 else [(0, 0, 0, 0)]
    return _GL[n]


def gens_of(S, n):
    gens, cur = [], closure([], n)
    for x in sorted(S):
        if x not in cur:
            gens.append(x)
            cur = closure(gens, n)
            if len(cur) == len(S):
                break
    return gens


def normalizes_mod(g, S, gens, n):
    if n == 1:
        return True
    gi = inv_mod(g, n)
    return all(mul(mul(g, s, n), gi, n) in S for s in gens)


def lines(n):
    seen, out = set(), []
    U = [u for u in range(n) if gcd(u, n) == 1]
    for x in range(n):
        for y in range(n):
            if gcd(gcd(x, y), n) != 1 or (x, y) in seen:
                continue
            out.append((x, y))
            for u in U:
                seen.add((u * x % n, u * y % n))
    return out


def fixes(v, gens, n):
    """FixesLine (for unimodular v): (h mod n) v = c v for some c, for all generators h."""
    x, y = v
    for g in gens:
        X, Y = (g[0] * x + g[1] * y) % n, (g[2] * x + g[3] * y) % n
        if not any((c * x - X) % n == 0 and (c * y - Y) % n == 0 for c in range(n)):
            return False
    return True


def fixed_lines(H, N, q):
    gq = [tuple(x % q for x in g) for g in (gens_of(H, N) if N > 1 else [])]
    return [L for L in lines(q) if fixes(L, gq, q)]


def type_I(H1, n):
    for p, v in factor(n).items():
        if not fixed_lines(H1, n, p):
            continue
        q = p ** v
        st = fixed_lines(H1, n, q)
        if not any((a[0] * b[1] - a[1] * b[0]) % p for a in st for b in st):
            return False
    return True


def subgroups_up_to_conj(n):
    G = sl2(n)
    I = closure([], n)
    key = lambda S: min(tuple(sorted(mul(mul(g, s, n), inv_mod(g, n), n) for s in S)) for g in G) if n > 1 else (0,)
    seen, todo, classes = {I}, [I], {}
    while todo:
        S = todo.pop()
        k = key(S)
        if k in classes:
            continue
        classes[k] = S
        for a in G:
            if a not in S:
                T = closure(list(gens_of(S, n)) + [a], n)
                if T not in seen:
                    seen.add(T)
                    todo.append(T)
    return sorted(classes.values(), key=len)


def crt(x1, n1, x2, n2):
    if n1 == 1:
        return x2 % n2
    if n2 == 1:
        return x1 % n1
    return (x1 + n1 * ((x2 - x1) * pow(n1, -1, n2) % n2)) % (n1 * n2)


def product_group(H1, N1, H2, N2):
    return frozenset(tuple(crt(a[i], N1, b[i], N2) for i in range(4)) for a in H1 for b in H2)


def H_delta(N2, Delta):
    return frozenset(M for M in sl2(N2) if M[2] % N2 == 0 and (M[3] % N2 if N2 > 1 else 0) in Delta)


def hnfs(N):
    out = []
    for D in divisors(N):
        for a in divisors(D):
            d = D // a
            for b in range(d):
                if gcd(gcd(a, b), d) == 1:
                    out.append((a, b, 0, d))
    return out


def tests_for(N, H):
    return ([lift_sl2(h, N) for h in gens_of(H, N)] if N > 1 else []) + [(1, N, 0, 1), (1, 0, N, 1),
                                                                          (1 + N, N, -N, 1 - N)]


def normalizes_int(m, N, H, tests=None):
    """Does D^{-1/2} m (m integral, D = det m > 0) normalize Gamma_H, H <= SL_2(Z/N)?  m t adj(m) / D is unchanged
    when m is scaled, so m need not be primitive."""
    D = det(m)
    if D <= 0:
        return False
    tests = tests if tests is not None else tests_for(N, H)
    ma = adj(m)
    for t in tests:
        P = mul(mul(m, t), ma)
        if any(x % D for x in P):
            return False
        if N > 1 and tuple((x // D) % N for x in P) not in H:
            return False
    return True


def normalizing(N, H):
    """One primitive integral m per class of Nor(Gamma_H)/Gamma_H."""
    seen, reps = set(), []
    for M in sl2(N):
        if M in seen:
            continue
        reps.append(M)
        for h in H:
            seen.add(mul(h, M, N))
    reps = [lift_sl2(M, N) for M in reps]
    tests = tests_for(N, H)
    return [mul(s, h) for h in hnfs(N) for s in reps if normalizes_int(mul(s, h), N, H, tests)]


def normalizes_mat(H1, N1, g):
    """NormalizesMat H1 g (Defs.lean), g a matrix over Z/N1 (any determinant)."""
    if N1 == 1:
        return True
    return all(any(mul(g, h, N1) == mul(h2, g, N1) for h2 in H1) for h in H1)


def local_data(N1, H1):
    gens = gens_of(H1, N1) if N1 > 1 else []
    nsl = sum(1 for g in sl2(N1) if normalizes_mod(g, H1, gens, N1)) if N1 > 1 else 1
    dets = frozenset(det(g) % N1 for g in gl2(N1) if normalizes_mod(g, H1, gens, N1)) if N1 > 1 else frozenset({0})
    return nsl // len(H1), dets


def red(x, n):
    return x % n if n > 1 else 0


def check_case(args):
    N1, H1, N2, H2, Delta = args
    N = N1 * N2
    errs = []
    idx, dets = local_data(N1, H1)
    tI = type_I(H1, N1)
    H = product_group(H1, N1, H2, N2)
    full = normalizing(N, H)
    nd = normalizing(N2, H2)
    t2 = tests_for(N2, H2)
    if tI:
        if not all(gcd(det(m), N1) == 1 for m in full):
            errs.append('isUnit_det_of_mem_normG_inf')
        if not all(normalizes_int(m, N2, H2, t2) for m in full):
            errs.append('normG_inf_le')
    # mem_normG_inf_iff and exists_mul_mem_normG_inf_iff (no condition on H1)
    cos, seen = [], set()
    for g in sl2(N1):
        if g in seen:
            continue
        cos.append(g)
        for h in H1:
            seen.add(mul(g, h, N1))
    lifts = [lift_sl2(tuple(crt(g[i], N1, (1, 0, 0, 1)[i] % N2 if N2 > 1 else 0, N2) for i in range(4)), N)
             for g in cos]
    tH = tests_for(N, H)
    for m in nd:
        hit = False
        for gam in lifts:
            for k in ([1, 2] if N1 % 2 else [1]):
                mm = tuple(k * x for x in mul(m, gam))
                lhs = normalizes_int(mm, N, H, tH)
                rhs = normalizes_mat(H1, N1, tuple(red(x, N1) for x in mm))
                if lhs != rhs:
                    errs.append('mem_normG_inf_iff')
                hit = hit or lhs
        if hit != (red(det(m), N1) in dets):
            errs.append('exists_mul_mem_normG_inf_iff')
    # normG_inf_inf_eq / relIndex_inf_normG (no condition on H1)
    inner = [m for m in full if det(m) == 1 and (N2 == 1 or tuple(x % N2 for x in m) in H2)]
    if len(inner) != idx:
        errs.append('relIndex_inf_normG')
    if tI:
        B = idx * sum(1 for m in nd if red(det(m), N1) in dets)
        if len(full) != B:
            errs.append('card_BG_inf')
        if all(red(u, N1) in dets for u in units(N1)) and len(full) != idx * len(nd):
            errs.append('card_BG_inf_of_isNormDet')
        if Delta is not None:
            S = sorted(Delta)
            hs = hstar(N2, S)
            ns = N2 // (hs * hs)
            wm = sum(1 for Q in exact_divisors(ns) if is_iota_stable(N2, S, hs, Q) and red(Q, N1) in dets)
            iD = Fraction(len(units(N2)), len(S))
            if len(full) != idx * iD * Fraction(psi(N2)) / Fraction(psi(ns)) * wm:
                errs.append('card_BG_inf_GammaDelta')
        if N2 > 1 and len(factor(N2)) == 1 and list(factor(N2).values()) == [1] and len(fixed_lines(H2, N2, N2)) == 1:
            nH2 = sum(1 for g in sl2(N2) if normalizes_mod(g, H2, gens_of(H2, N2), N2)) // len(H2)
            pred = idx * nH2 * (2 if red(N2, N1) in dets else 1)
            if len(full) != pred:
                errs.append('card_BG_inf_prime_unique' + ('' if red(N2, N1) in dets else '_of_not'))
    return dict(N1=N1, H1=len(H1), N2=N2, H2=len(H2), Delta=sorted(Delta) if Delta is not None else None,
                typeI=tI, brute=len(full), idx=idx, errs=sorted(set(errs)),
                obst=any(red(det(m), N1) not in dets for m in nd))


def H_ns_plus(p, eps):
    return frozenset(M for M in sl2(p) if (M[3] == M[0] and M[1] == eps * M[2] % p) or
                     (M[3] == (-M[0]) % p and M[1] == (-eps * M[2]) % p))


def H_sp_plus(p):
    return frozenset(M for M in sl2(p) if (M[1] == 0 and M[2] == 0) or (M[0] == 0 and M[3] == 0))


def main():
    ND = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    NG = int(sys.argv[2]) if len(sys.argv) > 2 else 36
    JOBS = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    N1s = [n for n in [1, 2, 3, 4, 5, 7, 8, 9] if n <= max(ND, NG)]
    subs1 = {n: subgroups_up_to_conj(n) for n in N1s}
    tasks = []
    for N1 in N1s:
        typeI = [S for S in subs1[N1] if type_I(S, N1)]
        other = [S for S in subs1[N1] if not type_I(S, N1)]
        print('# N1 = %d: %d classes of type I, %d others' % (N1, len(typeI), len(other)), flush=True)
        for N2 in range(1, ND // N1 + 1):
            if gcd(N1, N2) == 1:
                for Delta in all_subgroups(N2):
                    tasks += [(N1, H1, N2, H_delta(N2, frozenset(Delta)), frozenset(Delta)) for H1 in typeI]
        for N2 in [2, 3, 4, 5, 7]:
            if gcd(N1, N2) == 1 and N1 * N2 <= NG and N1 > 1:
                tasks += [(N1, H1, N2, H2, None) for H1 in typeI + other[:3] for H2 in subgroups_up_to_conj(N2)]
    print('# cases', len(tasks), flush=True)
    stats = {}
    bad = nobst = 0
    with Pool(JOBS) as pool:
        for r in pool.imap_unordered(check_case, tasks, chunksize=1):
            bad += bool(r['errs'])
            nobst += r['obst'] and r['typeI']
            if r['errs']:
                print('FAIL', r, flush=True)
    print('# cases with an obstruction (H1 of type I, some class of Nor(Gamma_H2) with det not in Det(H1)):', nobst)
    # §C and §S
    triv = lambda n: frozenset({(1 % n, 0, 0, 1 % n)})
    corr = []
    for N1, N2 in [(2, 3), (2, 5), (3, 2), (3, 4), (4, 3), (5, 2)]:
        for H2 in subgroups_up_to_conj(N2):
            corr.append(('card_BG_Gamma_inf', N1, triv(N1), N2, H2, len(sl2(N1))))
    for p, eps in [(5, 2), (7, 3)]:
        for N2 in [2, 3, 4]:
            for H2 in subgroups_up_to_conj(N2):
                corr.append(('card_BG_GammaNsPlus_inf', p, H_ns_plus(p, eps), N2, H2, 1))
    for N2 in [2, 3, 4]:
        for H2 in subgroups_up_to_conj(N2):
            corr.append(('card_BG_GammaSpPlus_inf', 7, H_sp_plus(7), N2, H2, 1))
    nc = 0
    for name, N1, H1, N2, H2, f in corr:
        full = len(normalizing(N1 * N2, product_group(H1, N1, H2, N2)))
        if full != f * len(normalizing(N2, H2)):
            print('FAIL', name, N1, N2, len(H2), flush=True)
            bad += 1
        nc += 1
    print('# corollary cases', nc)
    Q8 = closure([(0, 6, 1, 0), (2, 3, 3, 5)], 7)
    idx, dets = local_data(7, Q8)
    sq = {x * x % 7 for x in range(1, 7)}
    s_ok = (len(Q8) == 8 and dets == frozenset(sq)
            and len(normalizing(7, Q8)) == 6
            and len(normalizing(14, product_group(Q8, 7, H_delta(2, frozenset({1})), 2))) == 12
            and len(normalizing(21, product_group(Q8, 7, H_delta(3, frozenset({1, 2})), 3))) == 6)
    print('# isNormDet_Q8mod7_iff, card_BG_Q8mod7 (6), _inf_two (12), _inf_three (6):', 'OK' if s_ok else 'FAIL')
    bad += not s_ok
    print('# DONE failures', bad)


if __name__ == '__main__':
    main()
