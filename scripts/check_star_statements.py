#!/usr/bin/env python3
"""Numerical check of the Part 7 statements (NormalizerDelta/StatementsStar.lean), with the definitions of
NormalizerLean/Defs.lean (Part 7) implemented literally.

For every N in [NMIN, NMAX] and every subgroup Delta of (Z/N)^x (with or without -1):
  * hStar = Nat.findGreatest IsHStar N; every h with IsHStar divides it; it divides hDelta (epsDelta as in Defs.lean);
  * hStar_top, hStar_pmOne (N != 4), hStar_deltaPm_sq (N = M^2);
  * the brute-force normalizer (sigma*H enumeration of aut_orders.py, all pairs, not restricted to M_Delta):
      - every normalizing matrix A has D* A D*^-1 Atkin-Lehner of level n* for some Q || n* with IsIotaStable
        (mem_normG_GammaDeltaR_iff, =>; normG_le_MStar);
      - for every Q || n*, an Atkin-Lehner element w of level n* for Q gives D*^-1 w D* normalizing iff IsIotaStable
        (conj_mem_normG_iff), and so does every element of D*^-1 Gamma_0(n*) D* tried (Gamma0Star_le_normG);
      - |BG| = i_Delta * m = i_Delta * psi(N)/psi(n*) * wStar (card_BG_GammaDeltaR_hStar);
      - Nor <= Nor(Gamma_0(N)) iff hStar | hPart (normG_GammaDeltaR_le_Norm0_iff);
  * card_BG_GammaDeltaR_50 = 120, card_BG_GammaDeltaR_4_bot = 4, hStar_pmOne_four, isIotaStable_one,
    wStar_eq_sIota (h* = 1), MStar_le_MDelta (each D*^-1 w_Q D* lies in M_Delta; Gamma0Star <= Gamma0R(N)-conjugates
    are covered by the same test with Q = 1).
Usage: python3 scripts/check_star_statements.py [NMIN NMAX [JOBS]]   (default 1 60 8)
"""
import sys
from fractions import Fraction
from math import gcd
from multiprocessing import Pool

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from aut_orders import (factor, divisors, egcd, mul, adj, det, p1_reps, hnfs, apriori, normalizes, vp, psi,  # noqa
                        closure_add, in_M)


def units(N):
    return [u for u in range(N) if gcd(u, N) == 1] if N > 1 else [0]


def all_subgroups(N):
    U = units(N)
    start = frozenset({1 % N})
    seen, todo = {start}, [start]
    while todo:
        S = todo.pop()
        for a in U:
            if a not in S:
                T = closure_add(S, a, N)
                if T not in seen:
                    seen.add(T)
                    todo.append(T)
    return sorted(seen, key=lambda S: (-len(S), sorted(S)))


def cast(x, m):
    """ZMod.cast (x : ZMod N) : ZMod m for m | N: x.val mod m (ZMod 1 has one element, 0)."""
    return x % m if m > 0 else x


def is_hstar(N, S, h):
    return (h > 0 and N % (h * h) == 0 and all(cast(d, h) ** 2 % h == 1 % h for d in S)
            and all(u in S for u in units(N) if cast(u, N // h) == 1 % (N // h)))


def hstar(N, S):
    return max(h for h in range(0, N + 1) if h == 0 or is_hstar(N, S, h)) if N > 0 else 0


def hpart(N):
    return max(h for h in divisors(24) if N % (h * h) == 0)


def eps_delta(N, S):
    g = 0
    for d in S:
        g = gcd(g, max(d * d - 1, 0))     # (d : ZMod N).val ^ 2 - 1 in ℕ (truncated)
    return gcd(N, g)


def hdelta(N, S):
    e = eps_delta(N, S)
    r = 1
    for p, k in factor(N).items():
        r *= p ** min(vp(e, p), k // 2)
    return r


def is_iota_star(N, hs, Q, d, u):
    L = N // hs
    for p in factor(L):
        q = p ** vp(L, p)
        if Q % p == 0:
            if (cast(u, q) * cast(d, q)) % q != 1 % q:
                return False
        elif cast(u, q) != cast(d, q):
            return False
    return True


def is_iota_stable(N, S, hs, Q):
    return all((u in S) == any(is_iota_star(N, hs, Q, d, u) for d in S) for u in units(N))


def exact_divisors(n):
    return [Q for Q in divisors(n) if gcd(Q, n // Q) == 1]


def al_element(n, Q):
    """An integral matrix [[Q x, y], [n z, Q w]] of determinant Q (an Atkin-Lehner element times sqrt Q)."""
    g, a, b = egcd(Q, n // Q)          # a Q + b (n/Q) = 1  ->  Q*a*1 - (n/Q)*(-b)*1 ... take x = a, w = 1, y = -b? check
    # Q^2 x w - n y z = Q  <=>  Q x w - (n/Q) y z = 1: x = a, w = 1, y = -b, z = 1
    M = ((Q * a, -b), (n, Q))
    assert det(M) == Q
    return M


def is_al(A, n):
    """Is A/sqrt(det A) (A integral, det > 0) an Atkin-Lehner element of level n for some Q || n?  Returns Q or None.
    (Projectively: the primitive part [[x, y], [z, w]] of A has det Q || n, n | z, Q | x, Q | w.)"""
    x, y, z, w = A[0][0], A[0][1], A[1][0], A[1][1]
    g = gcd(gcd(x, y), gcd(z, w))
    x, y, z, w = x // g, y // g, z // g, w // g
    Q = x * w - y * z
    if Q <= 0 or n % Q or gcd(Q, n // Q) != 1:
        return None
    return Q if (z % n == 0 and x % Q == 0 and w % Q == 0) else None


def conj_D(A, h):
    """D A D^-1 for D = diag(h, 1), scaled to be integral: (a, h b; c / h, d) * h."""
    a, b, c, d = A[0][0], A[0][1], A[1][0], A[1][1]
    return ((a * h, b * h * h), (c, d * h))


def conj_Dinv(W, h):
    """D^-1 W D, scaled: (a, b / h; h c, d) * h."""
    a, b, c, d = W[0][0], W[0][1], W[1][0], W[1][1]
    return ((a * h, b), (c * h * h, d * h))


def gamma_gens(N, S):
    G = [((1, 1), (0, 1)), ((1, 0), (N, 1)), ((1 + N, N), (-N, 1 - N))]
    cur = frozenset({1 % N})
    for d in sorted(S):
        if d not in cur:
            cur = closure_add(cur, d, N)
            g, u, v = egcd(d, N)
            G.append(((u, -v), (N, d)))
    return G


def check_level(N):
    out = []
    if N <= 2:
        reps = [((1, 0), (0, 1))] if N == 1 else [((1, 0), (0, 1)), ((0, -1), (1, 0)), ((1, 0), (1, 1))]
    else:
        reps = p1_reps(N)
    pairs = [A for A in (mul(s, H) for s in reps for H in hnfs(N)) if N == 1 or apriori(A, N)]
    U = units(N)
    Uall = frozenset(U)
    g0 = gamma_gens(N, Uall)
    in0 = [normalizes(A, g0, N, Uall) for A in pairs]
    hp = hpart(N)
    for S in all_subgroups(N):
        bad = []
        hs = hstar(N, S)
        ns = N // (hs * hs)
        for h in range(1, N + 1):
            if is_hstar(N, S, h) and hs % h:
                bad.append('dvd_hStar h=%d' % h)
        if not is_hstar(N, S, hs):
            bad.append('isHStar_hStar')
        if hdelta(N, S) % hs:
            bad.append('hStar_dvd_hDelta')
        if S == Uall and hs != hp:
            bad.append('hStar_top')
        if S == frozenset({1 % N, (N - 1) % N}) and N != 4 and hs != 1:
            bad.append('hStar_pmOne')
        if S == frozenset({1 % N, (N - 1) % N}) and N == 4 and hs != 2:
            bad.append('hStar_pmOne_four')
        M = int(round(N ** 0.5))
        if M * M == N and S == frozenset(d for d in U if d % M in (1 % M, (M - 1) % M)) and hs != M:
            bad.append('hStar_deltaPm_sq')
        gg = gamma_gens(N, S)
        stable = {Q: is_iota_stable(N, S, hs, Q) for Q in exact_divisors(ns)}
        w = sum(stable.values())
        if not stable[1]:
            bad.append('isIotaStable_one')
        if hs == 1:
            # sIota (Part 2): #{Q | N, gcd(Q, N/Q) = 1, forall u: u in Delta <-> exists d in Delta, IsIota N Q d u}
            def is_iota(Q, d, u):
                return (cast(u, Q) * cast(d, Q)) % Q == 1 % Q and cast(u, N // Q) == cast(d, N // Q)
            si = sum(1 for Q in exact_divisors(N)
                     if all((u in S) == any(is_iota(Q, d, u) for d in S) for u in U))
            if si != w:
                bad.append('wStar_eq_sIota')
        hD = hdelta(N, S)
        for Q in exact_divisors(ns):
            if not in_M(conj_Dinv(al_element(ns, Q), hs), N, hD, N // (hD * hD)):
                bad.append('MStar_le_MDelta Q=%d' % Q)
        m = m0 = 0
        for A, n0 in zip(pairs, in0):
            if normalizes(A, gg, N, S):
                m += 1
                m0 += n0
                Q = is_al(conj_D(A, hs), ns)
                if Q is None or not stable[Q]:
                    bad.append('mem_normG_iff (=>)')
        for Q in exact_divisors(ns):
            W = al_element(ns, Q)
            ok = normalizes(conj_Dinv(W, hs), gg, N, S)
            if ok != stable[Q]:
                bad.append('conj_mem_normG_iff Q=%d' % Q)
        for g in [((1, 1), (0, 1)), ((1, 0), (ns, 1)), ((1 + ns, 1), (ns, 1)), ((-1, 0), (0, -1))]:
            assert det(g) == 1
            if not normalizes(conj_Dinv(g, hs), gg, N, S):
                bad.append('Gamma0Star_le_normG')
        idx = len(U) // len(S)
        if Fraction(idx * m) != idx * Fraction(psi(N), psi(ns)) * w:
            bad.append('card_BG')
        if (m == m0) != (hp % hs == 0):
            bad.append('le_Norm0_iff')
        if N == 4 and S == frozenset({1}) and idx * m != 4:
            bad.append('card_4_bot')
        if N == 50 and S == frozenset(d for d in U if d % 5 in (1, 4)) and idx * m != 120:
            bad.append('card_50')
        out.append((N, len(S), hs, ns, w, idx * m, bad))
    return out


def main():
    nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    with Pool(jobs) as P:
        res = P.map(check_level, range(nmin, nmax + 1), chunksize=1)
    rows = [r for lev in res for r in lev]
    fails = [r for r in rows if r[6]]
    for r in fails[:50]:
        print('FAIL', r)
    print('levels %d..%d: %d pairs (N, Delta), %d failures' % (nmin, nmax, len(rows), len(fails)))
    print('card_BG_GammaDeltaR_50:', [r[5] for r in rows if r[0] == 50 and r[1] == 10])
    print('card_BG_GammaDeltaR_4_bot:', [r[5] for r in rows if r[0] == 4 and r[1] == 1])


if __name__ == '__main__':
    main()
