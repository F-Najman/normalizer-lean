"""Numerical sanity checks of the Stage-0 statements of the Γ_Δ / Γ(N) / Γ₁(N) project.

Uses the coset machinery of scripts/aut_orders.py.  A normalizing coset Γ₀(N)A is represented by A = σH, with σ
running over Γ₀(N)\\SL₂(Z) and H over Hermite forms.

Checks:
 K  Δ = {±1}, 1 ≤ N ≤ NMAX: every normalizing σH (det | N) lies in Γ₀(N)⁺, and the number of
    normalizing cosets is 2^ω(N) (so [Nor : ±Γ₁(N)] = 2^ω(N) φ(N)/2), except at N = 4.
 X  M ≤ MMAX, N = M², Δ = {d ≡ ±1 mod M}: [Nor(Γ_Δ(N)) : Γ_Δ(N)] = #SL₂(Z/M)/#{±1}.
    (Conjugation by diag(M, 1) maps Γ_Δ(M²) onto ±Γ(M).)
 D  N ≤ DMAX, all Δ ∋ −1: every normalizing σH with det(H) ≤ EFAC·N² (not only det | N) has
    the form of the generalized Newman bound (in_M with h_Δ, n_Δ).  This does not presuppose det | N.

Run: nice -n 10 python3 scripts/check_delta_statements.py [NMAX MMAX DMAX EFAC JOBS]
(output of `400 18 30 2 6`, about 10 min: scripts/check_delta_statements_output.txt)
"""
import sys
from math import gcd
from multiprocessing import Pool

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import aut_orders as ao  # noqa: E402


def omega(n):
    return len(ao.factor(n)) if n > 1 else 0


def phi(n):
    return sum(1 for a in range(1, n + 1) if gcd(a, n) == 1)


def eps_h_n(N, S):
    eps = N
    for d in S:
        eps = gcd(eps, d * d - 1)
    hD = 1
    for p, k in ao.factor(N).items():
        hD *= p ** min(ao.vp(eps, p), k // 2)
    return eps, hD, N // (hD * hD)


def hnfs_upto(E):
    out = []
    for e in range(1, E + 1):
        for a in ao.divisors(e):
            d = e // a
            for b in range(d):
                if gcd(gcd(a, b), d) == 1:
                    out.append(((a, b), (0, d)))
    return out


def candidates(N, Hs):
    """The sigma H passing the necessary condition `apriori` (from g L g^-1 = L)."""
    return [A for A in (ao.mul(s, H) for s in ao.p1_reps(N) for H in Hs) if ao.apriori(A, N)]


def normalizing(N, S, gens, Hs, cand=None):
    gg = ao.gamma_gens(N, gens)
    if cand is None:
        cand = candidates(N, Hs)
    return [A for A in cand if ao.normalizes(A, gg, N, S)]


def check_K(N):
    if N <= 2:
        return (N, "trivial", True)
    S = frozenset({1, N - 1})
    gens = ao.small_gens(S, N)
    A = normalizing(N, S, gens, ao.hnfs(N))
    inPlus = all(ao.in_M(x, N, 1, N) for x in A)
    m = len(A)
    ok = inPlus and m == 2 ** omega(N)
    return (N, m, 2 ** omega(N), inPlus, ok)


def check_X(M):
    N = M * M
    S = frozenset(d for d in range(1, N) if gcd(d, N) == 1 and (d % M in (1 % M, (M - 1) % M)))
    gens = ao.small_gens(S, N)
    m = len(normalizing(N, S, gens, ao.hnfs(N)))
    idx = phi(N) // len(S)
    sl = M ** 3
    for p in ao.factor(M):
        sl = sl * (p * p - 1) // (p * p)
    psl = sl // (2 if M >= 3 else 1)
    return (M, idx * m, psl, idx * m == psl)


def check_D(args):
    N, efac = args
    Hs = hnfs_upto(efac * N * N)
    cand = candidates(N, Hs)
    bad, count = [], 0
    for S in ao.subgroups_with_minus1(N):
        gens = ao.small_gens(S, N)
        eps, hD, nD = eps_h_n(N, S)
        A = normalizing(N, S, gens, Hs, cand)
        count += 1
        for x in A:
            if not ao.in_M(x, N, hD, nD):
                bad.append((sorted(S), x))
    return (N, count, bad)


def main():
    a = [int(x) for x in sys.argv[1:]]
    NMAX, MMAX, DMAX, EFAC, JOBS = (a + [200, 20, 30, 2, 4][len(a):])[:5]
    with Pool(JOBS) as pool:
        K = pool.map(check_K, range(1, NMAX + 1))
        X = pool.map(check_X, range(2, MMAX + 1))
        D = pool.map(check_D, [(N, EFAC) for N in range(2, DMAX + 1)])
    print("== K: Delta = {+-1}, N <= %d" % NMAX)
    for r in K:
        if not r[-1] or r[0] == 4:
            print("  exception/fail:", r)
    print("  K ok for all N <= %d except: %s" % (NMAX, [r[0] for r in K if not r[-1]]))
    print("== X: N = M^2, Delta = +-1 mod M, M <= %d" % MMAX)
    for r in X:
        print("  M=%d  [Nor:Gamma_Delta]=%d  #PSL2(Z/M)=%d  %s" % r)
    print("== D: all Delta, N <= %d, det(H) <= %d N^2" % (DMAX, EFAC))
    nbad = sum(len(r[2]) for r in D)
    print("  subgroups tested: %d, matrices outside M_Delta: %d" % (sum(r[1] for r in D), nbad))
    for r in D:
        for b in r[2][:3]:
            print("  BAD", r[0], b)
    print("DONE")


if __name__ == "__main__":
    main()
