"""Numerical checks of the Stage-0 additions (Nor(Γ_Δ) ≤ Nor(Γ₀) and the index, the S₇ example, Γ₀ ≤ Nor(Γ_Δ)).

For 1 ≤ N ≤ NMAX and every Δ ≤ (Z/N)^x containing −1 (as in aut_orders.py):
 P1  if h_Δ = h(N), every normalizing coset of Γ_Δ(N) lies in Nor(Γ₀(N))       (normG_GammaDeltaR_le_Norm0)
 P2  if moreover 4 ∤ N and 9 ∤ N: the number of normalizing Γ₀(N)-cosets equals
     #{Q ∥ N : ι_Q(Δ) = Δ}, ι_Q(d) ≡ d⁻¹ mod Q, ≡ d mod N/Q                  (sDelta_eq_sIota)
 G0  Γ₀(N) normalizes Γ_Δ(N) (the identity coset is always counted)
Also: S₇ = [[1, 1/7], [0, 1]] (scaled [[7, 1], [0, 7]]) normalizes Γ_Δ(49), Δ = ±1 mod 7, and does not
normalize Γ₀(49).
Run: nice -n 10 python3 scripts/check_delta_index.py [NMAX JOBS]   (output: _output.txt next to it)
"""
import sys
from math import gcd
from multiprocessing import Pool

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import aut_orders as ao  # noqa: E402


def eps_h_n(N, S):
    eps = N
    for d in S:
        eps = gcd(eps, d * d - 1)
    hD = 1
    for p, k in ao.factor(N).items():
        hD *= p ** min(ao.vp(eps, p), k // 2)
    return hD


def iota(N, Q, d):
    """the unit u mod N with u ≡ d^-1 mod Q and u ≡ d mod N/Q (brute force)."""
    R = N // Q
    for u in range(N):
        if gcd(u, N) == 1 and (u * d) % Q == 1 % Q and (u - d) % R == 0:
            return u
    raise ValueError


def run(N):
    if N == 1:
        return (N, 0, [], 0, 0, 0)
    h24 = max(h for h in ao.divisors(24) if N % (h * h) == 0)
    reps = ao.p1_reps(N)
    cand = [ao.mul(s, H) for s in reps for H in ao.hnfs(N)]
    cand = [A for A in cand if ao.apriori(A, N)]
    full = frozenset(u for u in range(1, N) if gcd(u, N) == 1)
    g0 = ao.gamma_gens(N, ao.small_gens(full, N))
    n0 = [ao.normalizes(A, g0, N, full) for A in cand]
    exact = [Q for Q in ao.divisors(N) if gcd(Q, N // Q) == 1]
    bad, tested, nP1, nP2, negP1 = [], 0, 0, 0, 0
    for S in ao.subgroups_with_minus1(N):
        gg = ao.gamma_gens(N, ao.small_gens(S, N))
        norm = [ao.normalizes(A, gg, N, S) for A in cand]
        tested += 1
        if not ao.normalizes(((1, 0), (0, 1)), gg, N, S):
            bad.append(("G0", sorted(S)))
        hD = eps_h_n(N, S)
        m = sum(norm)
        m0 = sum(1 for a, b in zip(norm, n0) if a and b)
        if hD == h24:
            nP1 += 1
        elif m != m0:
            negP1 += 1      # known positives for the test: h_Δ ≠ h(N) and Nor(Γ_Δ) ⊄ Nor(Γ₀)
        if hD == h24 and m != m0:
            bad.append(("P1", sorted(S), m, m0))
        if hD == h24 and N % 4 and N % 9:
            nP2 += 1
            s = sum(1 for Q in exact if frozenset(iota(N, Q, d) for d in S) == S)
            if s != m:
                bad.append(("P2", sorted(S), m, s))
    return (N, tested, bad, nP1, nP2, negP1)


def s7():
    N = 49
    S = frozenset(d for d in range(1, N) if gcd(d, N) == 1 and d % 7 in (1, 6))
    gg = ao.gamma_gens(N, ao.small_gens(S, N))
    full = frozenset(u for u in range(1, N) if gcd(u, N) == 1)
    g0 = ao.gamma_gens(N, ao.small_gens(full, N))
    A = ((7, 1), (0, 7))
    return ao.normalizes(A, gg, N, S), ao.normalizes(A, g0, N, full)


def main():
    a = [int(x) for x in sys.argv[1:]]
    NMAX, JOBS = (a + [200, 6][len(a):])[:2]
    with Pool(JOBS) as pool:
        R = pool.map(run, range(1, NMAX + 1))
    print("N <= %d: subgroups tested %d, failures %d" % (NMAX, sum(r[1] for r in R), sum(len(r[2]) for r in R)))
    print("  P1 tested on %d subgroups (h_Delta = h(N)); P2 on %d (also 4, 9 not dividing N)" %
          (sum(r[3] for r in R), sum(r[4] for r in R)))
    print("  validation: %d subgroups with h_Delta != h(N) have Nor(Gamma_Delta) not in Nor(Gamma_0), at N = %s" %
          (sum(r[5] for r in R), [r[0] for r in R if r[5]][:12]))
    for r in R:
        for b in r[2]:
            print("  FAIL", r[0], b)
    print("S7 normalizes Gamma_Delta(49) (Delta = +-1 mod 7): %s; normalizes Gamma0(49): %s" % s7())
    print("DONE")


if __name__ == "__main__":
    main()
