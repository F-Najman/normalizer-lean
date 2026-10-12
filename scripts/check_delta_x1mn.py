"""Check of X_Δ(N) ≅ X₁(M, N/M): M² ∣ N, Δ = {d : d ≡ ±1 mod N/M}.  Conjugation by D = diag(M, 1),
γ ↦ DγD⁻¹ = [[a, Mb], [c/M, d]], maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)).  Exhaustive over integer
matrices with entries in [-B, B] (both inclusions).  Run: python3 scripts/check_delta_x1mn.py"""
from itertools import product
from math import gcd

B = 40
LEVELS = [(1, 1), (1, 6), (2, 4), (2, 8), (2, 12), (2, 16), (3, 9), (3, 18), (3, 27), (4, 16), (4, 32), (5, 25), (6, 36)]


def in_GammaDelta(g, N, M):
    a, b, c, d = g
    K = N // M
    return a * d - b * c == 1 and c % N == 0 and (d % K in (1 % K, (-1) % K))


def in_pm(g, M, K):
    a, b, c, d = g
    if a * d - b * c != 1:
        return False
    for s in (1, -1):
        A, Bb, C, D = s * a, s * b, s * c, s * d
        if (A - 1) % M == 0 and Bb % M == 0 and C % M == 0 and (D - 1) % M == 0 and C % K == 0 and (D - 1) % K == 0:
            return True
    return False


ok = True
for M, N in LEVELS:
    K = N // M
    n1 = n2 = 0
    for a, b, c, d in product(range(-B, B + 1), repeat=4):
        if a * d - b * c != 1:
            continue
        g = (a, b, c, d)
        if in_GammaDelta(g, N, M):          # image is integral since M ∣ N ∣ c
            n1 += 1
            if not in_pm((a, M * b, c // M, d), M, K):
                ok = False; print("FAIL image", M, N, g)
        if in_pm(g, M, K):                  # preimage D⁻¹gD = [[a, b/M], [Mc, d]]
            n2 += 1
            if b % M or not in_GammaDelta((a, b // M, M * c, d), N, M):
                ok = False; print("FAIL preimage", M, N, g)
    print("M=%d N=%d: %d elements of Gamma_Delta(N), %d of +-(Gamma(M) cap Gamma1(N/M)) tested" % (M, N, n1, n2))
print("ALL OK" if ok else "FAILURES")
