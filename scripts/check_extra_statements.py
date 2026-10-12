"""Numerical checks of the 2026-10-09 additions.
 H  for N ≤ NMAX and every subgroup Δ ≤ (Z/N)^x (with or without −1): h_Δ = h(N) ⟺ none of i)–iii).
 S  for N ≤ SMAX: the matrices σH (σ over aut_orders' representatives of Γ₀(N)\\SL₂(Z), H Hermite with
    det | N) lie in pairwise distinct cosets Γ₀(N)·(scalar), checked by the integrality test
    (σH)(σ'H')⁻¹ ∈ ℚ^× Γ₀(N)  ⟺  some rational multiple of σH·adj(σ'H') is in Γ₀(N).
Run: python3 scripts/check_extra_statements.py"""
import sys
from math import gcd
from fractions import Fraction
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import aut_orders as ao

def all_subgroups(N):
    U = [a for a in range(1, N) if gcd(a, N) == 1] if N > 1 else [0]
    start = frozenset({1 % N})
    seen, todo = {start}, [start]
    while todo:
        S = todo.pop()
        for a in U:
            if a not in S:
                T = ao.closure_add(S, a, N)
                if T not in seen:
                    seen.add(T); todo.append(T)
    return seen

def hD(N, S):
    eps = N
    for d in S: eps = gcd(eps, d * d - 1)
    h = 1
    for p, k in ao.factor(N).items(): h *= p ** min(ao.vp(eps, p), k // 2)
    return h

def h24(N): return max(h for h in ao.divisors(24) if N % (h * h) == 0)

def pm(m, d): return d % m in (1 % m, (m - 1) % m)

bad = tested = 0
for N in range(1, 301):
    f = ao.factor(N)
    for S in all_subgroups(N):
        tested += 1
        c1 = any(p >= 5 and k >= 2 and all(pm(p, d) for d in S) for p, k in f.items())
        c2 = N % 81 == 0 and all(pm(9, d) for d in S)
        c3 = N % 256 == 0 and all(pm(8, d) for d in S)
        if (hD(N, S) == h24(N)) != (not (c1 or c2 or c3)):
            bad += 1; print("H FAIL", N, sorted(S))
print("H: %d subgroups, N <= 300, failures %d" % (tested, bad))

def same_coset(A, B, N):
    # is A B^{-1} a rational multiple of an element of Gamma0(N)?  A adj(B) = det(B) A B^{-1}
    M = ao.mul(A, ao.adj(B))
    e = [M[0][0], M[0][1], M[1][0], M[1][1]]
    g = 0
    for x in e: g = gcd(g, x)
    q = [x // g for x in e]
    det = q[0] * q[3] - q[1] * q[2]
    if det not in (1, -1) or det < 0 and False: return False
    if det != 1: return False
    return q[2] % N == 0

bad = 0
for N in range(1, 25):
    reps = ao.p1_reps(N)
    pairs = [ao.mul(s, H) for s in reps for H in ao.hnfs(N)]
    for i in range(len(pairs)):
        for j in range(i):
            if same_coset(pairs[i], pairs[j], N):
                bad += 1; print("S FAIL", N, pairs[i], pairs[j])
print("S: N <= 24, coincidences %d" % bad)
