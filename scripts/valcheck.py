# Does the valuation abstraction of "B normalizes L'" imply Newman's local form?
INF = 10**6
def jk(p, nu):
    j = min(nu, 3) if p == 2 else (min(nu, 1) if p == 3 else 0)
    k = min(j, nu // 2)
    return j, k
def ok(p, nu, a, b, c, d, D):
    j, k = jk(p, nu); e2 = 1 if p == 2 else 0
    def v(*xs):  # valuation of a product
        return INF if any(x >= INF for x in xs) else sum(xs)
    conds = [
      k + v(a, c) - D >= 0, 2*a >= D if a < INF else True, (2*c >= D + nu - 2*k) if c < INF else True,
      (e2 + k + v(a, c) - D >= j),
      nu - k + v(b, d) - D >= 0, (2*b >= D - (nu - 2*k)) if b < INF else True, (2*d >= D) if d < INF else True,
      (e2 + nu - k + v(b, d) - D >= j),
      j + v(b, c) - D >= 0, j + v(a, b) - D >= k, j + v(c, d) - D >= nu - k, (e2 + v(b, c) >= D),
      k + v(c, d) - D >= 0, e2 + k + v(c, d) - D >= j,
      nu - k + v(a, b) - D >= 0, e2 + nu - k + v(a, b) - D >= j,
      j + v(b, d) - D >= k, j + v(a, c) - D >= nu - k,
    ]
    return all(conds)
def ultra(a, b, c, d, D):
    ad = INF if (a >= INF or d >= INF) else a + d
    bc = INF if (b >= INF or c >= INF) else b + c
    if ad >= INF and bc >= INF: return False
    if ad != bc: return D == min(ad, bc)
    return D >= ad
def goal(p, nu, a, b, c, d, D):
    j, k = jk(p, nu); nup = nu - 2*k
    return (D == 0 and c >= nup) or (D == nup and a >= nup and c >= nup and d >= nup)
bad = []
R = list(range(0, 9)) + [INF]
for p in (2, 3, 5):
    for nu in range(0, 10):
        for a in R:
            for b in R:
                for c in R:
                    for d in R:
                        if min(a, b, c, d) != 0: continue
                        for D in range(0, 20):
                            if not ultra(a, b, c, d, D): continue
                            if ok(p, nu, a, b, c, d, D) and not goal(p, nu, a, b, c, d, D):
                                bad.append((p, nu, a, b, c, d, D))
print(len(bad)); print(bad[:20])
