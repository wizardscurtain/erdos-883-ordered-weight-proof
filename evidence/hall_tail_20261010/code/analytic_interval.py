"""Interval-arithmetic replay of ANALYTIC_TAIL_G.md (z = 19, N0 = 1e8, sigma = 1/2, u1 = 9/10, s_low = 4).

Independent of analytic_G.py: written from the document; all real arithmetic uses mpmath interval arithmetic
(directed rounding, 100 bits) or exact rationals/integers. Only upper endpoints of upper bounds and lower endpoints of
lower bounds are used.

Euler products over primes p > z (and over all odd p for M_odd, C_odd):
  log prod (1 + h_s(p) p^{-tau}) with h_s(p) = (1-1/p)^{-s} - 1, tau in {1, sigma}:
   * p <= 1e5: exact interval sum of log1p(h_s(p) p^{-tau});
   * 1e5 < p <= 1e7: log1p(y) <= y and y(p) decreasing in p, so each bucket [a, b) (ratio 1.02) contributes at most
     #primes(bucket) * y(a)  (prime counts exact, from a sieve);
   * p > 1e7: h_s(p) <= 1.001 s/p (s <= 80), sum_{p > X} p^{-1-tau} <= X^{-tau}/tau.
"""
import math, itertools, json, sys
from fractions import Fraction
import numpy as np
from mpmath import iv, mpf

iv.prec = 100
Z, N0, U1, SLOW = 19, 10 ** 8, Fraction(9, 10), 4
SIG = iv.mpf(1) / 2
SGRID = [1, 1.5, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 26, 30, 35, 40, 50, 60, 80]
U_MID = Fraction(33, 100)
STEP = Fraction(5, 10000)
X1, X2 = 10 ** 5, 10 ** 7


def sieve(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, math.isqrt(N) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


PR = sieve(X2)
SMALL = [int(p) for p in PR if p <= X1]
BIG = PR[PR > X1]
BUCKETS = []
_a = X1
while _a < X2:
    _b = min(X2, int(_a * 1.02) + 1)
    _c = int(np.searchsorted(BIG, _b, side="right") - np.searchsorted(BIG, _a, side="right"))
    BUCKETS.append((_a, _c))
    _a = _b
assert sum(c for _, c in BUCKETS) == len(BIG)


def ivs(x):
    if isinstance(x, Fraction):
        return iv.mpf(x.numerator) / x.denominator
    return iv.mpf(x)


def h(s, p):
    return iv.expm1(-ivs(s) * iv.log(1 - iv.mpf(1) / p))


def log_prod_upper(s, zmin, tau):
    """upper endpoint of log prod_{p > zmin} (1 + h_s(p) p^{-tau})."""
    tot = iv.mpf(0)
    for p in SMALL:
        if p <= zmin:
            continue
        tot += iv.log(1 + h(s, p) * iv.mpf(p) ** (-tau))
    # buckets in (X1, X2]
    for a, cnt in BUCKETS:
        if cnt:
            tot += cnt * h(s, a) * iv.mpf(a) ** (-tau)        # y(p) <= y(a) for p in (a, b]
    tot += iv.mpf("1.001") * ivs(s) * iv.mpf(X2) ** (-tau) / tau
    return tot.b


def exact_discrepancy(P, Q):
    ok = np.ones(P + 1, dtype=bool); ok[0] = False
    for p in [2] + Q:
        ok[::p] = False
    C = np.cumsum(ok, dtype=np.int64)
    phi = int(C[P])
    y = np.arange(P + 1, dtype=np.int64)
    num = P * C - phi * y                     # exact integers (< 2^63 here)
    i = int(np.argmax(num))
    return Fraction(int(num[i]), P), Fraction(phi, P)


def main():
    Q = [int(p) for p in PR if 3 <= p <= Z]
    P = 2 * math.prod(Q)
    Dp, kappa = exact_discrepancy(P, Q)
    M = {s: iv.exp(log_prod_upper(s, Z, iv.mpf(1))).b for s in SGRID}
    C = {s: iv.exp(log_prod_upper(s, Z, SIG)).b for s in SGRID}
    errfac = (2 * iv.mpf(N0) ** (SIG - 1)).b
    onefac = Fraction(2, N0)
    classes = []
    for r in range(len(Q) + 1):
        for S in itertools.combinations(Q, r):
            dens, G, prodS = Fraction(1), Fraction(1), 1
            Us = iv.mpf(1)
            for p in Q:
                if p in S:
                    dens /= p; G *= Fraction(p - 1, p); prodS *= p; Us /= (iv.mpf(p) ** SIG - 1)
                else:
                    dens *= Fraction(p - 1, p)
            classes.append((dens, G, prodS, Us.b))

    def Phi_upper(tau):
        """tau: mpf upper value; returns an upper bound for Phi(tau)."""
        tot = iv.mpf(0)
        for dens, G, prodS, Us in classes:
            best = ivs(Fraction(1, prodS) + onefac).b
            cand = (ivs(dens) + ivs(Dp) * Us * errfac).b
            best = min(best, cand)
            Gi = ivs(G)
            if tau < Gi.a:                       # certainly tau < G(S)
                th = (iv.mpf(tau) / Gi).b
                for s in SGRID:
                    val = (iv.mpf(th) ** ivs(s) * (ivs(dens) * M[s] + ivs(Dp) * Us * C[s] * errfac)).b
                    best = min(best, val)
            tot += best
        return tot.b

    # e_sup over primorial intervals
    J, prod, k, g = [], 1, 0, Fraction(1)
    for p in PR[1:60]:
        p = int(p); prod *= p; k += 1; g *= Fraction(p - 1, p)
        J.append((prod, k, g))
    kN = max(kk for P_, kk, gg in J if P_ <= N0)
    def esup(xfun):
        best = iv.mpf(0).b
        for P_, kk, gg in J:
            if kk < kN:
                continue
            left = max(P_, N0)
            best = max(best, (iv.mpf(2) ** kk / iv.sqrt(iv.mpf(xfun(left)))).b)
        return best
    eq = esup(lambda n: 2 * (n // 2))
    en = esup(lambda n: 2 * n)
    delta = Fraction(1, N0 - 1)
    rep = dict(Dp=str(Dp), Dp_float=float(Dp), e_sup_q=float(eq), e_sup_n=float(en))
    # (A1-high)
    worst = None
    u = U_MID
    while u < U1:
        ub = min(U1, u + STEP)
        lhs = (iv.mpf(Phi_upper((iv.mpf(ub.numerator) / ub.denominator + eq).b)) * ivs(1 + delta) + ivs(2 * delta)).b
        rhs = ivs(u * u).a
        mg = rhs - lhs
        if worst is None or mg < worst[0]:
            worst = (mg, float(u))
        u = ub
    rep["A1_high_margin_lower"], rep["A1_high_at"] = float(worst[0]), worst[1]
    # (A1-low)
    Modd = iv.exp(log_prod_upper(SLOW, 2, iv.mpf(1))).b
    Codd = iv.exp(log_prod_upper(SLOW, 2, SIG)).b
    tau_hi = (ivs(U_MID) + eq).b
    lhs_low = (iv.mpf(tau_hi) ** (SLOW - 2) * (iv.mpf(Modd) * ivs(1 + delta) + 2 * ivs(1 + delta) * iv.mpf(N0) ** (SIG - 1) * Codd)).b
    r_sup, inv_sup = iv.mpf(0).b, iv.mpf(0).b
    for P_, kk, gg in J:
        if kk < kN:
            continue
        left = max(P_, N0); q = left // 2
        r_sup = max(r_sup, (iv.mpf(2) ** kk / iv.sqrt(iv.mpf(2 * q)) / ivs(gg)).b)
        inv_sup = max(inv_sup, (1 / (iv.mpf(q) * ivs(gg) ** 2)).b)
    lhs_low_tot = (iv.mpf(lhs_low) + inv_sup).b
    rhs_low = ((1 - iv.mpf(r_sup)) ** 2).a
    rep.update(A1_low_lhs_upper=float(lhs_low_tot), A1_low_rhs_lower=float(rhs_low), A1_low_margin_lower=float(rhs_low - lhs_low_tot),
               A0=bool(r_sup < 1), Modd=float(Modd))
    # (A2')
    eps0 = Fraction(7, 6 * N0)
    worst2 = None
    for i in range(400):
        xa, xb = Fraction(i, 2400), Fraction(i + 1, 2400)      # 400 cells covering [0, 1/6]
        t = (iv.sqrt(ivs(Fraction(1, 2) + eps0 + xb)) + en).b
        lhs = (iv.mpf(Phi_upper(t)) * ivs(1 + delta) - ivs(2 * xa) + ivs(3 * delta)).b
        rhs = ivs(U1 * U1 - Fraction(1, 3)).a
        mg = rhs - lhs
        if worst2 is None or mg < worst2[0]:
            worst2 = (mg, float(xa))
    rep["A2_margin_lower"], rep["A2_at_xi"] = float(worst2[0]), worst2[1]
    rep["ALL_OK"] = bool(worst[0] > 0 and worst2[0] > 0 and rhs_low - lhs_low_tot > 0 and r_sup < 1)
    return rep


if __name__ == "__main__":
    print(json.dumps(main(), indent=1))
