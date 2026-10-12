"""Exploratory density-bound version of Family E (refined costs) in the limit n -> infinity.

All counts are expressed as fractions of the number of odd integers (~3m). beta0 ~ 2m, Delta ~ m, q ~ 3m.
Normalised costs (divide by beta0):
  O3 vertex, signature S, large-prime reciprocal sum X:  c3 = (1-R(S)) + 2*R(S)*X
  C  vertex:  cd = (3/2)(1-R(S)) + 3*R(S)*X - d          (d = delta/beta0 in [0, 1/2])
  rho/beta0 <= (1-R(S)) + R(S)*X                           (both types; 3-free even loss)
Densities: among odd integers, P(3|v) = 1/3; signature S exactly: prod_{p in S} 1/p * prod_{p in P\S}(1-1/p).
Large-prime part: tail bound P(X >= y) <= min_s exp(-s y) * M(s), M(s) = prod_{p>=17, p notin P} (1 + (e^{s/p}-1)/p)
(an upper bound for the limiting distribution; finite-n corrections are O(sqrt(N)) and handled later).
Certificate at normalised budget beta = b/m and rank x = j/m (theta = beta0 - b - j -> 1 - (beta+x)/2):
  within <= min(abs_w, tail_w - beta) where abs_w = 3*Pr(rough), tail_w = 3*Pr(cost >= theta) (O3 part) etc.
We report the smallest slack x - bad/m over a grid, ignoring O(K/m) boundary caps (which matter only at small x).
"""
import math, sys
import numpy as np

P = (5, 7, 11, 13)


def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]


PR = [int(p) for p in primes_upto(2_000_000) if p >= 17 and p not in P]


def logM(s):
    # log prod (1 + (e^{s/p}-1)/p) over primes 17..2e6, plus tail bound sum_{p>2e6} (e^{s/p}-1)/p <= e^{s/2e6} s * sum 1/p^2
    tot = 0.0
    for p in PR:
        tot += math.log1p(math.expm1(s / p) / p)
    tot += math.exp(s / 2e6) * s * (1.0 / 2e6)   # crude tail: sum_{p>N} 1/p^2 <= 1/N
    return tot


SGRID = [0.5, 1, 2, 3, 5, 8, 12, 18, 25, 35, 50, 70, 100, 140]
LOGM = {s: logM(s) for s in SGRID}


def tailX(y):
    """upper bound on P(X >= y)."""
    if y <= 0:
        return 1.0
    return min(1.0, min(math.exp(-s * y + LOGM[s]) for s in SGRID))


def sigs():
    out = []
    for mask in range(1 << len(P)):
        S = [p for i, p in enumerate(P) if mask >> i & 1]
        R = 1.0
        dens = 1.0
        for p in P:
            if p in S:
                R *= (1 - 1 / p); dens *= 1 / p
            else:
                dens *= (1 - 1 / p)
        out.append((tuple(S), R, dens))
    return out


SIGS = sigs()


def frac_cost_ge(t, d):
    """upper bound on fraction of odd v with normalised cost >= t (O3 cost c3; C cost cd)."""
    f = 0.0
    for S, R, dens in SIGS:
        # O3 (prob 1/3): (1-R) + 2R X >= t  <=>  X >= (t-(1-R))/(2R)
        f += (1 / 3) * dens * tailX((t - (1 - R)) / (2 * R))
        # C (prob 2/3 among odd, minus divisible-by-3 already excluded): 1.5(1-R)+3RX-d >= t
        f += (2 / 3) * dens * tailX((t + d - 1.5 * (1 - R)) / (3 * R))
    return f


def frac_within_rough(theta, d):
    """O3: c3 >= theta ; C: cd >= theta + 1/2 - d (Delta/beta0 = 1/2)."""
    f = 0.0
    for S, R, dens in SIGS:
        f += (1 / 3) * dens * tailX((theta - (1 - R)) / (2 * R))
        f += (2 / 3) * dens * tailX((theta + 0.5 - 1.5 * (1 - R)) / (3 * R))
    return f


def frac_rho_ge(t):
    f = 0.0
    for S, R, dens in SIGS:
        f += dens * tailX((t - (1 - R)) / R)
    return f


def check(beta, d, gr):
    """min slack over x in (0,1] of: x - within/m - boundary/m (boundary uses 2*count, no cap)."""
    worst = 1e9
    for x in np.linspace(0.01, 1.0, 100):
        theta = 1 - (beta + x) / 2                          # normalised theta (beta0 = 2m)
        # counts in units of m: odd count = 3m
        tail_w = 3 * frac_cost_ge(theta, d)                 # tau_w(theta) >= theta for O3, shifted for C -> conservative
        abs_w = 3 * frac_within_rough(theta, d)
        within = min(abs_w, max(0.0, tail_w - beta))
        # boundary: rough by rho >= theta - gr ; tau >= theta - gr - d (cd >= rho - d)
        tail_b = 3 * frac_cost_ge(theta - gr - d, d)
        abs_b = 3 * frac_rho_ge(theta - gr)
        bnd = 2 * min(abs_b, max(0.0, tail_b - beta))
        slack = x - within - bnd
        worst = min(worst, slack)
    # separators: need 3*frac_rho_ge(gr) <= h/m = 1 (minus K/m), as a check (absolute count)
    sep_ok = 3 * frac_rho_ge(gr) < 1.0 or (3 * frac_cost_ge(gr - d, d) - beta) < 1.0
    return worst, sep_ok


if __name__ == "__main__":
    for beta in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2]:
        best = None
        for d in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5]:
            for gr in [0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3]:
                w, ok = check(beta, d, gr)
                if ok and (best is None or w > best[0]):
                    best = (w, d, gr)
        print(f"beta={beta:.1f}: best min slack over x in [0.01,1] = {best[0]:.4f} (d={best[1]}, gr={best[2]})")
