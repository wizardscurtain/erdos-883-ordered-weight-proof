"""Family G (multiplicative zigzag) — exploratory implementation.

Skeleton: Y0 = h+1 largest-Gt vertices of Y (Y = odd part of A, |Y| = h+1+b); coprime pair a,a' in Y0 (L1);
internal vertices o_1..o_{l-1} = the l-1 largest-Gt vertices of Y0 - {a,a'}, sorted decreasingly;
path a, o_1, ..., o_{l-1}, a'.  Lists: even 2k in A with gcd(k, o o') = 1.
  |L(o,o')| >= #{k<=q : gcd(k, rad(oo'))=1} - b >= q*G(o)G(o') - 2^{w(o)+w(o')-1} - b,
  G(v) = prod_{p | v} (1-1/p)  (all primes of v, v odd),  w = number of distinct prime factors.
  With e(v) = 2^{w(v)}/sqrt(2q), Gt = G - e:  bad at rank j  =>  min(Gt(o), Gt(o')) <= t_j, t_j^2 = (b+j-1)/q
  (if Gt(v) <= 0 the vertex counts as bad for every j).
  In the sorted path every bad gap has an endpoint in W_j = {Gt <= t_j}; the map gap -> later endpoint is injective
  except possibly for the last gap, so #bad_j <= w_j + [w_j > 0], w_j = #(V cap W_j) <= (N(t_j) - b)^+  (L4 with
  cost -Gt), N(t) = #{odd v <= n : Gt(v) <= t}.
Certificate G(b,l): for all 1 <= j <= l:  w_j + [w_j>0] <= j-1.
"""
import sys, json, math
import numpy as np


def tables(n):
    v = np.arange(1, n + 1, 2, dtype=np.int64)
    nv = len(v)
    logG = np.zeros(nv)
    om = np.zeros(nv, dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    for p in np.nonzero(sieve)[0]:
        if p == 2:
            continue
        idx = slice((p - 1) // 2, nv, p)          # odd multiples of p
        logG[idx] += math.log1p(-1.0 / p)
        om[idx] += 1
    return v, np.exp(logG), om


def lG_profile(n, extra_err=1.0):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    v, G, om = tables(n)
    e = (2.0 ** om) / math.sqrt(2 * q) * extra_err
    Gt = G - e
    s = np.sort(Gt)
    nodd = len(v)
    bmax = nodd - h - 1
    out = np.zeros(bmax + 1, dtype=np.int64)
    for b in range(bmax + 1):
        j = np.arange(1, m + 1)
        t = np.sqrt((b + j - 1) / q)
        N = np.searchsorted(s, t, side="right")          # #{Gt <= t}
        w = np.minimum(m + 1, np.maximum(0, N - b))
        ok = (w + (w > 0)) <= (j - 1)
        out[b] = m if ok.all() else int(np.argmin(ok))
    return dict(n=n, m=m, h=h, bmax=bmax, lG=out, Gmin=float(G.min()), Gtmin=float(Gt.min()))


if __name__ == "__main__":
    for n in [int(x) for x in sys.argv[1:]]:
        P = lG_profile(n)
        lG, m = P["lG"], P["m"]
        full = np.nonzero(lG >= m)[0]
        print(json.dumps(dict(n=n, m=m, bmax=P["bmax"], Gmin=round(P["Gmin"], 4), Gtmin=round(P["Gtmin"], 4),
                              b_full_lo=int(full.min()) if len(full) else None, b_full_hi=int(full.max()) if len(full) else None,
                              n_full=int(len(full)), min_lG=int(lG.min()), argmin_b=int(lG.argmin()),
                              lG_at=[int(lG[int(f * P["bmax"])]) for f in (0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0)])))


def lGA_profile(n, P=None):
    """Family GA: as G but connectors are any unused vertices of A (lists u in A - V, gcd(u, oo') = 1).
    |L| >= n G G' - 2^{w+w'-1} - (n - T + l);  e(v) = 2^w/sqrt(2n);  t_j^2 = (n - T + l + j - 1)/n.
    GA(b,l) is monotone in l; returns lGA[b] = max l (0..m) with GA(b,l)."""
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    v, G, om = tables(n)
    Gt = G - (2.0 ** om) / math.sqrt(2 * n)
    s = np.sort(Gt)
    nodd = len(v)
    bmax = nodd - h - 1
    out = np.zeros(bmax + 1, dtype=np.int64)
    def ok(b, l):
        j = np.arange(1, l + 1)
        t = np.sqrt((n - T + l + j - 1) / n)
        N = np.searchsorted(s, t, side="right")
        w = np.maximum(0, N - b)
        return bool(np.all(w + (w > 0) <= j - 1))
    for b in range(bmax + 1):
        if ok(b, m):
            out[b] = m; continue
        lo, hi = 0, m        # ok(lo) True (vacuous at l=0), ok(hi) False
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ok(b, mid): lo = mid
            else: hi = mid
        out[b] = lo
    return out


def combined(n):
    P = lG_profile(n)
    lG = P["lG"]; m = P["m"]
    lGA = lGA_profile(n)
    best = np.maximum(lG, lGA)
    unc = np.nonzero(best < m)[0]
    return dict(n=n, m=m, bmax=P["bmax"], n_unc_b=int(len(unc)), unc_b=[(int(b), int(lG[b]), int(lGA[b])) for b in unc[:8]],
                GA_full_from=int(np.nonzero(lGA >= m)[0].min()) if (lGA >= m).any() else None,
                G_full_upto=int(np.nonzero(lG >= m)[0].max()) if (lG >= m).any() else None)
