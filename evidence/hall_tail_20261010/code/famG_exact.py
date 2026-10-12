"""Exact-arithmetic replay of the Family G/GA criterion (independent of famG2.py; no shared code).

Every odd v <= N gets the exact integers r = rad(v), f = phi(rad v), w = omega(v), so G(v) = f/r exactly.
Comparisons  G(v) - 2^w/sqrt(2x) <= sqrt(P/Q)  (x, P, Q positive/non-negative integers) are decided by
  X := 2xQ f^2 - 2xP r^2 - 4^w Q r^2,   true  iff  X <= 0  or  X^2 <= 4^(w+1) r^4 (2x) P Q
(squaring is legitimate because f/r > 0 and sqrt(P/Q) + 2^w/sqrt(2x) > 0).  To stay fast, a float64 filter decides
every comparison whose float margin exceeds FILTER; the rest (a tiny fraction) are decided by the integer test.
Float error of the filtered quantities is below 1e-12 relative (one rounding each in f/r, sqrt, division, a few
additions), so FILTER = 1e-9 on Gt - t and a window 1e-12*x + 1e-9 around integers for x*Gt^2 are safe guards.

G-family: kappa(v) = least integer k >= 0 with Gt_x(v) <= sqrt(k/x)  (x = q, or q_lo for blocks);
  Nt(k) = #{kappa <= k};  y1 = 0 if Nt(0) > 0 else min{k >= 1 : Nt(k) >= k}.
GA-family: N_GA = #{v : Gt_y(v) <= sqrt(P/Q)} with y = n (or Nlo), P/Q = (n-T+2m-1)/n (or 1/3 + 7/(6Nlo) + (2m_hi-1)/Nlo).
Criterion: N_GA <= y1 - m (resp. m_hi).
"""
import sys, json, math, time
from fractions import Fraction
import numpy as np

FILTER = 1e-9


def arrays(N):
    nv = (N + 1) // 2
    rad = np.ones(nv, dtype=np.int64)
    phr = np.ones(nv, dtype=np.int64)
    w = np.zeros(nv, dtype=np.int8)
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, math.isqrt(N) + 1):
        if s[i]:
            s[i * i::i] = False
    for p in np.nonzero(s)[0]:
        p = int(p)
        if p == 2:
            continue
        sl = slice((p - 1) // 2, nv, p)
        rad[sl] *= p
        phr[sl] *= (p - 1)
        w[sl] += 1
    return rad, phr, w


def le_exact(f, r, w, x, P, Q):
    X = 2 * x * Q * f * f - 2 * x * P * r * r - (4 ** w) * Q * r * r
    return X <= 0 or X * X <= (4 ** (w + 1)) * (r ** 4) * 2 * x * P * Q


def kappa_all(rad, phr, w, x):
    """exact kappa(v) for every v (vectorised float + exact fix-up)."""
    G = phr / rad
    e = np.power(2.0, w) / math.sqrt(2 * x)
    Gt = G - e
    kf = x * np.square(np.maximum(Gt, 0.0))
    kap = np.ceil(kf).astype(np.int64)
    kap[Gt <= 0] = 0
    # borderline: Gt near 0, or x*Gt^2 near an integer
    frac = kf - np.floor(kf)
    border = (np.abs(Gt) < FILTER) | (np.minimum(frac, 1 - frac) < 1e-12 * x + FILTER)   # float error of kf <= ~3e-15*x
    idx = np.nonzero(border)[0]
    for i in idx:
        f, r, ww = int(phr[i]), int(rad[i]), int(w[i])
        # least k >= 0 with le_exact(..., k, x): start just below the float estimate
        k = max(0, int(kf[i]) - 2)
        while not le_exact(f, r, ww, x, k, x):
            k += 1
        # k is minimal provided le_exact(k-1) is false (check, walking down if needed)
        while k > 0 and le_exact(f, r, ww, x, k - 1, x):
            k -= 1
        kap[i] = k
    return kap, len(idx)


def y1_from_kappa(kap, nodd):
    if (kap == 0).any():
        return 0
    cnt = np.bincount(np.minimum(kap, nodd + 1), minlength=nodd + 2)
    cum = np.cumsum(cnt)
    k = np.arange(len(cum))
    ok = (k >= 1) & (cum >= k)
    return int(np.argmax(ok)) if ok.any() else nodd + 1


def count_le(rad, phr, w, y, P, Q):
    G = phr / rad
    Gt = G - np.power(2.0, w) / math.sqrt(2 * y)
    t = math.sqrt(P / Q)
    d = Gt - t
    sure_le = d < -FILTER
    border = np.abs(d) <= FILTER
    c = int(np.count_nonzero(sure_le))
    for i in np.nonzero(border)[0]:
        if le_exact(int(phr[i]), int(rad[i]), int(w[i]), y, P, Q):
            c += 1
    return c, int(np.count_nonzero(border))


def params(n):
    return n // 2, n // 6, n // 3 - n // 6, n // 2 + n // 3 - n // 6, (n + 1) // 2


def check_n(n, A):
    q, m, h, T, nodd = params(n)
    rad, phr, w = (a[:nodd] for a in A)
    kap, nb1 = kappa_all(rad, phr, w, q)
    y1 = y1_from_kappa(kap, nodd)
    P, Q = n - T + 2 * m - 1, n
    NGA, nb2 = count_le(rad, phr, w, n, P, Q)
    return dict(n=n, y1=y1, NGA=NGA, m=m, ok=NGA <= y1 - m, border=nb1 + nb2)


def check_block(Nlo, Nhi, A, chunk=4_000_000):
    qlo, _, _, _, _ = params(Nlo)
    _, mhi, _, _, nodd = params(Nhi)
    R = Fraction(1, 3) + Fraction(7, 6 * Nlo) + Fraction(2 * mhi - 1, Nlo)
    cnt = np.zeros(nodd + 2, dtype=np.int64)
    NGA = nb = 0
    for a in range(0, nodd, chunk):
        b = min(nodd, a + chunk)
        rad, phr, w = (x[a:b] for x in A)
        kap, nb1 = kappa_all(rad, phr, w, qlo)
        cnt += np.bincount(np.minimum(kap, nodd + 1), minlength=nodd + 2)
        c, nb2 = count_le(rad, phr, w, Nlo, R.numerator, R.denominator)
        NGA += c; nb += nb1 + nb2
    if cnt[0] > 0:
        y1 = 0
    else:
        cum = np.cumsum(cnt); k = np.arange(len(cum)); ok = (k >= 1) & (cum >= k)
        y1 = int(np.argmax(ok)) if ok.any() else nodd + 1
    return dict(Nlo=Nlo, Nhi=Nhi, y1=y1, NGA=NGA, mhi=mhi, ok=NGA <= y1 - mhi, border=nb)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "pern":
        lo, hi, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        A = arrays(hi)
        with open(out, "w") as fh:
            for n in range(lo, hi + 1):
                fh.write(json.dumps(check_n(n, A)) + "\n")
    else:
        blocks = [json.loads(l) for l in open(sys.argv[2])]
        out = sys.argv[3]
        A = arrays(blocks[-1]["Nhi"])
        with open(out, "w") as fh:
            for b in blocks:
                t = time.time()
                r = check_block(b["Nlo"], b["Nhi"], A)
                r["sec"] = round(time.time() - t, 2)
                fh.write(json.dumps(r) + "\n"); fh.flush()
