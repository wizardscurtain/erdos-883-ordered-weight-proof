"""Fast per-n and block checks for Families G and GA (see FAMILY_G.md for the lemma).

Notation: for odd v, G(v) = prod_{p|v}(1-1/p), w(v) = #distinct primes.
  G-family uses Gt_q(v) = G(v) - 2^{w(v)}/sqrt(2q);   GA-family uses Gt_n(v) = G(v) - 2^{w(v)}/sqrt(2n).
  Nt(y) = #{odd v <= n : Gt_q(v) <= sqrt(y/q)}.
  y1 = min{ y >= 1 : Nt(y) >= y }  (= nodd+1 if none); y1 = 0 if Nt(0) > 0.
  Family G certifies every (b,l) with b + l <= y1        [G(b,l) <=> Nt(b) <= b and Nt(y) <= y-1 on (b, b+l-1]]
  Family GA certifies every (b,l), l <= m, with b >= N_GA := #{odd v <= n : Gt_n(v) <= sqrt((n-T+2m-1)/n)}.
  Full coverage of n:  N_GA <= y1 - m.
Block [Nlo,Nhi]: counts over odd v <= Nhi with e computed at Nlo (larger e), thresholds sqrt(y/q_lo) and
  sqrt(1/3 + 7/(6 Nlo) + (2 m_hi - 1)/Nlo); full coverage of every n in the block if N_GA^+ <= y1^+ - m_hi.
"""
import sys, json, math, time
import numpy as np

_T = {}
SAFETY = 1e-9      # floating-point guard: every comparison is shifted in the conservative direction


def tables(N):
    """G and w for odd v <= N (index i <-> v = 2i+1); cached and extended."""
    if "N" in _T and _T["N"] >= N:
        k = (N + 1) // 2
        return _T["G"][:k], _T["w"][:k]
    v = np.arange(1, N + 1, 2, dtype=np.int64)
    nv = len(v)
    logG = np.zeros(nv)
    w = np.zeros(nv, dtype=np.int8)
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    for p in np.nonzero(sieve)[0][1:]:          # odd primes
        idx = slice((p - 1) // 2, nv, p)
        logG[idx] += math.log1p(-1.0 / p)
        w[idx] += 1
    _T.update(N=N, G=np.exp(logG), w=w)
    return _T["G"], _T["w"]


def y1_of(Gt_sorted, q):
    """min{y>=1 : Nt(y) >= y}, or 0 if Nt(0) > 0 (some Gt <= 0); G certifies (b,l) whenever b + l <= y1."""
    if Gt_sorted[0] - SAFETY <= 0:
        return 0
    k = np.arange(1, len(Gt_sorted) + 1)
    cond = Gt_sorted - SAFETY <= np.sqrt(k / q)
    return int(k[np.argmax(cond)]) if cond.any() else len(Gt_sorted) + 1


def params(n):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    nodd = (n + 1) // 2
    return q, m, h, T, nodd, nodd - h - 1


def check_n(n):
    q, m, h, T, nodd, bmax = params(n)
    G, w = tables(n)
    G, w = G[:nodd], w[:nodd]
    two = np.power(2.0, w.astype(np.float64))
    s = np.sort(G - two / math.sqrt(2 * q))
    y1 = y1_of(s, q)
    tA = math.sqrt((n - T + 2 * m - 1) / n)
    NGA = int(np.count_nonzero(G - two / math.sqrt(2 * n) - SAFETY <= tA))
    return dict(n=n, q=q, m=m, bmax=bmax, y1=y1, NGA=NGA, ok=bool(NGA <= y1 - m), margin=(y1 - m - NGA) / q)


def check_block(Nlo, Nhi):
    qlo, mlo, _, _, _, _ = params(Nlo)
    qhi, mhi, _, _, nodd_hi, _ = params(Nhi)
    G, w = tables(Nhi)
    G, w = G[:nodd_hi], w[:nodd_hi]
    two = np.power(2.0, w.astype(np.float64))
    s = np.sort(G - two / math.sqrt(2 * qlo))
    y1 = y1_of(s, qlo)
    tA = math.sqrt(1.0 / 3 + 7.0 / (6 * Nlo) + (2 * mhi - 1) / Nlo)
    NGA = int(np.count_nonzero(G - two / math.sqrt(2 * Nlo) - SAFETY <= tA))
    return dict(Nlo=Nlo, Nhi=Nhi, y1=y1, NGA=NGA, mhi=mhi, ok=bool(NGA <= y1 - mhi), margin=(y1 - mhi - NGA) / qlo)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "pern":
        lo, hi, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        tables(hi)
        with open(out, "a") as fh:
            for n in range(lo, hi + 1):
                fh.write(json.dumps(check_n(n)) + "\n")
    elif mode == "samples":
        out = sys.argv[2]
        with open(out, "a") as fh:
            for n in [int(x) for x in sys.argv[3:]]:
                fh.write(json.dumps(check_n(n)) + "\n"); fh.flush()
    elif mode == "blocks":
        lo, hi, ratio, out = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
        tables(hi)
        n = lo
        with open(out, "a") as fh:
            while n <= hi:
                Nhi = min(hi, max(n, int(n * ratio)))
                r = check_block(n, Nhi)
                fh.write(json.dumps(r) + "\n"); fh.flush()
                n = Nhi + 1
