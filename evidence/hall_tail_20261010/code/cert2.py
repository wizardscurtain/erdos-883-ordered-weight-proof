"""Probe-2 per-n certificates for Erdos #883(i): type-split families E' and R'.

Family E' (even connectors), skeleton = h+1 smallest-cost odd vertices of A, cost
  O3 vertex v : c(v) = sigma3(S) + 2*lambda3(v)
  C  vertex x : c(x) = sigmaA(S) + 2*lambdaA(x) - Delta,   Delta = floor(q/3)
  bad_j <= 2*max(0, R(theta_j)-b) + min(K, 2*max(0, R(ceil(theta_j/2)-Delta)-b)),
  theta_j = beta0 - b - j + 1.
Family R' (needs b >= h; skeleton inside X = A cap C; connectors = any unused vertex)
  cost cR(x) = sigmaN(S) + 2*lambdaN(x)
  bad_j <= 2*max(0, RC(thR_j)-(b-h)) + min(KC, 2*max(0, RC(ceil(thR_j/2))-(b-h))),
  thR_j = T - m - j + 1.
Everything is exact integer arithmetic; see REDUCTION_LEMMA.md.
"""
import sys
import json
import numpy as np

SIG = (5, 7, 11, 13)


def spf_table(N):
    spf = np.arange(N + 1)
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:
            blk = spf[i * i::i]
            mask = blk == np.arange(i * i, N + 1, i)
            blk[mask] = i
            spf[i * i::i] = blk
    return spf


def primes_of(v, spf):
    out = []
    while v > 1:
        p = int(spf[v])
        out.append(p)
        while v % p == 0:
            v //= p
    return out


def count_coprime(N, primes):
    primes = list(primes)
    tot = 0
    for mask in range(1 << len(primes)):
        d, bits = 1, 0
        for i, p in enumerate(primes):
            if mask >> i & 1:
                d *= p
                bits += 1
        tot += (-1) ** bits * (N // d)
    return tot


def build(n, spf):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    beta0 = q - q // 3
    Delta = q // 3
    sig3, sigA, sigN = {}, {}, {}
    for mask in range(1 << len(SIG)):
        S = tuple(p for i, p in enumerate(SIG) if mask >> i & 1)
        sig3[S] = (q - q // 3) - count_coprime(q, (3,) + S)
        sigA[S] = q - count_coprime(q, S)
        sigN[S] = n - count_coprime(n, S)
    cE, cRC = [], []
    keysE, keysC = set(), set()
    for v in range(1, n + 1, 2):
        ps = [p for p in primes_of(v, spf) if p != 3]
        S = tuple(p for p in SIG if p in ps)
        Lg = [p for p in ps if p not in SIG]
        if v % 3 == 0:
            lam3 = sum(q // p - q // (3 * p) for p in Lg)
            cE.append(sig3[S] + 2 * lam3)
            keysE.add(("O3", S))
        else:
            lamA = sum(q // p for p in Lg)
            cE.append(sigA[S] + 2 * lamA - Delta)
            keysE.add(("C", S))
            lamN = sum(n // p for p in Lg)
            cRC.append(sigN[S] + 2 * lamN)
            keysC.add(S)
    return dict(n=n, q=q, m=m, h=h, T=T, beta0=beta0, Delta=Delta, nodd=(n + 1) // 2,
                cE=np.sort(np.array(cE, dtype=np.int64)), cRC=np.sort(np.array(cRC, dtype=np.int64)),
                KE=len(keysE), KC=len(keysC))


def tail(arr, t):
    return len(arr) - np.searchsorted(arr, t, side="left")


def ceil_half(x):
    return -((-x) // 2)


def coverage(n, spf):
    D = build(n, spf)
    m, h = D["m"], D["h"]
    bmax = D["nodd"] - h - 1
    j = np.arange(1, m + 1, dtype=np.int64)[None, :]
    # family E' over b in [0, bmax]
    b = np.arange(0, bmax + 1, dtype=np.int64)[:, None]
    th = D["beta0"] - b - j + 1
    badE = 2 * np.maximum(0, tail(D["cE"], th) - b) + np.minimum(D["KE"], 2 * np.maximum(0, tail(D["cE"], ceil_half(th) - D["Delta"]) - b))
    okE = np.all(badE <= j - 1, axis=1)
    slackE = np.min((j - 1) - badE, axis=1)
    # family R' over b in [h, bmax]
    okR = np.zeros(bmax + 1, dtype=bool)
    slackR = np.full(bmax + 1, -10**9, dtype=np.int64)
    if bmax >= h:
        bR = np.arange(h, bmax + 1, dtype=np.int64)[:, None]
        thR = D["T"] - m - j + 1
        sub = bR - h
        badR = 2 * np.maximum(0, tail(D["cRC"], thR) - sub) + np.minimum(D["KC"], 2 * np.maximum(0, tail(D["cRC"], ceil_half(thR)) - sub))
        okR[h:] = np.all(badR <= j - 1, axis=1)
        slackR[h:] = np.min((j - 1) - badR, axis=1)
    cov = okE | okR
    unc = [int(x) for x in np.nonzero(~cov)[0]]
    return dict(n=n, m=m, h=h, bmax=int(bmax), E_all_below_h=bool(np.all(okE[:h])), R_all_from_h=bool(np.all(okR[h:])),
                uncovered=unc[:20], n_uncovered=len(unc),
                E_maxprefix=int(np.argmin(okE)) - 1 if not np.all(okE) else int(bmax),
                minslack_E_below_h=int(np.min(slackE[:h])), minslack_R_from_h=int(np.min(slackR[h:])) if bmax >= h else None)


if __name__ == "__main__":
    lo, hi, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    spf = spf_table(hi)
    rows = []
    for n in range(lo, hi + 1):
        rows.append(coverage(n, spf))
    json.dump(rows, open(out, "w"))
    print("done", len(rows))
