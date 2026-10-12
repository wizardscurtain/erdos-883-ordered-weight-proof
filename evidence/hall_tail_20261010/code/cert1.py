"""Per-n Hall-tail certificates for Erdos #883(i) (probe-1).

For a fixed n this computes, for every missing-even budget b, whether one of the
connector families F1 (even connectors, signature ordered), F2 (all unused
vertices, signature ordered) certifies every long cycle length, and reports the
uncovered budgets.  Also computes the unordered union-bound family F0.

All counts are exact integers.  See REDUCTION_LEMMA.md for the proof that these
inequalities imply the cycles.
"""
import sys
import json
import numpy as np

SIG_PRIMES = (5, 7, 11, 13)


def spf_table(N):
    spf = list(range(N + 1))
    i = 2
    while i * i <= N:
        if spf[i] == i:
            for k in range(i * i, N + 1, i):
                if spf[k] == k:
                    spf[k] = i
        i += 1
    return spf


def prime_set(v, spf):
    ps = []
    while v > 1:
        p = spf[v]
        ps.append(p)
        while v % p == 0:
            v //= p
    return ps


def count_coprime(N, primes):
    """#{1<=k<=N : gcd(k, prod primes) = 1} by inclusion-exclusion (exact)."""
    primes = list(primes)
    tot = 0
    L = len(primes)
    for mask in range(1 << L):
        d = 1
        bits = 0
        for i in range(L):
            if mask >> i & 1:
                d *= primes[i]
                bits += 1
        tot += (-1) ** bits * (N // d)
    return tot


def tables(n, spf):
    q = n // 2
    m = n // 6
    h = n // 3 - n // 6
    beta0 = q - q // 3
    odds = list(range(1, n + 1, 2))
    # sigma(S) for subsets of signature primes, base q (even connectors) and base n (all vertices)
    nc3_q = q - q // 3
    nc3_n = n - n // 3
    sigma_q = {}
    sigma_n = {}
    for mask in range(1 << len(SIG_PRIMES)):
        S = tuple(p for i, p in enumerate(SIG_PRIMES) if mask >> i & 1)
        sigma_q[S] = nc3_q - count_coprime(q, (3,) + S)
        sigma_n[S] = nc3_n - count_coprime(n, (3,) + S)
    rho = np.zeros(len(odds), dtype=np.int64)
    kap = np.zeros(len(odds), dtype=np.int64)
    kapn = np.zeros(len(odds), dtype=np.int64)
    sigs = set()
    for idx, v in enumerate(odds):
        ps = [p for p in prime_set(v, spf) if p != 3]
        S = tuple(p for p in SIG_PRIMES if p in ps)
        sigs.add(S)
        large = [p for p in ps if p not in SIG_PRIMES]
        lam = sum(q // p - q // (3 * p) for p in large)
        lamn = sum(n // p - n // (3 * p) for p in large)
        kap[idx] = sigma_q[S] + 2 * lam
        kapn[idx] = sigma_n[S] + 2 * lamn
        # exact rho(v) = #{k<=q: 3 !| k, gcd(k,v)>1}
        rho[idx] = nc3_q - count_coprime(q, [3] + ps)
    return dict(n=n, q=q, m=m, h=h, beta0=beta0, nodd=len(odds),
                rho=np.sort(rho), kap=np.sort(kap), kapn=np.sort(kapn),
                nsig=len(sigs))


def tail(sorted_arr, t):
    """#{x in arr : x >= t}, vectorized in t."""
    return len(sorted_arr) - np.searchsorted(sorted_arr, t, side="left")


def ceil_half(x):
    return -((-x) // 2)


def family_ok(T, b, fam):
    m = T["m"]
    j = np.arange(1, m + 1, dtype=np.int64)
    nb = T["nsig"] + 1
    if fam == "F1":
        theta = T["beta0"] - b - j + 1
        arr = T["kap"]
        within = 2 * np.maximum(0, tail(arr, theta) - b)
        bnd = np.minimum(nb, 2 * np.maximum(0, tail(arr, ceil_half(theta)) - b))
        bad = within + bnd
    elif fam == "F2":
        theta = T["beta0"] - m - j + 1
        arr = T["kapn"]
        within = 2 * np.maximum(0, tail(arr, theta) - b)
        bnd = np.minimum(nb, 2 * np.maximum(0, tail(arr, ceil_half(theta)) - b))
        bad = within + bnd
    elif fam == "F0":
        theta = T["beta0"] - b - j + 1
        bad = 2 * np.maximum(0, tail(T["rho"], ceil_half(theta)) - b)
    else:
        raise ValueError(fam)
    return bool(np.all(bad <= j - 1))


def analyse(n, spf):
    T = tables(n, spf)
    bmax = T["nodd"] - T["h"] - 1
    f1 = [family_ok(T, b, "F1") for b in range(bmax + 1)]
    f2 = [family_ok(T, b, "F2") for b in range(bmax + 1)]
    f0 = [family_ok(T, b, "F0") for b in range(bmax + 1)]
    uncovered = [b for b in range(bmax + 1) if not (f1[b] or f2[b])]
    def maxprefix(lst):
        k = 0
        while k < len(lst) and lst[k]:
            k += 1
        return k - 1
    return dict(n=n, m=T["m"], bmax=bmax, F1_b0=f1[0], F0_maxprefix=maxprefix(f0),
                F1_maxprefix=maxprefix(f1), F2_min=(min([b for b in range(bmax + 1) if f2[b]]) if any(f2) else None),
                uncovered_count=len(uncovered), uncovered_first=uncovered[:5], uncovered_last=uncovered[-5:])


if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3]
    spf = spf_table(hi)
    rows = [analyse(n, spf) for n in range(lo, hi + 1)]
    with open(out, "w") as fh:
        json.dump(rows, fh)
    print("done", len(rows))
