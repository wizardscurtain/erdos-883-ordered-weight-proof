"""Independent implementation-check for probe-1 tables (gate impl-check).

Recomputes rho, kappa, kappa_n by brute force (direct gcd loops, no inclusion-exclusion,
no spf sieve) for a few n and compares with cert1.tables.
"""
import sys
from math import gcd

SIGP = (5, 7, 11, 13)


def primes_of(v):
    out = []
    p = 2
    while p * p <= v:
        if v % p == 0:
            out.append(p)
            while v % p == 0:
                v //= p
        p += 1
    if v > 1:
        out.append(v)
    return out


def brute(n):
    q = n // 2
    rho, kap, kapn = [], [], []
    for v in range(1, n + 1, 2):
        rho.append(sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, v) > 1))
        ps = [p for p in primes_of(v) if p != 3]
        S = [p for p in ps if p in SIGP]
        prodS = 1
        for p in S:
            prodS *= p
        sig_q = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, prodS) > 1)
        sig_n = sum(1 for u in range(1, n + 1) if u % 3 and gcd(u, prodS) > 1)
        lam = sum(sum(1 for k in range(1, q + 1) if k % 3 and k % p == 0) for p in ps if p not in SIGP)
        lamn = sum(sum(1 for u in range(1, n + 1) if u % 3 and u % p == 0) for p in ps if p not in SIGP)
        kap.append(sig_q + 2 * lam)
        kapn.append(sig_n + 2 * lamn)
    return sorted(rho), sorted(kap), sorted(kapn)


if __name__ == "__main__":
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import cert1
    ok = True
    for n in map(int, sys.argv[1:]):
        spf = cert1.spf_table(n)
        T = cert1.tables(n, spf)
        r, k, kn = brute(n)
        same = (list(T["rho"]) == r and list(T["kap"]) == k and list(T["kapn"]) == kn)
        print(n, "MATCH" if same else "MISMATCH")
        ok &= same
    print("IMPL_CHECK_PASS" if ok else "IMPL_CHECK_FAIL")
