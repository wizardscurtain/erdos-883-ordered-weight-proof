"""Code-disjoint recomputation of the probe-2 cost tables by brute force gcd loops."""
import sys
from math import gcd

SIG = (5, 7, 11, 13)


def pf(v):
    out, p = [], 2
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
    Delta = q // 3
    cE, cRC = [], []
    for v in range(1, n + 1, 2):
        ps = [p for p in pf(v) if p != 3]
        S = [p for p in ps if p in SIG]
        P = 1
        for p in S:
            P *= p
        Lg = [p for p in ps if p not in SIG]
        if v % 3 == 0:
            s3 = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, P) > 1)
            l3 = sum(sum(1 for k in range(1, q + 1) if k % 3 and k % p == 0) for p in Lg)
            cE.append(s3 + 2 * l3)
        else:
            sA = sum(1 for k in range(1, q + 1) if gcd(k, P) > 1)
            lA = sum(sum(1 for k in range(1, q + 1) if k % p == 0) for p in Lg)
            cE.append(sA + 2 * lA - Delta)
            sN = sum(1 for u in range(1, n + 1) if gcd(u, P) > 1)
            lN = sum(sum(1 for u in range(1, n + 1) if u % p == 0) for p in Lg)
            cRC.append(sN + 2 * lN)
    return sorted(cE), sorted(cRC)


if __name__ == "__main__":
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import cert2
    ok = True
    for n in map(int, sys.argv[1:]):
        spf = cert2.spf_table(n)
        D = cert2.build(n, spf)
        e, r = brute(n)
        same = list(D["cE"]) == e and list(D["cRC"]) == r
        print(n, "MATCH" if same else "MISMATCH")
        ok &= same
    print("IMPL_CHECK_PASS" if ok else "IMPL_CHECK_FAIL")
