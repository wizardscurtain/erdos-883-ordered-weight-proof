"""Code-disjoint check for probe-3: brute-force rho/rhoN and the tau maps."""
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
    D = q // 3
    E, R = [], []
    for v in range(1, n + 1, 2):
        ps = [p for p in pf(v) if p != 3]
        S = [p for p in ps if p in SIG]
        P = 1
        for p in S:
            P *= p
        Lg = [p for p in ps if p not in SIG]
        rho = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, v) > 1)
        if v % 3 == 0:
            c = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, P) > 1) + 2 * sum(
                sum(1 for k in range(1, q + 1) if k % 3 and k % p == 0) for p in Lg)
        else:
            c = sum(1 for k in range(1, q + 1) if gcd(k, P) > 1) + 2 * sum(q // p for p in Lg) - D
            cr = sum(1 for u in range(1, n + 1) if gcd(u, P) > 1) + 2 * sum(n // p for p in Lg)
            rr = sum(1 for u in range(1, n + 1) if gcd(u, v) > 1)
            R.append((cr, rr))
        E.append((c, rho))
    return E, R


def tau(pairs, t):
    vals = [c for c, r in pairs if r >= t]
    return min(vals) if vals else 1 << 60


if __name__ == "__main__":
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import numpy as np
    import cert3
    ok = True
    for n in map(int, sys.argv[1:]):
        spf = cert3.spf_table(n)
        D = cert3.build3(n, spf)
        E, R = brute(n)
        same = (list(zip(D["cE"].tolist(), D["rhoE"].tolist())) == E and list(zip(D["cR"].tolist(), D["rhoR"].tolist())) == R)
        fE = cert3.tau_map(D["cE"], D["rhoE"])
        fR = cert3.tau_map(D["cR"], D["rhoR"])
        for t in range(0, n, max(1, n // 97)):
            same &= int(fE(np.array([t]))[0]) == tau(E, t)
            same &= int(fR(np.array([t]))[0]) == tau(R, t)
        print(n, "MATCH" if same else "MISMATCH")
        ok &= same
    print("IMPL_CHECK_PASS" if ok else "IMPL_CHECK_FAIL")
