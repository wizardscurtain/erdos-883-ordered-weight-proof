"""Code-disjoint slow re-implementation of the REDUCTION_LEMMA certificates for a given n.
Recomputes, for every b, the best certified prefix L_E(b) over the same parameter grid and the
R decisions, with plain loops (no tau/suffix structures, no numpy searchsorted), and compares
against cert7.Cert.
"""
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


def tables(n):
    q = n // 2
    D = q // 3
    rows = []   # (is3, base, rho, cR, rhoN, key)
    for v in range(1, n + 1, 2):
        ps = [p for p in pf(v) if p != 3]
        S = tuple(p for p in SIG if p in ps)
        P = 1
        for p in S:
            P *= p
        Lg = [p for p in ps if p not in SIG]
        rho = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, v) > 1)
        if v % 3 == 0:
            base = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, P) > 1) + 2 * sum(
                (q // p - q // (3 * p)) for p in Lg)
            rows.append((True, base, rho, None, None, (3, S)))
        else:
            base = sum(1 for k in range(1, q + 1) if gcd(k, P) > 1) + 2 * sum(q // p for p in Lg)
            cR = sum(1 for u in range(1, n + 1) if gcd(u, P) > 1) + 2 * sum(n // p for p in Lg)
            rhoN = sum(1 for u in range(1, n + 1) if gcd(u, v) > 1)
            rows.append((False, base, rho, cR, rhoN, (1, S)))
    return rows


def run(n, deltas, grs, gNs):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    Dl = q // 3
    beta0 = q - Dl
    rows = tables(n)
    K = len(set(r[5] for r in rows))
    KC = len(set(r[5] for r in rows if not r[0]))
    bmax = len(rows) - h - 1
    Cs = [x for x in range(1, n + 1) if x % 2 and x % 3]
    gc = 1 + (len(Cs) - 1 + 3) // 4
    LE = []
    for b in range(bmax + 1):
        best = 0
        for dl in deltas:
            cost = [r[1] - (0 if r[0] else dl) for r in rows]
            Rcount = lambda t: sum(1 for x in cost if x >= t)
            def tau(pred):
                vals = [cost[i] for i in range(len(rows)) if pred(i)]
                return min(vals) if vals else 1 << 60
            for gr in grs:
                Ns = h + 1 - max(0, Rcount(tau(lambda i: rows[i][2] >= gr + 1)) - b)
                if Ns < K + 3:
                    continue
                L = 0
                for j in range(1, m + 1):
                    th = beta0 - b - j + 1
                    tw = tau(lambda i: (cost[i] >= th) if rows[i][0] else (cost[i] >= th + Dl - dl))
                    w = 2 * max(0, Rcount(tw) - b)
                    tb = tau(lambda i: rows[i][2] >= th - gr)
                    bd = min(2 * K + 2, 2 * max(0, Rcount(tb) - b))
                    dd = K if th <= 2 * gr else 0
                    if w + bd + dd <= j - 1:
                        L = j
                    else:
                        break
                best = max(best, L)
        LE.append(best)
    Cr = [(r[3], r[4]) for r in rows if not r[0]]
    RCc = lambda t: sum(1 for c, _ in Cr if c >= t)
    def tauN(t):
        vals = [c for c, rn in Cr if rn >= t]
        return min(vals) if vals else 1 << 60
    def Rok(b, l):
        s0 = max(l + 1, gc + 1)
        if b + 1 < s0:
            return False
        sub = b + 1 - s0
        for gN in gNs:
            NsC = s0 - max(0, RCc(tauN(gN + 1)) - sub)
            if NsC < KC + 3:
                continue
            ok = True
            for j in range(1, l + 1):
                thR = T - l - j + 1
                W = 2 * max(0, RCc(thR) - sub)
                Bd = min(2 * KC + 2, 2 * max(0, RCc(tauN(thR - gN)) - sub))
                dd = KC if thR <= 2 * gN else 0
                if W + Bd + dd > j - 1:
                    ok = False
                    break
            if ok:
                return True
        return False
    unc = []
    for b in range(bmax + 1):
        if LE[b] == m:
            continue
        for l in range(LE[b] + 1, m + 1):
            if not Rok(b, l):
                unc.append((b, l, LE[b]))
                break
    return LE, unc


if __name__ == "__main__":
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import cert7
    allok = True
    for n in map(int, sys.argv[1:]):
        spf = cert7.spf_table(n)
        C = cert7.Cert(n, spf)
        LE_fast = [C.LE(b) for b in range(C.bmax + 1)]
        unc_fast = Cert_unc = cert7.Cert(n, spf).coverage()
        LE_slow, unc_slow = run(n, C.deltas, C.grs, C.gNs)
        same = LE_fast == LE_slow and [tuple(x) for x in unc_fast] == [tuple(x) for x in unc_slow]
        print(n, "MATCH" if same else "MISMATCH", "uncovered", len(unc_slow))
        allok &= same
    print("IMPL_CHECK_PASS" if allok else "IMPL_CHECK_FAIL")
