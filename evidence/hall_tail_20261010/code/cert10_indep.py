"""Code-disjoint plain-loop implementation of the amended certificates (cert9):
E (cost-sorted chunks: within factor 1; min(absolute, tail) counts; l=1 rule), R (min counts; l=1 rule),
M (mixed skeleton, absolute counts), each for signature sets (5,7,11,13), (5,7,11), (5,7);
(b,l) covered if some family under some signature set certifies it. Compares with cert9.coverage_multi.
"""
import sys
from math import gcd

SIGSETS = ((5, 7, 11, 13), (5, 7, 11), (5, 7))
FULL = False


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


def quantile_grid(vals, k, lo=0.02, hi=0.95):
    # replicate numpy.quantile (linear interpolation) without numpy
    s = sorted(vals)
    out = set()
    for i in range(k):
        p = lo + (hi - lo) * i / (k - 1)
        x = p * (len(s) - 1)
        f = int(x)
        c = min(f + 1, len(s) - 1)
        out.add(int(s[f] + (s[c] - s[f]) * (x - f)))
    return sorted(out)


class Indep:
    def __init__(self, n, SIG):
        self.n = n
        q = n // 2
        self.q, self.m = q, n // 6
        self.h = n // 3 - n // 6
        self.T = n // 2 + n // 3 - n // 6
        self.Dl = q // 3
        self.beta0 = q - self.Dl
        rows = []
        for v in range(1, n + 1, 2):
            ps = [p for p in pf(v) if p != 3]
            S = tuple(p for p in SIG if p in ps)
            P = 1
            for p in S:
                P *= p
            Lg = [p for p in ps if p not in SIG]
            rho = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, v) > 1)
            if v % 3 == 0:
                base = sum(1 for k in range(1, q + 1) if k % 3 and gcd(k, P) > 1) + 2 * sum(q // p - q // (3 * p) for p in Lg)
                rows.append(dict(is3=True, base=base, rho=rho, key=(3, S)))
            else:
                base = sum(1 for k in range(1, q + 1) if gcd(k, P) > 1) + 2 * sum(q // p for p in Lg)
                cR = sum(1 for u in range(1, n + 1) if gcd(u, P) > 1) + 2 * sum(n // p for p in Lg)
                rhoN = sum(1 for u in range(1, n + 1) if gcd(u, v) > 1)
                rows.append(dict(is3=False, base=base, rho=rho, cR=cR, rhoN=rhoN, key=(1, S)))
        self.rows = rows
        self.K = len(set(r["key"] for r in rows))
        self.KC = len(set(r["key"] for r in rows if not r["is3"]))
        self.bmax = len(rows) - self.h - 1
        Cs = [x for x in range(1, n + 1) if x % 2 and x % 3]
        self.gc = 1 + (len(Cs) - 1 + 3) // 4
        Dl = self.Dl
        self.Crows = [r for r in rows if not r["is3"]]
        if FULL:
            self.deltas = list(range(0, Dl + 1))
            self.grs = sorted(set(r["rho"] for r in rows))
            self.gNs = sorted(set(r["rhoN"] for r in self.Crows))
        else:
            self.deltas = sorted(set(int(round(Dl * k / 7)) for k in range(8)))
            self.grs = quantile_grid([r["rho"] for r in rows], 24)
            self.gNs = quantile_grid([r["rhoN"] for r in self.Crows], 24)
        self.O3rows = [r for r in rows if r["is3"]]

    # generic helpers ---------------------------------------------------
    @staticmethod
    def tail_count(items, cost, member, b):
        """min(#members, max(0, #{cost >= min cost over members} - b))."""
        mem = [x for x in items if member(x)]
        if not mem:
            return 0
        tau = min(cost(x) for x in mem)
        tot = sum(1 for x in items if cost(x) >= tau)
        return min(len(mem), max(0, tot - b))

    def E_prefix(self, b):
        best = 0
        m = self.m
        for dl in self.deltas:
            cost = lambda r, dl=dl: r["base"] - (0 if r["is3"] else dl)
            for gr in self.grs:
                nonsep = self.tail_count(self.rows, cost, lambda r: r["rho"] >= gr + 1, b)
                if self.h + 1 - nonsep < self.K + 3:
                    continue
                L = 0
                for j in range(1, m + 1):
                    th = self.beta0 - b - j + 1
                    w = self.tail_count(self.rows, cost, lambda r: cost(r) >= (th if r["is3"] else th + self.Dl - dl), b)
                    bd = min(2 * self.K + 2, 2 * self.tail_count(self.rows, cost, lambda r: r["rho"] >= th - gr, b))
                    dd = self.K if th <= 2 * gr else 0
                    if w + bd + dd <= j - 1:
                        L = j
                    else:
                        break
                best = max(best, L)
                if best == m:
                    return best
        return best

    def E_l1(self, b):
        t = -((-(self.beta0 - b)) // 2)
        for dl in self.deltas:
            cost = lambda r, dl=dl: r["base"] - (0 if r["is3"] else dl)
            if self.tail_count(self.rows, cost, lambda r: r["rho"] >= t, b) == 0:
                return True
        return False

    def R_ok(self, b, l):
        s0 = max(l + 1, self.gc + 1)
        if b + 1 < s0:
            return False
        sub = b + 1 - s0
        cost = lambda r: r["cR"]
        if l == 1:
            t = -((-(self.T - 1)) // 2)
            return self.tail_count(self.Crows, cost, lambda r: r["rhoN"] >= t, sub) == 0
        for gN in self.gNs:
            if s0 - self.tail_count(self.Crows, cost, lambda r: r["rhoN"] >= gN + 1, sub) < self.KC + 3:
                continue
            ok = True
            for j in range(1, l + 1):
                thR = self.T - l - j + 1
                W = self.tail_count(self.Crows, cost, lambda r: r["cR"] >= thR, sub)
                Bd = min(2 * self.KC + 2, 2 * self.tail_count(self.Crows, cost, lambda r: r["rhoN"] >= thR - gN, sub))
                dd = self.KC if thR <= 2 * gN else 0
                if W + Bd + dd > j - 1:
                    ok = False
                    break
            if ok:
                return True
        return False

    def M_ok(self, b, l):
        for c in range(0, self.h + 1):
            X = b + c + 1
            if X < self.gc + 1:
                return False
            if X >= l + 1:
                return self.R_ok(X - 1, l)
            if l == 1:
                return False
            z = l + 1 - X
            if z > self.h - c:
                return False
            sub3 = self.h - c - z
            okc = False
            for gN in self.gNs:
                nonsep = sum(1 for r in self.Crows if r["rhoN"] >= gN + 1)
                if X - nonsep < self.KC + 3 + z:
                    continue
                seps = [r["rho"] for r in self.Crows if r["rhoN"] <= gN]
                grho = max(seps) if seps else 0
                ok = True
                for j in range(1, l + 1):
                    thR = self.T - l - j + 1
                    th = self.beta0 - b - j + 1
                    W = sum(1 for r in self.Crows if r["cR"] >= thR)
                    Bd = min(2 * self.KC + 2, 2 * sum(1 for r in self.Crows if r["rhoN"] >= thR - gN))
                    dd = (self.KC + z) if thR <= 2 * gN else 0
                    O = min(2 * z, 2 * self.tail_count(self.O3rows, lambda r: r["base"], lambda r: r["rho"] >= th - grho, sub3))
                    if W + Bd + dd + O > j - 1:
                        ok = False
                        break
                if ok:
                    okc = True
                    break
            if not okc:
                return False
        return True


def coverage(n):
    certs = [Indep(n, sg) for sg in SIGSETS]
    C0 = certs[0]
    unc = []
    for b in range(C0.bmax + 1):
        if not any(C.E_l1(b) or C.R_ok(b, 1) for C in certs):
            unc.append((b, 1, 0))
            continue
        L = max(C.E_prefix(b) for C in certs)
        for l in range(max(2, L + 1), C0.m + 1):
            if any(C.R_ok(b, l) or C.M_ok(b, l) for C in certs):
                continue
            unc.append((b, l, L))
            break
    return unc


if __name__ == "__main__":
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import cert9, cert10
    args = sys.argv[1:]
    if args and args[0] == "--full":
        FULL = True
        SIGSETS = ((5,7,11,13),(5,7,11),(5,7),(5,),(5,11),(5,7,13),(5,11,13),(7,11,13),())
        args = args[1:]
    allok = True
    for n in map(int, args):
        spf = cert9.spf_table(n)
        if FULL:
            fast = [tuple(x) for x in cert10.coverage_multi(n, spf, full_grid=True, sigsets=SIGSETS)]
        else:
            fast = [tuple(x) for x in cert9.coverage_multi(n, spf)]
        slow = coverage(n)
        same = fast == slow
        print(n, "MATCH" if same else "MISMATCH", len(slow), slow[:4], fast[:4] if not same else "")
        allok &= same
    print("IMPL_CHECK_PASS" if allok else "IMPL_CHECK_FAIL")
