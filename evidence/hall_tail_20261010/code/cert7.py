"""Exact implementation of the certificates in REDUCTION_LEMMA.md (families E and R).

coverage(n): for every b in [0,b_max] find the largest prefix of targets l certified by E
(over a parameter grid), then require R for every remaining l. Reports uncovered (b, l).
"""
import sys, json
import numpy as np
from cert4 import build4, tau_from, spf_table


def gC(n):
    """number of groups in the C-partition of L2."""
    C = [x for x in range(1, n + 1) if x % 2 and x % 3]
    rest = C[1:]
    return 1 + (len(rest) + 3) // 4


class Cert:
    def __init__(self, n, spf):
        D = build4(n, spf)
        self.D = D
        self.n, self.m, self.h, self.T = n, D["m"], D["h"], D["T"]
        self.bmax = D["nodd"] - D["h"] - 1
        self.gc = gC(n)
        Dl = D["Delta"]
        self.deltas = sorted(set([0, Dl // 8, Dl // 4, (3 * Dl) // 8, Dl // 2, (5 * Dl) // 8, (3 * Dl) // 4, Dl]))
        self.grs = sorted(set(int(x) for x in np.quantile(D["rho"], np.linspace(0.02, 0.9, 24))))
        self.gNs = sorted(set(int(x) for x in np.quantile(D["rhoN"], np.linspace(0.02, 0.9, 24))))
        m = self.m
        s = np.arange(0, self.bmax + m + 3, dtype=np.int64)
        self.P = []
        for dl in self.deltas:
            c = D["base"] - np.where(D["is3"], 0, dl)
            cs = np.sort(c)
            R = (lambda cs: (lambda t: len(cs) - np.searchsorted(cs, t, side="left")))(cs)
            th = D["beta0"] - s + 1
            keyw = np.where(D["is3"], c, c - (Dl - dl))
            Fw = R(tau_from(keyw, c, th))
            ordr = np.argsort(D["rho"], kind="stable")
            rs = D["rho"][ordr]
            suf = np.append(np.minimum.accumulate(c[ordr][::-1])[::-1], 1 << 60)
            tr = (lambda rs, suf: (lambda t: suf[np.searchsorted(rs, t, side="left")]))(rs, suf)
            for gr in self.grs:
                Gb = R(tr(th - gr))
                Rsep = int(R(tr(np.array([gr + 1])))[0])
                bmin = Rsep - (self.h + 1) + D["K"] + 3
                if self.h + 1 < D["K"] + 3:
                    bmin = 1 << 60          # separators can never suffice
                self.P.append((dl, gr, Fw, Gb, bmin, th))
        csR = np.sort(D["cR"])
        self.RC = lambda t: len(csR) - np.searchsorted(csR, t, side="left")
        ordN = np.argsort(D["rhoN"], kind="stable")
        self._rsN = D["rhoN"][ordN]
        self._sufN = np.append(np.minimum.accumulate(D["cR"][ordN][::-1])[::-1], 1 << 60)
        self.tauN = lambda t: self._sufN[np.searchsorted(self._rsN, t, side="left")]
        self.PR = [(gN, int(self.RC(self.tauN(np.array([gN + 1])))[0])) for gN in self.gNs]
        self.order = list(range(len(self.P)))

    def LE(self, b):
        D, m = self.D, self.m
        j = np.arange(1, m + 1, dtype=np.int64)
        cap = 2 * D["K"] + 2
        best, bi = 0, None
        for idx in self.order:
            dl, gr, Fw, Gb, bmin, th = self.P[idx]
            if b < bmin:
                continue
            sidx = b + j
            bad = (2 * np.maximum(0, Fw[sidx] - b) + np.minimum(cap, 2 * np.maximum(0, Gb[sidx] - b))
                   + D["K"] * (th[sidx] <= 2 * gr))
            okj = bad <= j - 1
            L = m if okj.all() else int(np.argmin(okj))
            if L > best:
                best, bi = L, idx
                if best == m:
                    break
        if bi is not None:
            self.order.remove(bi)
            self.order.insert(0, bi)
        return best

    def Rok(self, b, l):
        D = self.D
        s0 = max(l + 1, self.gc + 1)
        if b + 1 < s0:
            return False
        sub = b + 1 - s0
        j = np.arange(1, l + 1, dtype=np.int64)
        thR = self.T - l - j + 1
        W = 2 * np.maximum(0, self.RC(thR) - sub)
        capC = 2 * D["KC"] + 2
        for gN, RsepN in self.PR:
            NsC = s0 - max(0, RsepN - sub)
            if NsC < D["KC"] + 3:
                continue
            Bd = np.minimum(capC, 2 * np.maximum(0, self.RC(self.tauN(thR - gN)) - sub))
            dd = D["KC"] * (thR <= 2 * gN)
            if np.all(W + Bd + dd <= j - 1):
                return True
        return False

    def coverage(self):
        unc = []
        for b in range(self.bmax + 1):
            L = self.LE(b)
            if L == self.m:
                continue
            for l in range(L + 1, self.m + 1):
                if not self.Rok(b, l):
                    unc.append((b, l, L))
                    break
        return unc


def run(n, spf):
    C = Cert(n, spf)
    unc = C.coverage()
    return dict(n=n, m=C.m, h=C.h, bmax=C.bmax, gC=C.gc, n_uncovered=len(unc), uncovered=unc[:12])


if __name__ == "__main__":
    lo, hi, step = map(int, sys.argv[1:4])
    out = sys.argv[4]
    spf = spf_table(hi)
    rows = [run(n, spf) for n in range(lo, hi + 1, step)]
    json.dump(rows, open(out, "w"))
    U = [r["n"] for r in rows if r["n_uncovered"]]
    print("scanned", len(rows), "uncovered n", len(U), "max", max(U) if U else None)
