"""cert8: families E, R, M with (i) audit fix for l=1, (ii) every rough count bounded by
min(absolute count in the natural key, tail-subtracted count via tau map), (iii) separator
availability likewise. See REDUCTION_LEMMA.md (sections 3-5 and amendment A-3).

Absolute counts: the skeleton is a subset of the odd part of A, so #(skeleton cap W) <= |W cap odd [n]|
for every set W, with no assumption on A. This is valid in every family.
"""
import sys, json
import numpy as np
WF = 1   # within-chunk factor: 1 with cost-sorted chunks (amendment A-4), 2 = audited original
from cert4 import build4, tau_from, spf_table
from cert7 import gC


def sorted_tail(arr):
    s = np.sort(arr)
    return lambda t: len(s) - np.searchsorted(s, t, side="left")


def tau_struct(key, cost):
    o = np.argsort(key, kind="stable")
    ks = key[o]
    suf = np.append(np.minimum.accumulate(cost[o][::-1])[::-1], 1 << 60)
    return lambda t: suf[np.searchsorted(ks, t, side="left")]


class Cert8:
    def __init__(self, n, spf, ndelta=8, ngr=24, ngN=24, sig=(5, 7, 11, 13), full_grid=False, D=None):
        if D is None:
            D = build4(n, spf, SIG=sig)
        self.D = D
        self.n, self.m, self.h, self.T = n, D["m"], D["h"], D["T"]
        self.bmax = D["nodd"] - D["h"] - 1
        self.gc = gC(n)
        Dl = D["Delta"]
        if full_grid:
            self.deltas = list(range(0, Dl + 1))
            self.grs = sorted(set(int(x) for x in D["rho"]))
            self.gNs = sorted(set(int(x) for x in D["rhoN"]))
        else:
            self.deltas = sorted(set(int(round(Dl * k / (ndelta - 1))) for k in range(ndelta)))
            self.grs = sorted(set(int(x) for x in np.quantile(D["rho"], np.linspace(0.02, 0.95, ngr))))
            self.gNs = sorted(set(int(x) for x in np.quantile(D["rhoN"], np.linspace(0.02, 0.95, ngN))))
        m = self.m
        s = np.arange(0, self.bmax + m + 3, dtype=np.int64)
        th = D["beta0"] - s + 1
        # absolute (A-free) counts over all odd vertices
        absRho = sorted_tail(D["rho"])
        is3 = D["is3"]
        self.P = []
        for dl in self.deltas:
            c = D["base"] - np.where(is3, 0, dl)
            R = sorted_tail(c)
            keyw = np.where(is3, c, c - (Dl - dl))
            absW = sorted_tail(keyw)                       # #odd v in W_w(theta) = #{keyw >= theta}
            Fw = np.minimum(absW(th), np.maximum(0, R(tau_from(keyw, c, th)) - 0))   # b subtracted later
            Fw_tail = R(tau_from(keyw, c, th))
            Fw_abs = absW(th)
            tr = tau_struct(D["rho"], c)
            for gr in self.grs:
                Gb_tail = R(tr(th - gr))
                Gb_abs = absRho(th - gr)
                Rsep_tail = int(R(tr(np.array([gr + 1])))[0])
                Rsep_abs = int(absRho(np.array([gr + 1]))[0])
                self.P.append((dl, gr, Fw_tail, Fw_abs, Gb_tail, Gb_abs, Rsep_tail, Rsep_abs, th))
            # l=1 data: rough set {rho >= ceil(theta1/2)}
        self.l1 = []
        for dl in self.deltas:
            c = D["base"] - np.where(is3, 0, dl)
            R = sorted_tail(c)
            tr = tau_struct(D["rho"], c)
            self.l1.append((R, tr))
        self.absRho = absRho
        self.RC = sorted_tail(D["cR"])
        self.tauN = tau_struct(D["rhoN"], D["cR"])
        self.absN = sorted_tail(D["rhoN"])
        self.absCR = sorted_tail(D["cR"])
        self.PR = [(gN, int(self.RC(self.tauN(np.array([gN + 1])))[0]), int(self.absN(np.array([gN + 1]))[0])) for gN in self.gNs]
        # M-family data
        isC = ~is3
        self.rhoC = D["rho"][isC]
        self.c3 = D["base"][is3]
        self.rho3 = D["rho"][is3]
        self.R3 = sorted_tail(self.c3)
        self.tau3 = tau_struct(self.rho3, self.c3)
        self.abs3 = sorted_tail(self.rho3)
        self.grho = {gN: int(self.rhoC[D["rhoN"] <= gN].max()) if (D["rhoN"] <= gN).any() else 0 for gN in self.gNs}
        self.order = list(range(len(self.P)))

    # ---------------- Family E ----------------
    def LE(self, b):
        D, m = self.D, self.m
        j = np.arange(1, m + 1, dtype=np.int64)
        K = D["K"]
        cap = 2 * K + 2
        best, bi = 0, None
        for idx in self.order:
            dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th = self.P[idx]
            Ns = self.h + 1 - min(Rsa, max(0, Rst - b))
            if Ns < K + 3:
                continue
            sidx = b + j
            within = WF * np.minimum(Fwa[sidx], np.maximum(0, Fwt[sidx] - b))
            bnd = np.minimum(cap, 2 * np.minimum(Gba[sidx], np.maximum(0, Gbt[sidx] - b)))
            dd = K * (th[sidx] <= 2 * gr)
            bad = within + bnd + dd
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

    def E_l1(self, b):
        D = self.D
        t = -((-(D["beta0"] - b)) // 2)
        for R, tr in self.l1:
            cnt = min(int(self.absRho(np.array([t]))[0]), max(0, int(R(tr(np.array([t])))[0]) - b))
            if cnt == 0:
                return True
        return False

    # ---------------- Family R ----------------
    def Rok(self, b, l):
        D = self.D
        s0 = max(l + 1, self.gc + 1)
        if b + 1 < s0:
            return False
        sub = b + 1 - s0
        if l == 1:
            t = np.array([-((-(self.T - 1)) // 2)])
            return min(int(self.absN(t)[0]), max(0, int(self.RC(self.tauN(t))[0]) - sub)) == 0
        j = np.arange(1, l + 1, dtype=np.int64)
        thR = self.T - l - j + 1
        W = WF * np.minimum(self.absCR(thR), np.maximum(0, self.RC(thR) - sub))
        KC = D["KC"]
        for gN, Rst, Rsa in self.PR:
            NsC = s0 - min(Rsa, max(0, Rst - sub))
            if NsC < KC + 3:
                continue
            tt = thR - gN
            Bd = np.minimum(2 * KC + 2, 2 * np.minimum(self.absN(tt), np.maximum(0, self.RC(self.tauN(tt)) - sub)))
            dd = KC * (thR <= 2 * gN)
            if np.all(W + Bd + dd <= j - 1):
                return True
        return False

    # ---------------- Family M ----------------
    def M_ok_c(self, b, l, c):
        D = self.D
        h, T = self.h, self.T
        X = b + c + 1
        if X < self.gc + 1:
            return False
        if X >= l + 1:
            return None  # this c is handled by R-type with subX = X-l-1 >= b+1-s0 ... use R check
        z, subX, xpart = l + 1 - X, 0, X
        if z > h - c:
            return False
        sub3 = h - c - z
        if l == 1:
            return False
        j = np.arange(1, l + 1, dtype=np.int64)
        thR = T - l - j + 1
        th = D["beta0"] - b - j + 1
        W = WF * self.absCR(thR)
        KC = D["KC"]
        for gN, Rst, Rsa in self.PR:
            NsC = xpart - Rsa
            if NsC < KC + 3 + z:
                continue
            Bd = np.minimum(2 * KC + 2, 2 * self.absN(thR - gN))
            dd = (KC + z) * (thR <= 2 * gN)
            tt = th - self.grho[gN]
            O = np.minimum(2 * z, 2 * np.minimum(self.abs3(tt), np.maximum(0, self.R3(self.tau3(tt)) - sub3)))
            if np.all(W + Bd + dd + O <= j - 1):
                return True
        return False

    def M_ok(self, b, l):
        # every adversarial c must be handled: either by M (z>0) or by R-type (|X| >= l+1)
        for c in range(0, self.h + 1):
            r = self.M_ok_c(b, l, c)
            if r is None:
                # |X| = b+c+1 >= l+1: R-family with sub >= b+c+1-s0 >= sub(c=0); monotone in c, so
                # it suffices that Rok holds with the actual |X|; check R at the smallest such c
                if not self.R_with_X(b + c + 1, l):
                    return False
                break   # larger c only increases |X| (R monotone in sub)
            if not r:
                return False
        return True

    def R_with_X(self, X, l):
        # R certificate when |X| is known (= X); equivalent to Rok with b = X-1
        return self.Rok(X - 1, l)

    def coverage(self):
        unc = []
        for b in range(self.bmax + 1):
            if not (self.E_l1(b) or self.Rok(b, 1)):
                unc.append((b, 1, 0))
                continue
            L = self.LE(b)
            for l in range(max(2, L + 1), self.m + 1):
                if self.Rok(b, l) or self.M_ok(b, l):
                    continue
                unc.append((b, l, L))
                break
        return unc


SIGSETS = ((5, 7, 11, 13), (5, 7, 11), (5, 7))


def coverage_multi(n, spf, full_grid=False, sigsets=None):
    """(b,l) is covered if covered under some signature-prime set (constructor's choice)."""
    certs = [Cert8(n, spf, sig=sg, full_grid=full_grid) for sg in (sigsets or SIGSETS)]
    unc = []
    C0 = certs[0]
    for b in range(C0.bmax + 1):
        if not any(C.E_l1(b) or C.Rok(b, 1) for C in certs):
            unc.append((b, 1, 0)); continue
        Ls = [C.LE(b) for C in certs]
        L = max(Ls)
        for l in range(max(2, L + 1), C0.m + 1):
            if any(C.Rok(b, l) or C.M_ok(b, l) for C in certs):
                continue
            unc.append((b, l, L)); break
    return unc


def run(n, spf):
    C = Cert8(n, spf)
    unc = coverage_multi(n, spf)
    return dict(n=n, m=C.m, h=C.h, bmax=C.bmax, n_uncovered=len(unc), uncovered=unc[:12])


if __name__ == "__main__":
    ns = [int(x) for x in open(sys.argv[1]).read().split()] if not sys.argv[1].isdigit() else list(range(int(sys.argv[1]), int(sys.argv[2]) + 1))
    out = sys.argv[-1]
    spf = spf_table(max(ns))
    with open(out, "a") as fh:
        for n in ns:
            fh.write(json.dumps(run(n, spf)) + "\n")
            fh.flush()
