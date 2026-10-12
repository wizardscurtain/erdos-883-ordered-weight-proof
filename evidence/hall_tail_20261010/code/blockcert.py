"""Block certificates: one certificate valid for every n in [Nlo, Nhi] (Families E and R, refined costs).

Monotonicity facts (all counts/costs are nondecreasing in n): for v <= n <= Nhi,
  cost_lo(v) <= cost_n(v) <= cost_hi(v), rho_n(v) <= rho_hi(v), rhoN_n(v) <= rhoN_hi(v),
  beta0, Delta, h, T, q are nondecreasing in n; K(n) <= K(Nhi); g_C(n) <= g_C(Nhi).
Conservative replacements (n in the block, any b <= b_max(n), any l <= m(n)):
  thresholds use beta0_lo, Delta_lo, T_lo, h_lo; universes use v <= Nhi with cost_hi for upper counts;
  minima over rough sets use cost_lo (lower bound of cost_n); ranks up to m_hi, budgets up to b_max_hi.
Within (E): every v in W_n has cost_n >= theta_n >= theta_lo, so tail count <= R_hi(theta_lo).
"""
import sys, json, time
import numpy as np
import fastcert
from cert7 import gC

BIG = 1 << 60


def tail_fn(arr):
    s = np.sort(arr)
    return lambda t: len(s) - np.searchsorted(s, t, side="left")


def tau_fn(key, cost):
    o = np.argsort(key, kind="stable")
    ks = key[o]
    suf = np.append(np.minimum.accumulate(cost[o][::-1])[::-1], BIG)
    return lambda t: suf[np.searchsorted(ks, t, side="left")]


class BlockCert:
    def __init__(self, Nlo, Nhi, P, ndelta=8, ngr=24, ngN=24, refined=True):
        self.Nlo, self.Nhi, self.P = Nlo, Nhi, P
        Dh = fastcert.build_fast(Nhi, P, refined=refined)
        # costs of the same vertices (v <= Nhi) evaluated with n = Nlo parameters (lower bounds)
        Dl = fastcert.build_fast_costs_at(Nhi, Nlo, P, refined=refined)
        self.Dh, self.Dl = Dh, Dl
        lo = dict(q=Nlo // 2, m=Nlo // 6, h=Nlo // 3 - Nlo // 6, T=Nlo // 2 + Nlo // 3 - Nlo // 6)
        lo["beta0"] = lo["q"] - lo["q"] // 3; lo["Delta"] = lo["q"] // 3
        self.lo = lo
        self.m_hi, self.h_hi = Dh["m"], Dh["h"]
        self.bmax = Dh["nodd"] - Dh["h"] - 1          # max over block (b_max nondecreasing)
        self.K, self.KC = Dh["K"], Dh["KC"]
        self.gc = gC(Nhi)
        Dl_ = lo["Delta"]
        self.deltas = sorted(set(int(round(Dl_ * k / (ndelta - 1))) for k in range(ndelta)))
        self.grs = sorted(set(int(x) for x in np.quantile(Dh["rho"], np.linspace(0.02, 0.95, ngr))))
        self.gNs = sorted(set(int(x) for x in np.quantile(Dh["rhoN"], np.linspace(0.02, 0.95, ngN))))
        m = self.m_hi
        s = np.arange(0, self.bmax + m + 3, dtype=np.int64)
        th = lo["beta0"] - s + 1
        is3 = Dh["is3"]
        absRho = tail_fn(Dh["rho"])
        self.absRho = absRho
        self.P_ = []
        self.l1 = []
        for dl in self.deltas:
            chi = Dh["base"] - np.where(is3, 0, dl)
            clo = Dl["base"] - np.where(is3, 0, dl)
            Rhi = tail_fn(chi)
            keyw = np.where(is3, chi, chi - (lo["Delta"] - dl))
            absW = tail_fn(keyw)
            Fwt = Rhi(th)                     # tau_n >= theta_lo
            Fwa = absW(th)
            trho = tau_fn(Dh["rho"], clo)     # min cost_lo over {rho_hi >= t}
            for gr in self.grs:
                Gbt = Rhi(trho(th - gr))
                Gba = absRho(th - gr)
                Rst = int(Rhi(trho(np.array([gr + 1])))[0])
                Rsa = int(absRho(np.array([gr + 1]))[0])
                self.P_.append((dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th))
            self.l1.append((Rhi, trho))
        # R family
        isC = ~is3
        self.cRhi, self.cRlo = Dh["cR"], Dl["cR"]
        self.RC = tail_fn(self.cRhi)
        self.absCR = tail_fn(self.cRhi)
        self.absN = tail_fn(Dh["rhoN"])
        self.tauN = tau_fn(Dh["rhoN"], self.cRlo)
        self.PR = [(gN, int(self.RC(self.tauN(np.array([gN + 1])))[0]), int(self.absN(np.array([gN + 1]))[0])) for gN in self.gNs]
        self.order = list(range(len(self.P_)))
        self.cap = 2 * self.K + 2
        self.J0 = min(m, self.cap + self.K + 1)
        self.win = []
        for (dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th_) in self.P_:
            ss = np.arange(len(Fwt))
            dd = self.K * (th_ <= 2 * gr)
            A = ss - 1 - Fwt - self.cap - dd
            self.win.append((np.concatenate([[0], np.cumsum(A < 0)]), Fwt))

    # ---- Family E ----
    def E_full_fast(self, b, idx):
        m, K = self.m_hi, self.K
        dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th = self.P_[idx]
        if self.lo["h"] + 1 - min(Rsa, max(0, Rst - b)) < K + 3:
            return False
        j = np.arange(1, self.J0 + 1)
        si = b + j
        bad = (np.minimum(Fwa[si], np.maximum(0, Fwt[si] - b)) + np.minimum(self.cap, 2 * np.minimum(Gba[si], np.maximum(0, Gbt[si] - b)))
               + K * (th[si] <= 2 * gr))
        if not np.all(bad <= j - 1):
            return False
        if self.J0 >= m:
            return True
        badA, Ft = self.win[idx]
        lo_ = max(b + self.J0 + 1, int(np.searchsorted(Ft, b, side="left")))
        hi_ = b + m
        return lo_ > hi_ or badA[hi_ + 1] - badA[lo_] == 0

    def E_prefix_exact(self, b, idx):
        m, K = self.m_hi, self.K
        dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th = self.P_[idx]
        if self.lo["h"] + 1 - min(Rsa, max(0, Rst - b)) < K + 3:
            return 0
        j = np.arange(1, m + 1)
        si = b + j
        bad = (np.minimum(Fwa[si], np.maximum(0, Fwt[si] - b)) + np.minimum(self.cap, 2 * np.minimum(Gba[si], np.maximum(0, Gbt[si] - b)))
               + K * (th[si] <= 2 * gr))
        ok = bad <= j - 1
        return m if ok.all() else int(np.argmin(ok))

    def LE(self, b):
        for idx in self.order:
            if self.E_full_fast(b, idx):
                self.order.remove(idx); self.order.insert(0, idx)
                return self.m_hi
        best = 0
        for idx in self.order:
            best = max(best, self.E_prefix_exact(b, idx))
            if best == self.m_hi:
                break
        return best

    def E_l1(self, b):
        t = -((-(self.lo["beta0"] - b)) // 2)
        for Rhi, trho in self.l1:
            if min(int(self.absRho(np.array([t]))[0]), max(0, int(Rhi(trho(np.array([t])))[0]) - b)) == 0:
                return True
        return False

    # ---- Family R ----
    def Rok(self, b, l):
        s0 = max(l + 1, self.gc + 1)
        if b + 1 < s0:
            return False
        sub = b + 1 - s0
        T = self.lo["T"]
        if l == 1:
            t = np.array([-((-(T - 1)) // 2)])
            return min(int(self.absN(t)[0]), max(0, int(self.RC(self.tauN(t))[0]) - sub)) == 0
        j = np.arange(1, l + 1)
        thR = T - l - j + 1
        W = np.minimum(self.absCR(thR), np.maximum(0, self.RC(thR) - sub))
        KC = self.KC
        for gN, Rst, Rsa in self.PR:
            if s0 - min(Rsa, max(0, Rst - sub)) < KC + 3:
                continue
            tt = thR - gN
            Bd = np.minimum(2 * KC + 2, 2 * np.minimum(self.absN(tt), np.maximum(0, self.RC(self.tauN(tt)) - sub)))
            dd = KC * (thR <= 2 * gN)
            if np.all(W + Bd + dd <= j - 1):
                return True
        return False


def block_uncovered(Nlo, Nhi, sigsets=((5, 7, 11, 13), (5, 7, 11), (5, 7)), limit=5):
    certs = [BlockCert(Nlo, Nhi, P) for P in sigsets]
    C0 = certs[0]
    unc = []
    for b in range(C0.bmax + 1):
        if not any(C.E_l1(b) or C.Rok(b, 1) for C in certs):
            unc.append((b, 1, 0))
            if len(unc) >= limit: break
            continue
        L = 0
        for C in certs:
            L = max(L, C.LE(b))
            if L == C0.m_hi: break
        if L == C0.m_hi:
            continue
        for l in range(max(2, L + 1), C0.m_hi + 1):
            if any(C.Rok(b, l) for C in certs):
                continue
            unc.append((b, l, L)); break
        if len(unc) >= limit:
            break
    return unc


if __name__ == "__main__":
    lo, hi, eps, out = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    n = lo
    with open(out, "a") as fh:
        while n <= hi:
            w = max(0, int(eps * n))
            t = time.time()
            u = block_uncovered(n, min(hi, n + w))
            rec = {"Nlo": n, "Nhi": min(hi, n + w), "n_uncovered": len(u), "uncovered": [list(x) for x in u], "sec": round(time.time() - t, 2)}
            if u and w > 0:
                # retry with a narrower block
                eps2 = eps / 4
                rec["retry"] = True
                w = max(0, int(eps2 * n))
                u = block_uncovered(n, min(hi, n + w))
                rec.update({"Nhi": min(hi, n + w), "n_uncovered": len(u), "uncovered": [list(x) for x in u]})
            fh.write(json.dumps(rec) + "\n"); fh.flush()
            n = rec["Nhi"] + 1


def _E_prefix_atleast(C, b, need):
    """True if Family E certifies every l <= need for budget b (early exit)."""
    for idx in C.order:
        if C.E_full_fast(b, idx):
            return True
    for idx in C.order:
        if C.E_prefix_exact(b, idx) >= need:
            return True
    return False


def block_uncovered2(Nlo, Nhi, sigsets=((5, 7, 11, 13), (5, 7, 11), (5, 7)), limit=5):
    """Same semantics as block_uncovered, using monotonicity of Family R in b (binary search per l)."""
    certs = [BlockCert(Nlo, Nhi, P) for P in sigsets]
    C0 = certs[0]
    m, bmax = C0.m_hi, C0.bmax
    INF = bmax + 1
    bR = [INF] * (m + 1)              # bR[l] = least b with some R certificate for (b,l)
    for l in range(1, m + 1):
        best = INF
        for C in certs:
            lo_b = max(l, C.gc)       # need b+1 >= s0
            if lo_b > bmax or not C.Rok(bmax, l):
                continue
            a, z = lo_b, bmax           # Rok(z) True; find least b with Rok True
            while a < z:
                mid = (a + z) // 2
                if C.Rok(mid, l):
                    z = mid
                else:
                    a = mid + 1
            best = min(best, a)
        bR[l] = best
    # need_l(b) = max{ l : b < bR[l] }
    unc = []
    for b in range(bmax + 1):
        need = 0
        for l in range(m, 0, -1):
            if b < bR[l]:
                need = l
                break
        if need == 0:
            continue
        if need >= 1 and not (any(C.E_l1(b) for C in certs) or b >= bR[1]):
            unc.append((b, 1, 0))
            if len(unc) >= limit: break
            continue
        if need == 1:
            continue
        if not any(_E_prefix_atleast(C, b, need) for C in certs):
            unc.append((b, need, -1))
            if len(unc) >= limit: break
    return unc
