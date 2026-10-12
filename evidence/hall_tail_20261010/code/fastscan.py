"""Fast coverage scan: tables from fastcert.build_fast, Family-E prefix via window test with exact fallback.
Covered(b,l) semantics identical to cert10.coverage_multi (validated on overlap)."""
import sys, json, time
import numpy as np
import cert10, fastcert

SS_DEFAULT = ((5, 7, 11, 13), (5, 7, 11), (5, 7))


class FastCert(cert10.Cert8):
    def __init__(self, n, sig, full_grid=False):
        D = fastcert.build_fast(n, sig)
        super().__init__(n, None, sig=sig, full_grid=full_grid, D=D)
        m = self.m
        K = D["K"]; self.cap = 2 * K + 2
        self.J0 = min(m, self.cap + K + 1)
        # window data per parameter: A(s) < 0 prefix counts, and s_F(b) via Ft (tail) array
        self.win = []
        for (dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th) in self.P:
            s = np.arange(len(Fwt))
            dd = K * (th <= 2 * gr)
            A = s - 1 - Fwt - self.cap - dd
            badA = np.concatenate([[0], np.cumsum(A < 0)])
            self.win.append((badA, Fwt))

    def fast_full(self, b, idx):
        """True if parameter idx certifies all ranks j<=m for budget b (sufficient test)."""
        D, m, K = self.D, self.m, self.D["K"]
        dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th = self.P[idx]
        Ns = self.h + 1 - min(Rsa, max(0, Rst - b))
        if Ns < K + 3:
            return False
        # exact for j <= J0
        j = np.arange(1, self.J0 + 1)
        sidx = b + j
        bad = (np.minimum(Fwa[sidx], np.maximum(0, Fwt[sidx] - b))
               + np.minimum(self.cap, 2 * np.minimum(Gba[sidx], np.maximum(0, Gbt[sidx] - b)))
               + K * (th[sidx] <= 2 * gr))
        if not np.all(bad <= j - 1):
            return False
        if self.J0 >= m:
            return True
        badA, Ft = self.win[idx]
        lo = b + self.J0 + 1
        sF = int(np.searchsorted(Ft, b, side="left"))   # first s with Ft(s) >= b
        lo = max(lo, sF)
        hi = b + m
        if lo > hi:
            return True
        return badA[hi + 1] - badA[lo] == 0

    def LE(self, b):
        for idx in self.order:
            if self.fast_full(b, idx):
                self.order.remove(idx); self.order.insert(0, idx)
                return self.m
        return super().LE(b)


def coverage_fast(n, sigsets=SS_DEFAULT, full_grid=False):
    certs = [FastCert(n, sg, full_grid) for sg in sigsets]
    C0 = certs[0]
    unc = []
    for b in range(C0.bmax + 1):
        if not any(C.E_l1(b) or C.Rok(b, 1) for C in certs):
            unc.append((b, 1, 0)); continue
        L = 0
        for C in certs:
            L = max(L, C.LE(b))
            if L == C0.m: break
        for l in range(max(2, L + 1), C0.m + 1):
            if any(C.Rok(b, l) or C.M_ok(b, l) for C in certs):
                continue
            unc.append((b, l, L)); break
    return unc


if __name__ == "__main__":
    lo, hi, step, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    with open(out, "a") as fh:
        for n in range(lo, hi + 1, step):
            t = time.time()
            u = coverage_fast(n)
            fh.write(json.dumps({"n": n, "n_uncovered": len(u), "uncovered": [list(x) for x in u[:12]], "sec": round(time.time() - t, 2)}) + "\n"); fh.flush()
