"""Fast coverage scanner for families E5 (even connectors, separators) and R5(l) (skeleton in X).

For each n and each missing-even budget b:
  L_E(b) = max over parameters (delta, gr) of the largest l certified by E5 (ranks j<=l).
  covered(b) iff L_E(b) = m, or every l in (L_E(b), m] satisfies l <= b and R5(l) certifies for some gN.
Outputs per n: number of uncovered b, first few uncovered (b, l, L_E).
"""
import sys, json
import numpy as np
from cert4 import build4, tau_from, spf_table


def prep(D):
    c_cache = {}
    Dl = D["Delta"]
    deltas = sorted(set([0, Dl // 8, Dl // 4, (3 * Dl) // 8, Dl // 2, (5 * Dl) // 8, (3 * Dl) // 4, Dl]))
    grs = sorted(set(int(x) for x in np.quantile(D["rho"], np.linspace(0.02, 0.9, 24))))
    gNs = sorted(set(int(x) for x in np.quantile(D["rhoN"], np.linspace(0.02, 0.9, 24))))
    P = []
    m, h = D["m"], D["h"]
    bmax = D["nodd"] - h - 1
    smax = bmax + m + 2
    s = np.arange(0, smax + 1, dtype=np.int64)
    for dl in deltas:
        c = D["base"] - np.where(D["is3"], 0, dl)
        cs = np.sort(c)
        R = lambda t: len(cs) - np.searchsorted(cs, t, side="left")
        keyw = np.where(D["is3"], c, c - (Dl - dl))
        th = D["beta0"] - s + 1               # theta as a function of s=b+j
        Fw = R(tau_from(keyw, c, th))
        for gr in grs:
            Gb = R(tau_from(D["rho"], c, th - gr))
            Rsep = int(R(tau_from(D["rho"], c, np.array([gr + 1])))[0])
            bmin = Rsep - (h + 1) + D["K"] + 3        # separator applicability: b >= bmin
            P.append((dl, gr, Fw, Gb, bmin))
    # R5 tables
    csR = np.sort(D["cR"])
    RC = lambda t: len(csR) - np.searchsorted(csR, t, side="left")
    PR = []
    for gN in gNs:
        RsepN = int(RC(tau_from(D["rhoN"], D["cR"], np.array([gN + 1])))[0])
        PR.append((gN, RsepN))
    return P, PR, RC


def LE_for_b(D, P, b, order):
    m = D["m"]
    j = np.arange(1, m + 1, dtype=np.int64)
    cap = 2 * D["K"] + 2
    best = 0
    besti = None
    for idx in order:
        dl, gr, Fw, Gb, bmin = P[idx]
        if b < bmin:
            continue
        sidx = b + j
        bad = 2 * np.maximum(0, Fw[sidx] - b) + np.minimum(cap, 2 * np.maximum(0, Gb[sidx] - b))
        okj = bad <= j - 1
        L = m if okj.all() else int(np.argmin(okj))
        if L > best:
            best, besti = L, idx
            if best == m:
                break
    return best, besti


def R5_ok(D, PR, RC, b, l):
    if l > b:
        return False
    sub = b - l
    j = np.arange(1, l + 1, dtype=np.int64)
    thR = D["T"] - l - j + 1
    W = 2 * np.maximum(0, RC(thR) - sub)
    capC = 2 * D["KC"] + 2
    for gN, RsepN in PR:
        nonsep = max(0, RsepN - sub)
        if l + 1 > D["KC"] + 3 and (l + 1) - nonsep < D["KC"] + 3:
            continue
        Bd = np.minimum(capC, 2 * np.maximum(0, RC(tau_from(D["rhoN"], D["cR"], thR - gN)) - sub))
        if np.all(W + Bd <= j - 1):
            return True
    return False


def scan_n(n, spf):
    D = build4(n, spf)
    m, h = D["m"], D["h"]
    bmax = D["nodd"] - h - 1
    P, PR, RC = prep(D)
    order = list(range(len(P)))
    unc = []
    for b in range(bmax + 1):
        L, bi = LE_for_b(D, P, b, order)
        if bi is not None:
            order.remove(bi)
            order.insert(0, bi)
        if L == m:
            continue
        bad_l = None
        for l in range(L + 1, m + 1):
            if not R5_ok(D, PR, RC, b, l):
                bad_l = l
                break
        if bad_l is not None:
            unc.append((b, bad_l, L))
    return dict(n=n, m=m, h=h, bmax=bmax, n_uncovered=len(unc), uncovered=unc[:12])


if __name__ == "__main__":
    lo, hi, step = map(int, sys.argv[1:4])
    out = sys.argv[4]
    spf = spf_table(hi)
    rows = []
    for n in range(lo, hi + 1, step):
        rows.append(scan_n(n, spf))
    json.dump(rows, open(out, "w"))
    U = [r["n"] for r in rows if r["n_uncovered"]]
    print("scanned", len(rows), "uncovered n count", len(U), "max uncovered n", max(U) if U else None)
