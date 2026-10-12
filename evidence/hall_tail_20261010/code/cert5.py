"""E5: like E4 but separators chosen by rho <= gr directly; their availability is counted
through the exact tau map: #(Y0 with rho > gr) <= (R(tau_rho(gr+1)) - b)^+.
R5: like R3 with separators by rhoN <= gN; target-aware variant R5l for l <= b (b<h allowed):
    skeleton inside X (|X| >= b+1 >= l+1), sub = b - l, thR(l) = T - l - j + 1, j <= l.
E5l: E5 checked only for ranks j <= l.
"""
import sys, json
import numpy as np
from cert4 import build4, tau_from, spf_table

def E5_bad(D, b, delta, gr):
    m, h = D["m"], D["h"]
    c = D["base"] - np.where(D["is3"], 0, delta)
    cs = np.sort(c)
    R = lambda t: len(cs) - np.searchsorted(cs, t, side="left")
    nonsep_bound = max(0, int(R(tau_from(D["rho"], c, np.array([gr + 1])))[0]) - b)
    Ns = h + 1 - nonsep_bound
    if Ns < D["K"] + 3:
        return None
    j = np.arange(1, m + 1, dtype=np.int64)
    th = D["beta0"] - b - j + 1
    keyw = np.where(D["is3"], c, c - (D["Delta"] - delta))
    within = 2 * np.maximum(0, R(tau_from(keyw, c, th)) - b)
    bnd = np.minimum(2 * D["K"] + 2, 2 * np.maximum(0, R(tau_from(D["rho"], c, th - gr)) - b))
    return within + bnd   # bad_j bound for j = 1..m

def R5_bad(D, b, l, gN):
    """skeleton inside X with |X| >= b+1; valid for l <= b (and l <= m)."""
    if l > b:
        return None
    sub = b - l
    cs = np.sort(D["cR"])
    RC = lambda t: len(cs) - np.searchsorted(cs, t, side="left")
    nonsep = max(0, int(RC(tau_from(D["rhoN"], D["cR"], np.array([gN + 1])))[0]) - sub)
    if (l + 1) - nonsep < D["KC"] + 3 and l + 1 > D["KC"] + 3:
        return None
    j = np.arange(1, l + 1, dtype=np.int64)
    thR = D["T"] - l - j + 1
    within = 2 * np.maximum(0, RC(thR) - sub)
    bnd = np.minimum(2 * D["KC"] + 2, 2 * np.maximum(0, RC(tau_from(D["rhoN"], D["cR"], thR - gN)) - sub))
    return within + bnd

def grids(D):
    Dl = D["Delta"]
    deltas = sorted(set([0, Dl // 4, Dl // 2, (3 * Dl) // 4, Dl]))
    grs = sorted(set(int(x) for x in np.quantile(D["rho"], [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8])))
    gNs = sorted(set(int(x) for x in np.quantile(D["rhoN"], [0.2, 0.3, 0.4, 0.5, 0.6, 0.7])))
    return deltas, grs, gNs

def coverage5(n, spf):
    D = build4(n, spf)
    m, h = D["m"], D["h"]
    bmax = D["nodd"] - h - 1
    deltas, grs, gNs = grids(D)
    unc = []   # list of (b, l_first_uncovered)
    for b in range(bmax + 1):
        # best E5 bad profile: for each l we need prefix j<=l ok; compute max l certified by some param
        Ecert_l = 0
        for dl in deltas:
            for gr in grs:
                bad = E5_bad(D, b, dl, gr)
                if bad is None:
                    continue
                okj = bad <= np.arange(0, m)
                L = m if okj.all() else int(np.argmin(okj))  # largest l with all j<=l ok
                Ecert_l = max(Ecert_l, L)
                if Ecert_l == m: break
            if Ecert_l == m: break
        if Ecert_l == m:
            continue
        # remaining targets l in (Ecert_l, m]: try R5 for l <= b
        bad_l = None
        for l in range(Ecert_l + 1, m + 1):
            okl = False
            for gN in gNs:
                bb = R5_bad(D, b, l, gN)
                if bb is not None and bool(np.all(bb <= np.arange(0, l))):
                    okl = True; break
            if not okl:
                bad_l = l; break
        if bad_l is not None:
            unc.append((b, bad_l, Ecert_l))
    return dict(n=n, m=m, h=h, bmax=bmax, n_uncovered=len(unc), uncovered=unc[:20])

if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1].split(",")]
    spf = spf_table(max(ns))
    rows = [coverage5(n, spf) for n in ns]
    json.dump(rows, open(sys.argv[2], "w"), indent=1)
    for r in rows: print(r["n"], r["n_uncovered"], r["uncovered"][:10])
