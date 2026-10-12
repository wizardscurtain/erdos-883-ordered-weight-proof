"""Amended l=1 coverage (audit A-2): for each n and b, l=1 is covered iff for some discount delta
R(tau_rho(ceil(theta1/2))) <= b  [Family E], or Family R l=1 applies:
b+1 >= gC+1 and RC(tauN(ceil((T-1)/2))) <= b+1-(gC+1)."""
import sys, json
import numpy as np
from cert4 import build4, tau_from, spf_table
from cert7 import gC

def l1_uncovered(n, spf):
    D = build4(n, spf)
    h = D["h"]; bmax = D["nodd"] - h - 1
    Dl = D["Delta"]
    deltas = sorted(set([0, Dl // 8, Dl // 4, (3 * Dl) // 8, Dl // 2, (5 * Dl) // 8, (3 * Dl) // 4, Dl]))
    b = np.arange(0, bmax + 1, dtype=np.int64)
    th1 = D["beta0"] - b
    t = -((-th1) // 2)
    okE = np.zeros(bmax + 1, dtype=bool)
    for dl in deltas:
        c = D["base"] - np.where(D["is3"], 0, dl)
        cs = np.sort(c)
        Rv = len(cs) - np.searchsorted(cs, tau_from(D["rho"], c, t), side="left")
        okE |= (Rv <= b)
    gc = gC(n)
    csR = np.sort(D["cR"])
    RC = len(csR) - np.searchsorted(csR, tau_from(D["rhoN"], D["cR"], np.array([-((-(D["T"] - 1)) // 2)])), side="left")[0]
    okR = (b + 1 >= gc + 1) & (RC <= b + 1 - (gc + 1))
    unc = [int(x) for x in np.nonzero(~(okE | okR))[0]]
    return unc

if __name__ == "__main__":
    ns = [int(x) for x in open(sys.argv[1]).read().split()]
    spf = spf_table(max(ns))
    out = open(sys.argv[2], "w")
    for n in ns:
        u = l1_uncovered(n, spf)
        out.write(json.dumps({"n": n, "l1_uncovered": u[:20], "n_l1_uncovered": len(u)}) + "\n")
    print("done")
