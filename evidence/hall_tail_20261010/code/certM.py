"""Family M (mixed skeleton) for the corner b < l, b >= g_C.

Given (n,b,l) and the adversary's c = #missing odd multiples of 3 (|X| = b+c+1, |O3 cap A| = h-c):
  if |X| < g_C+1 the family does not apply; if |X| >= s0 := max(l+1, g_C+1) this is Family R
  (z=0, skeleton pool = s0 smallest-cR elements of X, subX = |X|-s0; audit D-1 / external review fix);
  else (g_C+1 <= |X| <= l) z = l+1-|X| odd multiples of 3 are used,
  X-part = all of X (subX = 0), O3-part = z smallest-c3 vertices of O3 cap A (sub3 = h-c-z).
Arrangement: a, s, chunk, s, ..., chunk, s, o_1, s, o_2, ..., s, o_z, s, a'  (C separators s by rhoN<=gN).
Bounds (rank j<=l):
  C within chunk (all-unused pool, base T-l):        bad => cR >= thR_j = T-l-j+1
  C chunk end / a / a' next to a C separator:          bad => rhoN >= thR_j - gN
  C separator - C separator (left-over):               bad iff thR_j <= 2gN, count <= K_C + z
  O3 vertex o between two C separators (3-free evens, base beta0-b): bad => rho(o) >= th_j - grho,
       grho = max{rho(x) : x in C, rhoN(x) <= gN},  th_j = beta0-b-j+1;  count <= min(2z, 2(R3(tau3(th_j-grho)) - sub3)^+)
Requirements: |X| >= g_C+1 (coprime pair in X-part by L2), separators NsC >= K_C + 3 + z.
"""
import numpy as np
from cert4 import tau_from


class MFam:
    def __init__(self, cert):
        self.C = cert
        D = cert.D
        self.D = D
        isC = ~D["is3"]
        self.rhoC = D["rho"][isC]           # 3-free even loss of C vertices (same order as cR, rhoN)
        o3 = D["is3"]
        self.c3 = D["base"][o3]
        self.rho3 = D["rho"][o3]
        cs3 = np.sort(self.c3)
        self.R3 = lambda t: len(cs3) - np.searchsorted(cs3, t, side="left")
        ordr = np.argsort(self.rho3, kind="stable")
        self._rs3 = self.rho3[ordr]
        self._suf3 = np.append(np.minimum.accumulate(self.c3[ordr][::-1])[::-1], 1 << 60)
        self.tau3 = lambda t: self._suf3[np.searchsorted(self._rs3, t, side="left")]
        self.gNs = cert.gNs
        self.grho = {gN: int(self.rhoC[D["rhoN"] <= gN].max()) if (D["rhoN"] <= gN).any() else 0 for gN in self.gNs}
        self.RsepN = {gN: int(cert.RC(cert.tauN(np.array([gN + 1])))[0]) for gN in self.gNs}
        rN = np.sort(D["rhoN"]); self.absN = lambda t: len(rN) - np.searchsorted(rN, t, side="left")   # #C with rhoN >= t
        cR = np.sort(D["cR"]); self.absR = lambda t: len(cR) - np.searchsorted(cR, t, side="left")
        r3 = np.sort(self.rho3); self.abs3 = lambda t: len(r3) - np.searchsorted(r3, t, side="left")

    def ok_c(self, b, l, c):
        C, D = self.C, self.D
        h, T = C.h, C.T
        X = b + c + 1
        if X < C.gc + 1:
            return False
        s0 = max(l + 1, C.gc + 1)
        if X >= s0:
            # Family R (audit D-1 fix): skeleton pool = s0 smallest-cR elements of X so that L2 gives a coprime pair
            z, subX, xpart = 0, X - s0, s0
        else:
            z, subX, xpart = l + 1 - X, 0, X
        if z > h - c:
            return False
        sub3 = h - c - z
        j = np.arange(1, l + 1, dtype=np.int64)
        thR = T - l - j + 1
        th = D["beta0"] - b - j + 1
        W = 2 * np.minimum(self.absR(thR), np.maximum(0, C.RC(thR) - subX))
        KC = D["KC"]
        for gN in self.gNs:
            NsC = xpart - min(int(self.absN(np.array([gN + 1]))[0]), max(0, self.RsepN[gN] - subX))
            if NsC < KC + 3 + z:
                continue
            Bd = np.minimum(2 * KC + 2, 2 * np.minimum(self.absN(thR - gN), np.maximum(0, C.RC(C.tauN(thR - gN)) - subX)))
            dd = (KC + z) * (thR <= 2 * gN)
            if z > 0:
                O = np.minimum(2 * z, 2 * np.minimum(self.abs3(th - self.grho[gN]), np.maximum(0, self.R3(self.tau3(th - self.grho[gN])) - sub3)))
            else:
                O = 0
            if np.all(W + Bd + dd + O <= j - 1):
                return True
        return False

    def ok(self, b, l):
        h = self.C.h
        for c in range(0, h + 1):
            if not self.ok_c(b, l, c):
                return False
        return True
