"""Separator ("spine") certificates E4 / R3 for Erdos #883(i).

E4(n,b; delta, gamma)   [even connectors]
  cost   O3: c = sig3(S) + 2*lam3(v)          C: c = sigA(S) + 2*lamA(v) - delta   (0<=delta<=Delta)
  Y0 = h+1 smallest-cost odd vertices of A; V = l+1 smallest-cost of Y0 plus a coprime pair.
  separators: vertices with c <= gamma; arrangement a, s0, B1', s1, ..., Br', sr, a'
  within-block (same type & signature, non-separators):
      O3 bad => c >= theta ; C bad => c >= theta + Delta - delta     (theta = beta0 - b - j + 1)
  boundary gaps (always one separator endpoint, 3-free even pool):
      bad => rho(v) >= theta - gr,  gr = max{rho(s) : c(s) <= gamma}
  bad_j <= 2*(R(tau_w(theta)) - b)^+ + min(2K+2, 2*(R(tau_rho(theta-gr)) - b)^+)
  applicability: Ns = h+1 - (R(gamma+1)-b)^+ >= K + 3
R3(n,b; gamma)  [b >= h, skeleton in X, any unused vertex as connector]
  cost cR = sigN(S) + 2*lamN(x); X0 = h+1 smallest; sub = b - h
  within bad => cR >= thR (thR = T - m - j + 1); boundary bad => rhoN(v) >= thR - gN
  bad_j <= 2*(RC(thR)-sub)^+ + min(2KC+2, 2*(RC(tauN(thR-gN)) - sub)^+)
  applicability: NsC = h+1 - (RC(gamma+1)-sub)^+ >= KC + 3
"""
import sys
import json
import numpy as np
from cert2 import spf_table, primes_of, count_coprime, SIG, tail

BIG = 1 << 60


def build4(n, spf, SIG=SIG):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    beta0 = q - q // 3
    Delta = q // 3
    sig3, sigA, sigN = {}, {}, {}
    for mask in range(1 << len(SIG)):
        S = tuple(p for i, p in enumerate(SIG) if mask >> i & 1)
        sig3[S] = (q - q // 3) - count_coprime(q, (3,) + S)
        sigA[S] = q - count_coprime(q, S)
        sigN[S] = n - count_coprime(n, S)
    is3, base, rho = [], [], []
    cR, rhoN = [], []
    keys, keysC = set(), set()
    for v in range(1, n + 1, 2):
        ps = [p for p in primes_of(v, spf) if p != 3]
        S = tuple(p for p in SIG if p in ps)
        Lg = [p for p in ps if p not in SIG]
        rho.append((q - q // 3) - count_coprime(q, [3] + ps))
        if v % 3 == 0:
            is3.append(True)
            base.append(sig3[S] + 2 * sum(q // p - q // (3 * p) for p in Lg))
            keys.add((3, S))
        else:
            is3.append(False)
            base.append(sigA[S] + 2 * sum(q // p for p in Lg))
            keys.add((1, S))
            cR.append(sigN[S] + 2 * sum(n // p for p in Lg))
            rhoN.append(n - count_coprime(n, ps))
            keysC.add(S)
    A = lambda x: np.array(x, dtype=np.int64)
    return dict(n=n, q=q, m=m, h=h, T=T, beta0=beta0, Delta=Delta, nodd=(n + 1) // 2,
                is3=np.array(is3), base=A(base), rho=A(rho), cR=A(cR), rhoN=A(rhoN),
                K=len(keys), KC=len(keysC))


def tau_from(key, cost, thr_vals):
    """tau(t) = min{cost[i] : key[i] >= t}, vectorized over t (any shape). BIG if empty."""
    order = np.argsort(key, kind="stable")
    ks, cs = key[order], cost[order]
    suf = np.append(np.minimum.accumulate(cs[::-1])[::-1], BIG)
    return suf[np.searchsorted(ks, thr_vals, side="left")]


def E4_ok(D, b, delta, gamma, return_slack=False):
    m, h = D["m"], D["h"]
    c = D["base"] - np.where(D["is3"], 0, delta)
    cs = np.sort(c)
    R = lambda t: len(cs) - np.searchsorted(cs, t, side="left")
    # applicability: separators
    Ns = h + 1 - max(0, int(R(np.array([gamma + 1]))[0]) - b)
    if Ns < D["K"] + 3:
        return (False, None) if return_slack else False
    sepmask = c <= gamma
    gr = int(D["rho"][sepmask].max()) if sepmask.any() else 0
    j = np.arange(1, m + 1, dtype=np.int64)
    th = D["beta0"] - b - j + 1
    # within-block rough set: O3 with c>=th, C with c>=th+Delta-delta  (key for tau: shifted cost)
    keyw = np.where(D["is3"], c, c - (D["Delta"] - delta))
    tw = tau_from(keyw, c, th)
    within = 2 * np.maximum(0, R(tw) - b)
    tb = tau_from(D["rho"], c, th - gr)
    bnd = np.minimum(2 * D["K"] + 2, 2 * np.maximum(0, R(tb) - b))
    bad = within + bnd
    ok = bool(np.all(bad <= j - 1))
    if return_slack:
        return ok, int(np.min(j - 1 - bad))
    return ok


def R3_ok(D, b, gamma, return_slack=False):
    m, h = D["m"], D["h"]
    if b < h:
        return (False, None) if return_slack else False
    sub = b - h
    cs = np.sort(D["cR"])
    RC = lambda t: len(cs) - np.searchsorted(cs, t, side="left")
    NsC = h + 1 - max(0, int(RC(np.array([gamma + 1]))[0]) - sub)
    if NsC < D["KC"] + 3:
        return (False, None) if return_slack else False
    sep = D["cR"] <= gamma
    gN = int(D["rhoN"][sep].max()) if sep.any() else 0
    j = np.arange(1, m + 1, dtype=np.int64)
    thR = D["T"] - m - j + 1
    within = 2 * np.maximum(0, RC(thR) - sub)
    tb = tau_from(D["rhoN"], D["cR"], thR - gN)
    bnd = np.minimum(2 * D["KC"] + 2, 2 * np.maximum(0, RC(tb) - sub))
    bad = within + bnd
    ok = bool(np.all(bad <= j - 1))
    if return_slack:
        return ok, int(np.min(j - 1 - bad))
    return ok


def param_grid(D):
    Dl = D["Delta"]
    deltas = sorted(set([0, Dl // 4, Dl // 2, (3 * Dl) // 4, Dl]))
    # gamma grid: quantiles of base cost distribution
    qs = np.quantile(D["base"], [0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7]).astype(np.int64)
    gammas = sorted(set(int(x) for x in qs) | {0, D["beta0"] // 20, D["beta0"] // 10, D["beta0"] // 5})
    return deltas, gammas


def coverage4(n, spf):
    D = build4(n, spf)
    h = D["h"]
    bmax = D["nodd"] - h - 1
    deltas, gammas = param_grid(D)
    gR = sorted(set(int(x) for x in np.quantile(D["cR"], [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7])))
    cov = []
    how = []
    for b in range(bmax + 1):
        done = None
        for dl in deltas:
            for g in gammas:
                if E4_ok(D, b, dl, g - (0 if True else 0)):
                    done = ("E4", dl, g)
                    break
            if done:
                break
        if not done and b >= h:
            for g in gR:
                if R3_ok(D, b, g):
                    done = ("R3", g)
                    break
        cov.append(done is not None)
        how.append(done)
    unc = [b for b in range(bmax + 1) if not cov[b]]
    return dict(n=n, m=D["m"], h=h, bmax=bmax, n_uncovered=len(unc), uncovered=unc[:30],
                uncovered_last=unc[-10:], how_sample={b: how[b] for b in range(0, bmax + 1, max(1, bmax // 10))})


if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1].split(",")]
    out = sys.argv[2]
    spf = spf_table(max(ns))
    rows = [coverage4(n, spf) for n in ns]
    json.dump(rows, open(out, "w"), indent=1, default=str)
    for r in rows:
        print(r["n"], "uncovered", r["n_uncovered"], r["uncovered"][:12], r["uncovered_last"])
