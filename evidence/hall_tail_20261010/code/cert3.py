"""Probe-3 per-n certificates for Erdos #883(i): E'' and R'' with exact boundary maps.

Same as cert2 (families E', R') except boundary gaps are bounded through the exact
per-vertex union-bound loss:
  E'': rho(v)  = #{k<=q : 3 !| k, gcd(k,v)>1};    boundary bad => max rho >= ceil(theta/2)
  R'': rhoN(x) = #{u<=n : gcd(u,x)>1};             boundary bad => max rhoN >= ceil(thetaR/2)
and #{v in skeleton : rho(v) >= t} <= max(0, R(tau(t)) - budget), with
tau(t) = min{ cost(v) : rho(v) >= t } (exact, +inf if empty).
"""
import sys
import json
import numpy as np
from cert2 import spf_table, primes_of, count_coprime, SIG, tail, ceil_half

BIG = 1 << 60


def build3(n, spf):
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
    cE, rhoE, cR, rhoR = [], [], [], []
    keysE, keysC = set(), set()
    for v in range(1, n + 1, 2):
        ps = [p for p in primes_of(v, spf) if p != 3]
        S = tuple(p for p in SIG if p in ps)
        Lg = [p for p in ps if p not in SIG]
        rhoE.append((q - q // 3) - count_coprime(q, [3] + ps))
        if v % 3 == 0:
            cE.append(sig3[S] + 2 * sum(q // p - q // (3 * p) for p in Lg))
            keysE.add(("O3", S))
        else:
            cE.append(sigA[S] + 2 * sum(q // p for p in Lg) - Delta)
            keysE.add(("C", S))
            cR.append(sigN[S] + 2 * sum(n // p for p in Lg))
            rhoR.append(n - count_coprime(n, ps))
            keysC.add(S)
    cE, rhoE, cR, rhoR = map(lambda a: np.array(a, dtype=np.int64), (cE, rhoE, cR, rhoR))
    return dict(n=n, q=q, m=m, h=h, T=T, beta0=beta0, Delta=Delta, nodd=(n + 1) // 2,
                cE=cE, rhoE=rhoE, cR=cR, rhoR=rhoR, cE_sorted=np.sort(cE), cR_sorted=np.sort(cR),
                KE=len(keysE), KC=len(keysC))


def tau_map(cost, rho):
    """Return function t -> min{cost[i] : rho[i] >= t} (vectorized), BIG if empty."""
    order = np.argsort(rho, kind="stable")
    rs = rho[order]
    cs = cost[order]
    sufmin = np.minimum.accumulate(cs[::-1])[::-1]
    sufmin = np.append(sufmin, BIG)

    def f(t):
        idx = np.searchsorted(rs, t, side="left")
        return sufmin[idx]
    return f


def coverage3(n, spf):
    D = build3(n, spf)
    m, h = D["m"], D["h"]
    bmax = D["nodd"] - h - 1
    j = np.arange(1, m + 1, dtype=np.int64)[None, :]
    tauE = tau_map(D["cE"], D["rhoE"])
    tauR = tau_map(D["cR"], D["rhoR"])
    b = np.arange(0, bmax + 1, dtype=np.int64)[:, None]
    th = D["beta0"] - b - j + 1
    within = 2 * np.maximum(0, tail(D["cE_sorted"], th) - b)
    bnd = np.minimum(D["KE"], 2 * np.maximum(0, tail(D["cE_sorted"], tauE(ceil_half(th))) - b))
    badE = within + bnd
    okE = np.all(badE <= j - 1, axis=1)
    slackE = np.min((j - 1) - badE, axis=1)
    okR = np.zeros(bmax + 1, dtype=bool)
    slackR = np.full(bmax + 1, -10**9, dtype=np.int64)
    if bmax >= h:
        sub = np.arange(h, bmax + 1, dtype=np.int64)[:, None] - h
        thR = D["T"] - m - j + 1
        withinR = 2 * np.maximum(0, tail(D["cR_sorted"], thR) - sub)
        bndR = np.minimum(D["KC"], 2 * np.maximum(0, tail(D["cR_sorted"], tauR(ceil_half(thR))) - sub))
        badR = withinR + bndR
        okR[h:] = np.all(badR <= j - 1, axis=1)
        slackR[h:] = np.min((j - 1) - badR, axis=1)
    cov = okE | okR
    unc = [int(x) for x in np.nonzero(~cov)[0]]
    Eprefix = int(np.argmin(okE)) - 1 if not np.all(okE) else int(bmax)
    return dict(n=n, m=m, h=h, bmax=int(bmax), E_all_below_h=bool(np.all(okE[:h])),
                R_all_from_h=bool(np.all(okR[h:])) if bmax >= h else True,
                n_uncovered=len(unc), uncovered=unc[:20], E_maxprefix=Eprefix,
                minslack_E_below_h=int(np.min(slackE[:h])) if h > 0 else None,
                minslack_R_from_h=int(np.min(slackR[h:])) if bmax >= h else None,
                minslack_cov=int(np.min(np.maximum(np.where(okE, slackE, -10**9), np.where(okR, slackR, -10**9)))))


if __name__ == "__main__":
    lo, hi, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    spf = spf_table(hi)
    rows = [coverage3(n, spf) for n in range(lo, hi + 1)]
    json.dump(rows, open(out, "w"))
    print("done", len(rows))
