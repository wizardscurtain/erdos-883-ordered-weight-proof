"""Exploratory (design-only) margin landscape of Family E at large n: for budgets b = beta*m and the
best parameter in the grid, report min over ranks j >= J0 of (j-1-bad_j)/m and whether all ranks pass."""
import sys, numpy as np, fastscan
n = int(sys.argv[1]); sig = tuple(int(x) for x in sys.argv[2].split(',')) if len(sys.argv) > 2 else (5,7,11,13)
C = fastscan.FastCert(n, sig)
m, K = C.m, C.D["K"]
rows = []
for beta in [0, 0.1, 0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6, 1.7]:
    b = int(beta * m)
    if b > C.bmax: break
    best = None
    for (dl, gr, Fwt, Fwa, Gbt, Gba, Rst, Rsa, th) in C.P:
        Ns = C.h + 1 - min(Rsa, max(0, Rst - b))
        if Ns < K + 3: continue
        j = np.arange(1, m + 1); s = b + j
        bad = (np.minimum(Fwa[s], np.maximum(0, Fwt[s] - b)) + np.minimum(C.cap, 2 * np.minimum(Gba[s], np.maximum(0, Gbt[s] - b))) + K * (th[s] <= 2 * gr))
        sl = (j - 1 - bad)
        ok = bool(np.all(sl >= 0))
        J0 = C.J0
        j5 = max(J0, m // 20); mn = float(np.min((sl/np.maximum(1,j-1))[j5:]))
        # first rank where slack < 0
        key = (ok, mn)
        if best is None or key > best[0]:
            best = (key, dl, gr, int(np.argmin(sl)) + 1)
    rows.append((beta, best))
    print(f"n={n} beta={beta:.2f} b={b}: all_ok={best[0][0]} min_rel_slack(j>=0.05m)={best[0][1]:.4f} delta={best[1]} gr={best[2]} argmin_j={best[3]}")
