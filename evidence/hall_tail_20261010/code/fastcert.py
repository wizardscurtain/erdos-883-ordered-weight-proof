"""Vectorized tables + window-accelerated Family-E check (falls back to the exact per-b check).

build_fast(n, P) returns the same dict as cert4.build4(n, spf, SIG=P) (validated by test_fast()).
FastCert(n, P): Cert8 with tables from build_fast and LE(b) accelerated:
  for ranks j <= J0 the exact terms are evaluated; for j > J0 the sufficient condition
  (Ft(s) - b)^+ + cap + dd(s) <= j - 1 is used, which for Ft(s) >= b reads A(s) = s-1-Ft(s)-cap-dd(s) >= 0
  and for Ft(s) < b holds automatically once j-1 >= cap + K (ensured by J0 = cap + K + 1).
  If the fast test fails, the exact cert9 prefix computation is used for that b.
"""
import numpy as np
import cert9

_SPF = None


def spf_upto(N):
    global _SPF
    if _SPF is None or len(_SPF) <= N:
        spf = np.arange(N + 1, dtype=np.int64)
        for i in range(2, int(N ** 0.5) + 1):
            if spf[i] == i:
                blk = spf[i * i::i]
                mask = blk == np.arange(i * i, N + 1, i)
                blk[mask] = i
                spf[i * i::i] = blk
        _SPF = spf
    return _SPF


def mobius_upto(N):
    mu = np.ones(N + 1, dtype=np.int64)
    spf = spf_upto(N)
    isp = (spf == np.arange(N + 1)) & (np.arange(N + 1) >= 2)
    for p in np.nonzero(isp)[0]:
        mu[p::p] *= -1
        mu[p * p::p * p] = 0
    return mu


def build_fast(n, P=(5, 7, 11, 13)):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    beta0 = q - q // 3
    Delta = q // 3
    v = np.arange(1, n + 1, 2, dtype=np.int64)          # odd vertices; index i <-> v = 2i+1
    nv = len(v)
    is3 = (v % 3 == 0)
    spf = spf_upto(n)
    primes = [int(p) for p in np.nonzero((spf == np.arange(len(spf))) & (np.arange(len(spf)) >= 2))[0] if p <= n]
    # signature mask
    mask = np.zeros(nv, dtype=np.int64)
    for bit, p in enumerate(P):
        mask |= ((v % p == 0).astype(np.int64) << bit)
    # lambda sums over primes >=5 outside P (odd multiples of p: v = p, 3p, 5p, ... -> indices (p-1)/2 + p*k)
    lam3 = np.zeros(nv, dtype=np.int64); lamA = np.zeros(nv, dtype=np.int64); lamN = np.zeros(nv, dtype=np.int64)
    for p in primes:
        if p < 5 or p in P:
            continue
        idx = slice((p - 1) // 2, nv, p)
        lam3[idx] += q // p - q // (3 * p)
        lamA[idx] += q // p
        lamN[idx] += n // p
    # sigma per mask
    def cc(N, ps):
        tot = 0
        L = len(ps)
        for mm in range(1 << L):
            d = 1; bits = 0
            for i in range(L):
                if mm >> i & 1:
                    d *= ps[i]; bits += 1
            tot += (-1) ** bits * (N // d)
        return tot
    nm = 1 << len(P)
    sig3 = np.zeros(nm, dtype=np.int64); sigA = np.zeros(nm, dtype=np.int64); sigN = np.zeros(nm, dtype=np.int64)
    for mm in range(nm):
        S = [p for i, p in enumerate(P) if mm >> i & 1]
        sig3[mm] = (q - q // 3) - cc(q, [3] + S)
        sigA[mm] = q - cc(q, S)
        sigN[mm] = n - cc(n, S)
    # exact rho via Mobius over odd squarefree d | rad(v):  g(v) = sum mu(d) floor(q/d), g3 = sum mu(d) floor(q/3d)
    mu = mobius_upto(n)
    g = np.zeros(nv, dtype=np.int64); g3 = np.zeros(nv, dtype=np.int64); gN = np.zeros(nv, dtype=np.int64)
    for d in range(1, n + 1, 2):
        if mu[d] == 0:
            continue
        idx = slice((d - 1) // 2, nv, d)
        g[idx] += mu[d] * (q // d)
        g3[idx] += mu[d] * (q // (3 * d))
        gN[idx] += mu[d] * (n // d)
    # #{k<=q: 3!|k, gcd(k,v)=1}: O3 v -> g(v) ; C v -> g(v) - g3(v)
    cop3 = np.where(is3, g, g - g3)
    rho = beta0 - cop3
    base = np.where(is3, sig3[mask] + 2 * lam3, sigA[mask] + 2 * lamA)
    isC = ~is3
    cR = (sigN[mask] + 2 * lamN)[isC]
    rhoN = (n - gN)[isC]
    keys = set(zip(is3.tolist(), mask.tolist()))
    keysC = set(mask[isC].tolist())
    return dict(n=n, q=q, m=m, h=h, T=T, beta0=beta0, Delta=Delta, nodd=nv,
                is3=is3, base=base, rho=rho, cR=cR, rhoN=rhoN, K=len(keys), KC=len(keysC))


def test_fast(ns=(30, 97, 300, 1001, 2999), sets=((5, 7, 11, 13), (5, 7), (), (5,), (7, 11, 13))):
    import cert4
    ok = True
    for n in ns:
        spf = cert4.spf_table(n)
        for P in sets:
            A = cert4.build4(n, spf, SIG=P)
            B = build_fast(n, P)
            for k in ("is3", "base", "rho", "cR", "rhoN"):
                if not np.array_equal(np.asarray(A[k]), np.asarray(B[k])):
                    print("MISMATCH", n, P, k); ok = False
            for k in ("K", "KC", "m", "h", "T", "beta0", "Delta", "nodd"):
                if A[k] != B[k]:
                    print("MISMATCH", n, P, k, A[k], B[k]); ok = False
    print("BUILD_FAST_MATCH" if ok else "BUILD_FAST_FAIL")
    return ok


if __name__ == "__main__":
    test_fast()
