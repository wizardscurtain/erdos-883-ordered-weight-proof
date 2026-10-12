"""Independent plain-loop implementation of the Family G / GA rank conditions (no numpy, trial division).
For each (b,l): G(b,l) iff for all 1<=j<=l: w + [w>0] <= j-1, w = max(0, #{odd v<=n: Gt_q(v) <= t_j} - b),
t_j = sqrt((b+j-1)/q);  GA(b,l) same with Gt_n and t_j = sqrt((n-T+l+j-1)/n).
Checks the claims used by famG2: (i) b+l <= y1 => G(b,l); (ii) b >= N_GA => GA(b,l) for all l<=m;
(iii) famG2.ok => every (b,l) covered."""
import sys, math, json


def factor_primes(v):
    ps, d = [], 2
    while d * d <= v:
        if v % d == 0:
            ps.append(d)
            while v % d == 0:
                v //= d
        d += 1
    if v > 1:
        ps.append(v)
    return ps


def run(n):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    odds = list(range(1, n + 1, 2))
    bmax = len(odds) - h - 1
    Gq, Gn = [], []
    for v in odds:
        ps = factor_primes(v)
        g = 1.0
        for p in ps:
            g *= (1 - 1 / p)
        Gq.append(g - 2 ** len(ps) / math.sqrt(2 * q))
        Gn.append(g - 2 ** len(ps) / math.sqrt(2 * n))
    def cnt(arr, t):
        return sum(1 for x in arr if x <= t)
    # memoise counts by threshold
    memo_q, memo_n = {}, {}
    def Nq(y):
        if y not in memo_q:
            memo_q[y] = cnt(Gq, math.sqrt(y / q))
        return memo_q[y]
    def Nn(y):
        if y not in memo_n:
            memo_n[y] = cnt(Gn, math.sqrt(y / n))
        return memo_n[y]
    def Gok(b, l):
        for j in range(1, l + 1):
            w = max(0, Nq(b + j - 1) - b)
            if w + (1 if w > 0 else 0) > j - 1:
                return False
        return True
    def GAok(b, l):
        for j in range(1, l + 1):
            w = max(0, Nn(n - T + l + j - 1) - b)
            if w + (1 if w > 0 else 0) > j - 1:
                return False
        return True
    # per-b maximal l for G (prefix property: the j-th condition does not depend on l)
    lG = []
    for b in range(bmax + 1):
        L = 0
        for j in range(1, m + 1):
            w = max(0, Nq(b + j - 1) - b)
            if w + (1 if w > 0 else 0) > j - 1:
                break
            L = j
        lG.append(L)
    # GA(b,l) is monotone in b (up) and in l (down): two-pointer for lGA[b] = max l with GA(b,l)
    lGA, L = [], 0
    for b in range(bmax + 1):
        while L < m and GAok(b, L + 1):
            L += 1
        lGA.append(L)
    unc = [(b, max(lG[b], lGA[b]) + 1) for b in range(bmax + 1) if max(lG[b], lGA[b]) < m]
    # y1 and N_GA computed independently
    y1 = 0 if Nq(0) > 0 else next((y for y in range(1, len(odds) + 1) if Nq(y) >= y), len(odds) + 1)
    tA = math.sqrt((n - T + 2 * m - 1) / n)
    NGA = cnt(Gn, tA)
    claim_i = all(lG[b] >= min(m, y1 - b) for b in range(0, min(bmax + 1, y1)))
    claim_ii = (NGA > bmax) or all(GAok(NGA, l) for l in range(1, m + 1))
    return dict(n=n, y1=y1, NGA=NGA, ok_fast_criterion=NGA <= y1 - m, n_unc_b=len(unc), first_unc=unc[:3],
                claim_i=claim_i, claim_ii=claim_ii)


if __name__ == "__main__":
    for n in [int(x) for x in sys.argv[1:]]:
        print(json.dumps(run(n)), flush=True)
