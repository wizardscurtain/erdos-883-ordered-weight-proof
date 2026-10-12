"""End-to-end constructive test of Families G / GA (FAMILY_G.md) on small n.

For certified (b,l) (full rank conditions, computed here from scratch) and many sets A (random and adversarial)
with that b, build the path exactly as in the proof, the lists, and find an SDR by bipartite matching; any failure
would refute the lemma.  Also checks the resulting cycle is a genuine C_{2l+1} in the coprime graph of A."""
import sys, math, random, json
from math import gcd


def primes_of(v):
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


def setup(n):
    q, m = n // 2, n // 6
    h = n // 3 - n // 6
    T = n // 2 + n // 3 - n // 6
    odds = list(range(1, n + 1, 2))
    Gq, Gn = {}, {}
    for v in odds:
        ps = primes_of(v)
        g = 1.0
        for p in ps:
            g *= 1 - 1 / p
        Gq[v] = g - 2 ** len(ps) / math.sqrt(2 * q)
        Gn[v] = g - 2 ** len(ps) / math.sqrt(2 * n)
    return dict(n=n, q=q, m=m, h=h, T=T, odds=odds, Gq=Gq, Gn=Gn)


def certified(D, b, l, fam):
    import bisect
    n, q, T = D["n"], D["q"], D["T"]
    key = "sq" if fam == "G" else "sn"
    if key not in D:
        D[key] = sorted((D["Gq"] if fam == "G" else D["Gn"]).values())
    vals = D[key]
    for j in range(1, l + 1):
        t = math.sqrt((b + j - 1) / q) if fam == "G" else math.sqrt((n - T + l + j - 1) / n)
        N = bisect.bisect_right(vals, t)
        w = max(0, N - b)
        if w + (1 if w > 0 else 0) > j - 1:
            return False
    return True


def matching(lists):
    match = {}
    def aug(i, seen):
        for u in lists[i]:
            if u in seen:
                continue
            seen.add(u)
            if u not in match or aug(match[u], seen):
                match[u] = i
                return True
        return False
    for i in sorted(range(len(lists)), key=lambda i: len(lists[i])):
        if not aug(i, set()):
            return None
    return {i: u for u, i in match.items()}


def build_cycle(D, A, l, fam, rng):
    Aset = set(A)
    Y = [v for v in A if v % 2]
    Gt = D["Gq"] if fam == "G" else D["Gn"]
    Ysorted = sorted(Y, key=lambda v: (-Gt[v], rng.random()))
    Y0 = Ysorted[:D["h"] + 1]
    pairs = [(x, y) for i, x in enumerate(Y0) for y in Y0[i + 1:] if gcd(x, y) == 1]
    assert pairs, "L1 violated"
    a, a2 = rng.choice(pairs)
    rest = [v for v in Y0 if v not in (a, a2)]
    rest.sort(key=lambda v: (-Gt[v], rng.random()))
    internal = rest[:l - 1]
    path = [a] + internal + [a2]
    V = set(path)
    if fam == "G":
        pool = [u for u in A if u % 2 == 0]
    else:
        pool = [u for u in A if u not in V]
    lists = [[u for u in pool if gcd(u, path[i] * path[i + 1]) == 1] for i in range(l)]
    M = matching(lists)
    if M is None:
        return None
    cyc = []
    for i in range(l):
        cyc += [path[i], M[i]]
    cyc.append(path[l])
    assert len(set(cyc)) == 2 * l + 1 and set(cyc) <= Aset
    assert all(gcd(cyc[i], cyc[(i + 1) % len(cyc)]) == 1 for i in range(len(cyc)))
    return cyc


def random_A(D, b, rng, mode):
    n, q, h = D["n"], D["q"], D["h"]
    evens = list(range(2, n + 1, 2))
    odds = D["odds"]
    nY = h + 1 + b
    if mode == "uniform":
        Y = rng.sample(odds, nY)
        ev = rng.sample(evens, q - b)
    elif mode == "lowG":            # adversary: odd part = lowest-G odds, missing evens = smooth ones
        Y = sorted(odds, key=lambda v: (D["Gq"][v], rng.random()))[:nY]
        ev = sorted(evens, key=lambda v: (-len(primes_of(v)), rng.random()))[b:]
    else:                           # mixed: half lowest-G, half random
        k = nY // 2
        low = sorted(odds, key=lambda v: D["Gq"][v])[:k]
        others = [v for v in odds if v not in set(low)]
        Y = low + rng.sample(others, nY - k)
        ev = rng.sample(evens, q - b)
    return sorted(Y + ev)


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    stats = dict(tests=0, failures=0, certified_pairs=0)
    for n in [int(x) for x in sys.argv[2:]] or [240, 360, 480, 600]:
        D = setup(n)
        bmax = len(D["odds"]) - D["h"] - 1
        for fam in ("G", "GA"):
            cert = [(b, l) for b in range(bmax + 1) for l in range(1, D["m"] + 1) if certified(D, b, l, fam)]
            stats["certified_pairs"] += len(cert)
            sample = rng.sample(cert, min(40, len(cert)))
            for b, l in sample:
                for mode in ("uniform", "lowG", "mixed"):
                    for _ in range(3):
                        A = random_A(D, b, rng, mode)
                        assert len(A) == D["T"] + 1
                        stats["tests"] += 1
                        if build_cycle(D, A, l, fam, rng) is None:
                            stats["failures"] += 1
                            print("FAIL", n, fam, b, l, mode)
        print(json.dumps(dict(n=n, **stats)), flush=True)
    print("CONSTRUCT_OK" if stats["failures"] == 0 else "CONSTRUCT_FAIL")
