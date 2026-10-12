"""Exact CEGAR verifier for Erdos #883(i) at a fixed n and odd cycle length k.

Decides: does every A subset [n] with |A| = T(n)+1 (or a given size) contain C_k in its coprime graph?

Reduction (WLOG for a counterexample, per fixed k): support compression. If A has no C_k and
x in A, y notin A with supp(x) a proper subset of supp(y), then A - x + y has no C_k (N(y) subset N(x)).
Iterating (sum of |supp| strictly increases) gives a counterexample that is up-closed under strict
support inclusion; twins (equal support) are interchangeable, so each support class is a prefix.

SAT model over x_v: |A| = size; prefix within classes; x_{S,first} -> x_{S',last} for S' = S + {p}.
Loop: solve; if SAT, search a C_k in G(A) (constructive heuristic, then exact SAT search);
if found, block its class pattern  OR_S not x_{S, t_S}; if no C_k exists, report a counterexample.
UNSAT => verified (no counterexample of that size, hence none larger).
"""
import sys, json, random, time
from math import gcd
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def rad_primes(v):
    ps, p = [], 2
    while p * p <= v:
        if v % p == 0:
            ps.append(p)
            while v % p == 0:
                v //= p
        p += 1
    if v > 1:
        ps.append(v)
    return tuple(ps)


class Model:
    def __init__(self, n, size=None, b=None):
        self.n = n
        self.T = n // 2 + n // 3 - n // 6
        self.size = self.T + 1 if size is None else size
        self.supp = {v: rad_primes(v) for v in range(1, n + 1)}
        classes = {}
        for v in range(1, n + 1):
            classes.setdefault(self.supp[v], []).append(v)
        self.classes = classes          # support tuple -> sorted list of members
        self.pool = IDPool()
        self.var = {v: self.pool.id(("x", v)) for v in range(1, n + 1)}
        self.cls_of = {v: self.supp[v] for v in range(1, n + 1)}
        self.b = b

    def base_clauses(self):
        cl = []
        # prefix symmetry inside classes
        for S, mem in self.classes.items():
            for i in range(len(mem) - 1):
                cl.append([-self.var[mem[i + 1]], self.var[mem[i]]])
        # compression along covering pairs S -> S+{p}; with fixed b only parity-preserving moves
        # (2 in S iff 2 in S') are WLOG, since they keep the number of missing evens fixed
        keys = set(self.classes)
        for S, mem in self.classes.items():
            for S2 in keys:
                if len(S2) == len(S) + 1 and set(S) < set(S2):
                    if self.b is not None and ((2 in S) != (2 in S2)):
                        continue
                    cl.append([-self.var[mem[0]], self.var[self.classes[S2][-1]]])
        if self.b is not None:
            q = self.n // 2
            ev = [self.var[v] for v in range(2, self.n + 1, 2)]
            cl.extend(CardEnc.equals(lits=ev, bound=q - self.b, vpool=self.pool, encoding=EncType.seqcounter).clauses)
        lits = [self.var[v] for v in range(1, self.n + 1)]
        enc = CardEnc.equals(lits=lits, bound=self.size, vpool=self.pool, encoding=EncType.seqcounter)
        cl.extend(enc.clauses)
        return cl


def find_cycle_heuristic(A, k, rng, tries=60):
    """Randomized skeleton + bipartite matching (odd skeleton of l+1 vertices with a coprime closing pair,
    connectors = any other vertices of A). Returns list of vertices or None."""
    l = (k - 1) // 2
    Aset = list(A)
    odds = [v for v in Aset if v % 2]
    if len(odds) < l + 1:
        return None
    # loss proxy: number of A-elements not coprime
    for t in range(tries):
        # pick coprime pair
        o2 = odds[:]
        rng.shuffle(o2)
        pair = None
        for i in range(len(o2)):
            for j in range(i + 1, min(len(o2), i + 40)):
                if gcd(o2[i], o2[j]) == 1:
                    pair = (o2[i], o2[j]); break
            if pair: break
        if not pair:
            return None
        rest = [v for v in odds if v not in pair]
        # prefer smooth odds (few prime factors), with randomness
        rest.sort(key=lambda v: (len(rad_primes(v)) + rng.random() * (1 + t / 10)))
        skel_mid = rest[:l - 1]
        if len(skel_mid) < l - 1:
            return None
        # order: group by smallest prime factor signature, random tie-break
        skel_mid.sort(key=lambda v: (rad_primes(v), rng.random()) if t % 2 == 0 else rng.random())
        skel = [pair[0]] + skel_mid + [pair[1]]
        used = set(skel)
        others = [u for u in Aset if u not in used]
        gaps = [(skel[i], skel[i + 1]) for i in range(l)]
        # bipartite matching gaps -> others
        adj = [[u for u in others if gcd(u, a * b) == 1] for a, b in gaps]
        match_u = {}
        def aug(i, seen):
            for u in adj[i]:
                if u in seen: continue
                seen.add(u)
                if u not in match_u or aug(match_u[u], seen):
                    match_u[u] = i
                    return True
            return False
        order = sorted(range(l), key=lambda i: len(adj[i]))
        ok = True
        for i in order:
            if not aug(i, set()):
                ok = False; break
        if ok:
            conn = {i: u for u, i in match_u.items()}
            cyc = []
            for i in range(l):
                cyc += [skel[i], conn[i]]
            cyc.append(skel[l])
            return cyc
    return None


def find_cycle_exact(A, k, time_budget=None):
    """Exact SAT search for a cycle of length k in G(A): position variables."""
    A = sorted(A)
    pool = IDPool()
    P = lambda v, i: pool.id(("p", v, i))
    cl = []
    for i in range(k):
        lits = [P(v, i) for v in A]
        cl += CardEnc.equals(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    for v in A:
        lits = [P(v, i) for i in range(k)]
        cl += CardEnc.atmost(lits=lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    # adjacency: position i and i+1 must be coprime
    nonadj = {v: [u for u in A if u != v and gcd(u, v) > 1] for v in A}
    for i in range(k):
        j = (i + 1) % k
        for v in A:
            for u in nonadj[v]:
                cl.append([-P(v, i), -P(u, j)])
    # symmetry: smallest vertex at position 0 not enforced (keep simple)
    with Solver(name="cadical153", bootstrap_with=cl) as s:
        if s.solve():
            mdl = set(x for x in s.get_model() if x > 0)
            cyc = [None] * k
            for v in A:
                for i in range(k):
                    if P(v, i) in mdl:
                        cyc[i] = v
            return cyc
        return False


def check_cycle(cyc, A, k):
    if cyc is None or len(cyc) != k or len(set(cyc)) != k:
        return False
    if not set(cyc) <= set(A):
        return False
    return all(gcd(cyc[i], cyc[(i + 1) % k]) == 1 for i in range(k))


def verify(n, k, size=None, seed=0, verbose=False, max_iter=10 ** 6, b=None):
    M = Model(n, size, b)
    rng = random.Random(seed)
    stats = dict(n=n, k=k, size=M.size, b=b, iters=0, exact_calls=0)
    with Solver(name="cadical153", bootstrap_with=M.base_clauses()) as s:
        while stats["iters"] < max_iter:
            if not s.solve():
                stats["result"] = "VERIFIED_NO_COUNTEREXAMPLE"
                return stats
            mdl = set(x for x in s.get_model() if x > 0)
            A = [v for v in range(1, n + 1) if M.var[v] in mdl]
            stats["iters"] += 1
            cyc = find_cycle_heuristic(A, k, rng)
            if cyc is None:
                stats["exact_calls"] += 1
                cyc = find_cycle_exact(A, k)
                if cyc is False:
                    stats["result"] = "COUNTEREXAMPLE"
                    stats["A"] = A
                    return stats
            assert check_cycle(cyc, A, k), "invalid cycle"
            # block class pattern
            cnt = {}
            for v in cyc:
                cnt[M.cls_of[v]] = cnt.get(M.cls_of[v], 0) + 1
            clause = [-M.var[M.classes[S][t - 1]] for S, t in cnt.items()]
            s.add_clause(clause)
    stats["result"] = "ITER_LIMIT"
    return stats


if __name__ == "__main__":
    n, k = int(sys.argv[1]), int(sys.argv[2])
    size = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != "-" else None
    b = int(sys.argv[4]) if len(sys.argv) > 4 else None
    t = time.time()
    st = verify(n, k, size, b=b)
    st["sec"] = round(time.time() - t, 2)
    print(json.dumps(st))
