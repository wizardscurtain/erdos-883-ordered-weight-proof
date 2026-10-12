"""Exact CEGAR verifier v2 for Erdos #883(i): fixed n, odd cycle length k, fixed b, and an upper bound
cmax on c = #(odd multiples of 3 in [n] missing from A).

WLOG reductions (each maps counterexamples to counterexamples with the same |A| and b, and never
increases c):
  * support compression x -> y with supp(x) a proper subset of supp(y), restricted to moves with
    (2 in supp x) == (2 in supp y) (keeps b).  If 3 | x then 3 | y, and if 3 does not divide x the move can
    only add an odd multiple of 3, so c never increases.  Iterating gives an up-closed counterexample.
  * twins (equal support) are interchangeable: each support class is a prefix (increasing order).
  * large-prime automorphisms: for primes p < p' > sqrt(n) with floor(n/p) == floor(n/p'), the map
    k*p <-> k*p' is an automorphism of the coprime graph on [n] preserving parity, 3-divisibility,
    support classes (and their internal order) and up-closure.  Hence some compressed counterexample is
    the lex-max of its orbit, so we may impose (x_{kp})_k >=_lex (x_{kp'})_k for consecutive p < p' of
    a bucket (one global variable order: (k, p) increasing within the bucket).
UNSAT => no counterexample with that (size, b, c <= cmax).
"""
import sys, json, random, time
from math import gcd, isqrt
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
import exact883


def lex_geq(pool, xs, ys):
    """Clauses for (xs) >=_lex (ys) (lists of literals of equal length), standard chain encoding."""
    cl = []
    # e_i : prefixes equal up to i-1 (e_0 = True)
    prev = None
    for i, (x, y) in enumerate(zip(xs, ys)):
        # if prefix equal then x_i >= y_i :  prev -> (x or not y)
        if prev is None:
            cl.append([x, -y])
        else:
            cl.append([-prev, x, -y])
        if i == len(xs) - 1:
            break
        e = pool.id(("lexeq", tuple(xs), tuple(ys), i))
        # e -> prev and (x == y);  (prev and x==y) -> e is not needed for soundness of >=
        if prev is not None:
            cl.append([-e, prev])
        cl.append([-e, x, -y]); cl.append([-e, -x, y])
        # need: prev & (x == y) -> e  (otherwise e could be False and drop constraints -> still sound
        # but weaker); add it to keep the constraint full strength
        if prev is None:
            cl.append([e, -x, -y]); cl.append([e, x, y])
        else:
            cl.append([e, -prev, -x, -y]); cl.append([e, -prev, x, y])
        prev = e
    return cl


class Model2(exact883.Model):
    def __init__(self, n, size=None, b=None, cmax=None, symm=True):
        super().__init__(n, size, b)
        self.cmax = cmax
        self.symm = symm

    def buckets(self):
        n = self.n
        r = isqrt(n)
        ps = [p for p in range(r + 1, n + 1) if all(p % d for d in range(2, isqrt(p) + 1)) and p > 3 and p * p > n]
        B = {}
        for p in ps:
            B.setdefault(n // p, []).append(p)
        return {K: v for K, v in B.items() if len(v) >= 2}

    def base_clauses(self):
        cl = super().base_clauses()
        n = self.n
        if self.cmax is not None:
            o3 = [self.var[v] for v in range(3, n + 1, 6)]
            h = len(o3)
            cl.extend(CardEnc.atleast(lits=o3, bound=h - self.cmax, vpool=self.pool, encoding=EncType.seqcounter).clauses)
        if self.symm:
            for K, ps in self.buckets().items():
                for p, p2 in zip(ps, ps[1:]):
                    xs = [self.var[k * p] for k in range(1, K + 1)]
                    ys = [self.var[k * p2] for k in range(1, K + 1)]
                    cl.extend(lex_geq(self.pool, xs, ys))
        return cl


def verify(n, k, size=None, seed=0, max_iter=10 ** 7, b=None, cmax=None, symm=True, time_limit=None):
    M = Model2(n, size, b, cmax, symm)
    rng = random.Random(seed)
    st = dict(n=n, k=k, size=M.size, b=b, cmax=cmax, symm=symm, iters=0, exact_calls=0)
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=M.base_clauses()) as s:
        while st["iters"] < max_iter:
            if time_limit and time.time() - t0 > time_limit:
                st["result"] = "TIME_LIMIT"; return st
            if not s.solve():
                st["result"] = "VERIFIED_NO_COUNTEREXAMPLE"; return st
            mdl = set(x for x in s.get_model() if x > 0)
            A = [v for v in range(1, n + 1) if M.var[v] in mdl]
            st["iters"] += 1
            cyc = exact883.find_cycle_heuristic(A, k, rng)
            if cyc is None:
                st["exact_calls"] += 1
                cyc = exact883.find_cycle_exact(A, k)
                if cyc is False:
                    st["result"] = "COUNTEREXAMPLE"; st["A"] = A; return st
            assert exact883.check_cycle(cyc, A, k)
            cnt = {}
            for v in cyc:
                cnt[M.cls_of[v]] = cnt.get(M.cls_of[v], 0) + 1
            s.add_clause([-M.var[M.classes[S][t - 1]] for S, t in cnt.items()])
    st["result"] = "ITER_LIMIT"
    return st


if __name__ == "__main__":
    n, k = int(sys.argv[1]), int(sys.argv[2])
    size = None if sys.argv[3] == "-" else int(sys.argv[3])
    b = None if sys.argv[4] == "-" else int(sys.argv[4])
    cmax = None if sys.argv[5] == "-" else int(sys.argv[5])
    symm = len(sys.argv) <= 6 or sys.argv[6] != "nosymm"
    t = time.time()
    st = verify(n, k, size, b=b, cmax=cmax, symm=symm)
    st["sec"] = round(time.time() - t, 2)
    st.pop("A", None) if st["result"] != "COUNTEREXAMPLE" else None
    print(json.dumps(st))
