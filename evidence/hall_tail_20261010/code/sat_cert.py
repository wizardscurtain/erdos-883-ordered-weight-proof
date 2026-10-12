"""Independent SAT certificate builder/checker for the exact base (does not import exact883/exact883b).

For an instance (n, k, b, cmax, symm) and a logged list of blocking clauses with canonical cycles:
  1. checks every canonical cycle (k distinct vertices in [1,n], cyclically consecutive coprime) and that the clause is
     exactly { not x_{S[t_S]} } for the support classes S used by the cycle with multiplicities t_S;
  2. builds the base CNF from scratch with its own encodings: prefix order inside support classes; parity-preserving
     covering compression clauses; |A| = T+1; #evens = q-b; (optional) #odd multiples of 3 >= h-cmax; (optional)
     lex-leader constraints for the large-prime bucket automorphisms;
  3. solves base + blocking clauses with Glucose 4 (proof logging), writes the CNF and the DRUP proof, checks the proof
     with drat-trim (built from source), converts it to LRAT and checks the LRAT with lrat-check.
UNSAT with a checked proof + valid witnesses => no threshold set with this (size, b[, c <= cmax]) avoids C_k
(given the counterexample-preserving reductions in the version 1.1 paper, section 6).
"""
import sys, os, json, hashlib, subprocess, time
from math import gcd, isqrt
from pysat.solvers import Solver

TOOLS = os.environ.get("DRAT_TOOLS", os.path.join(os.path.dirname(__file__), "..", ".tools", "drat-trim"))


def primes_of(v):
    out, d = [], 2
    while d * d <= v:
        if v % d == 0:
            out.append(d)
            while v % d == 0:
                v //= d
        d += 1
    if v > 1:
        out.append(v)
    return tuple(out)


class CNF:
    def __init__(self, nvars):
        self.top = nvars
        self.clauses = []

    def new(self):
        self.top += 1
        return self.top

    def add(self, c):
        self.clauses.append(list(c))

    def atmost(self, xs, k):
        """Sinz sequential counter: sum(xs) <= k."""
        n = len(xs)
        if k >= n:
            return
        if k == 0:
            for x in xs:
                self.add([-x])
            return
        s = [[self.new() for _ in range(k)] for _ in range(n)]
        self.add([-xs[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, n):
            self.add([-xs[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-xs[i], -s[i - 1][k - 1]])

    def atleast(self, xs, k):
        self.atmost([-x for x in xs], len(xs) - k)

    def exactly(self, xs, k):
        self.atmost(xs, k)
        self.atleast(xs, k)

    def lex_geq(self, xs, ys):
        """(xs) >=_lex (ys): e_i = 'prefixes before i equal'."""
        prev = None
        for i, (x, y) in enumerate(zip(xs, ys)):
            self.add(([-prev] if prev else []) + [x, -y])
            if i == len(xs) - 1:
                break
            e = self.new()
            # e <-> prev & (x == y)
            if prev:
                self.add([-e, prev])
            self.add([-e, x, -y]); self.add([-e, -x, y])
            self.add(([-prev] if prev else []) + [e, x, y])
            self.add(([-prev] if prev else []) + [e, -x, -y])
            prev = e


def base_cnf(n, b, cmax, symm, size=None):
    q, h = n // 2, n // 3 - n // 6
    size = n // 2 + n // 3 - n // 6 + 1 if size is None else size
    supp = {v: primes_of(v) for v in range(1, n + 1)}
    classes = {}
    for v in range(1, n + 1):
        classes.setdefault(supp[v], []).append(v)
    F = CNF(n)
    for S, mem in classes.items():
        for a, c in zip(mem, mem[1:]):
            F.add([-c, a])                                   # prefix: x_c -> x_a  (a < c)
    for S, mem in classes.items():
        for S2, mem2 in classes.items():
            if len(S2) == len(S) + 1 and set(S) < set(S2) and ((2 in S) == (2 in S2)):
                F.add([-mem[0], mem2[-1]])                  # parity-preserving covering compression
    F.exactly(list(range(1, n + 1)), size)
    F.exactly(list(range(2, n + 1, 2)), q - b)
    if cmax is not None:
        F.atleast(list(range(3, n + 1, 6)), h - cmax)
    if symm:
        r = isqrt(n)
        ps = [p for p in range(r + 1, n + 1) if len(primes_of(p)) == 1 and primes_of(p)[0] == p and p > 3 and p * p > n]
        buckets = {}
        for p in ps:
            buckets.setdefault(n // p, []).append(p)
        for K, bp in buckets.items():
            if len(bp) < 2:
                continue
            for p, p2 in zip(bp, bp[1:]):
                F.lex_geq([kk * p for kk in range(1, K + 1)], [kk * p2 for kk in range(1, K + 1)])
    return F, classes, supp, size


def check_witnesses(n, k, blocks, classes, supp):
    for blk in blocks:
        cyc, lits = blk["cycle"], blk["lits"]
        assert len(cyc) == k and len(set(cyc)) == k and all(1 <= v <= n for v in cyc), "bad cycle shape"
        assert all(gcd(cyc[i], cyc[(i + 1) % k]) == 1 for i in range(k)), "cycle edge not coprime"
        cnt = {}
        for v in cyc:
            cnt[supp[v]] = cnt.get(supp[v], 0) + 1
        for S, t in cnt.items():
            assert sorted(v for v in cyc if supp[v] == S) == classes[S][:t], "cycle not canonical"
        assert sorted(lits) == sorted(classes[S][t - 1] for S, t in cnt.items()), "clause does not match cycle"
    return True


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def certify(blockfile, outdir):
    R = json.load(open(blockfile))
    assert R["result"] == "UNSAT"
    n, k, b, cmax, symm = R["n"], R["k"], R["b"], R["cmax"], R["symm"]
    F, classes, supp, size = base_cnf(n, b, cmax, symm)
    assert size == R["size"]
    check_witnesses(n, k, R["blocks"], classes, supp)
    for blk in R["blocks"]:
        F.add([-v for v in blk["lits"]])
    base = os.path.join(outdir, R["id"])
    cnf = base + ".cnf"
    with open(cnf, "w") as fh:
        fh.write(f"p cnf {F.top} {len(F.clauses)}\n")
        for c in F.clauses:
            fh.write(" ".join(map(str, c)) + " 0\n")
    t = time.time()
    with Solver(name="glucose4", with_proof=True, bootstrap_with=F.clauses) as s:
        sat = s.solve()
        assert not sat, "base + blocks is SAT: certificate incomplete"
        proof = s.get_proof()
    drat = base + ".drat"
    with open(drat, "w") as fh:
        fh.write("\n".join(proof) + "\n")
    lrat = base + ".lrat"
    d = subprocess.run([os.path.join(TOOLS, "drat-trim"), cnf, drat, "-L", lrat, "-t", "20000"], capture_output=True, text=True)
    drat_ok = "s VERIFIED" in d.stdout
    l = subprocess.run([os.path.join(TOOLS, "lrat-check"), cnf, lrat], capture_output=True, text=True)
    lrat_ok = ("c VERIFIED" in l.stdout) or ("s VERIFIED" in l.stdout)
    rec = dict(id=R["id"], n=n, k=k, b=b, cmax=cmax, symm=symm, n_blocks=len(R["blocks"]), vars=F.top, clauses=len(F.clauses),
               witnesses_ok=True, drat_trim_verified=drat_ok, lrat_check_verified=lrat_ok,
               cnf_sha256=sha(cnf), drat_sha256=sha(drat), lrat_sha256=sha(lrat) if os.path.exists(lrat) else None,
               blocks_sha256=sha(blockfile), sec=round(time.time() - t, 2),
               drat_tail=d.stdout.strip().splitlines()[-1:] if d.stdout else [], lrat_tail=l.stdout.strip().splitlines()[-1:] if l.stdout else [])
    return rec


if __name__ == "__main__":
    outdir = sys.argv[1]
    files = sys.argv[2:]
    with open(os.path.join(outdir, "certificates.jsonl"), "a") as out:
        for f in files:
            rec = certify(f, outdir)
            out.write(json.dumps(rec) + "\n"); out.flush()
            print(rec["id"], rec["drat_trim_verified"], rec["lrat_check_verified"], rec["n_blocks"], rec["sec"], flush=True)
