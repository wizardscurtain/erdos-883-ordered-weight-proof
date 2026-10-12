"""Second-solver cross-check of the exact base: rerun every verified (n, k, b[, cmax]) with a different SAT solver
(default glucose4) and a different random seed for the cycle heuristic."""
import sys, json, time
import pysat.solvers as PS
import exact883, exact883b
NAME = sys.argv[2] if len(sys.argv) > 2 else "glucose4"
def S(name=None, bootstrap_with=None):
    return PS.Solver(name=NAME, bootstrap_with=bootstrap_with)
exact883.Solver = S
exact883b.Solver = S
out = open(sys.argv[1], "a")
for f, mod in (("exact_base.jsonl", "a"), ("exact_base2.jsonl", "b")):
    for line in open(f):
        r = json.loads(line)
        if r["result"] != "VERIFIED_NO_COUNTEREXAMPLE":
            continue
        t = time.time()
        if mod == "a":
            st = exact883.verify(r["n"], r["k"], None, seed=7, b=r["b"], max_iter=10 ** 7)
        else:
            st = exact883b.verify(r["n"], r["k"], None, seed=7, b=r["b"], cmax=r["cmax"])
        st.pop("A", None)
        st.update(solver=NAME, sec=round(time.time() - t, 2), source=f)
        out.write(json.dumps(st) + "\n"); out.flush()
