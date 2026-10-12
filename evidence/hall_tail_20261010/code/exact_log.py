"""Re-run the exact-base CEGAR for one instance and log every blocking clause with a canonical witness cycle.

Output (JSON): instance parameters and a list of blocks; each block = {"lits": [v1, v2, ...]} meaning the clause
  OR_i  not x_{v_i}   (v_i = the t_S-th member of support class S used by the cycle),
and "cycle": the canonical cycle obtained by replacing the cycle's class-S vertices by the first t_S members of S
(twins have identical neighbourhoods in the coprime graph, so this is again a cycle; sat_cert.py re-checks it).
"""
import sys, json, random, time
from pysat.solvers import Solver
import exact883, exact883b


def run(n, k, b, cmax=None, symm=False, seed=0, max_iter=10 ** 7):
    if cmax is None and not symm:
        M = exact883.Model(n, None, b)
    else:
        M = exact883b.Model2(n, None, b, cmax, symm)
    rng = random.Random(seed)
    blocks = []
    with Solver(name="cadical153", bootstrap_with=M.base_clauses()) as s:
        it = 0
        while it < max_iter:
            if not s.solve():
                return dict(n=n, k=k, b=b, cmax=cmax, symm=symm, size=M.size, result="UNSAT", iters=it, blocks=blocks)
            mdl = set(x for x in s.get_model() if x > 0)
            A = [v for v in range(1, n + 1) if M.var[v] in mdl]
            it += 1
            cyc = exact883.find_cycle_heuristic(A, k, rng)
            if cyc is None:
                cyc = exact883.find_cycle_exact(A, k)
                if cyc is False:
                    return dict(n=n, k=k, b=b, cmax=cmax, symm=symm, result="COUNTEREXAMPLE", A=A)
            assert exact883.check_cycle(cyc, A, k)
            cnt = {}
            for v in cyc:
                cnt[M.cls_of[v]] = cnt.get(M.cls_of[v], 0) + 1
            lits = [M.classes[S][t - 1] for S, t in cnt.items()]
            # canonical cycle: i-th occurrence of class S in the cycle -> i-th member of class S
            seen = {}
            canon = []
            for v in cyc:
                S = M.cls_of[v]
                seen[S] = seen.get(S, 0) + 1
                canon.append(M.classes[S][seen[S] - 1])
            blocks.append(dict(lits=lits, cycle=canon))
            s.add_clause([-M.var[v] for v in lits])
    return dict(n=n, k=k, b=b, cmax=cmax, symm=symm, result="ITER_LIMIT")


if __name__ == "__main__":
    man = json.load(open(sys.argv[1]))
    outdir = sys.argv[2]
    ids = set(sys.argv[3:])
    import os
    os.makedirs(outdir, exist_ok=True)
    for inst in man["instances"]:
        if ids and inst["id"] not in ids:
            continue
        path = os.path.join(outdir, inst["id"] + ".blocks.json")
        if os.path.exists(path):
            continue
        t = time.time()
        symm = inst["cmax"] is not None          # exact883b runs used symmetry breaking (default symm=True)
        r = run(inst["n"], inst["k"], inst["b"], inst["cmax"], symm)
        r["sec"] = round(time.time() - t, 2)
        r["id"] = inst["id"]
        json.dump(r, open(path, "w"))
        print(inst["id"], r["result"], len(r.get("blocks", [])), r["sec"], flush=True)
