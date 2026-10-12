"""Exact verification v2 of the residual triples (n,b,l) with c restricted to the values not covered by
Family M per-c (c <= cmax).  Usage: exact_base2.py out.jsonl n:b:l:cmax ..."""
import sys, json, time
import exact883b
out = open(sys.argv[1], "a")
for spec in sys.argv[2:]:
    n, b, l, cmax = map(int, spec.split(":"))
    t = time.time()
    st = exact883b.verify(n, 2 * l + 1, None, b=b, cmax=cmax, time_limit=6 * 3600)
    st["sec"] = round(time.time() - t, 2)
    st.pop("A", None) if st["result"] != "COUNTEREXAMPLE" else None
    out.write(json.dumps(st) + "\n"); out.flush()
