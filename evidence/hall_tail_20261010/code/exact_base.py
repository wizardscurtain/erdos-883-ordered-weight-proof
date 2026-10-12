"""Exact verification of the (n,b,l) pairs left uncovered by the certificates (probe-6), for all
targets l' in [l, m] with b fixed (parity-preserving compression)."""
import sys, json, time
import exact883
pairs = json.load(open(sys.argv[1]))
out = open(sys.argv[2], "a")
for n, m, b, l in pairs:
    for lp in range(l, m + 1):
        t = time.time()
        st = exact883.verify(n, 2 * lp + 1, None, b=b, max_iter=200000)
        st["sec"] = round(time.time() - t, 2)
        out.write(json.dumps(st) + "\n"); out.flush()
