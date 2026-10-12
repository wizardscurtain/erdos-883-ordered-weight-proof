import sys, json, time, blockcert
lo, hi, eps, out = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
n = lo
with open(out, "a") as fh:
    while n <= hi:
        w = max(0, int(eps * n)); t = time.time()
        u = blockcert.block_uncovered2(n, min(hi, n + w))
        rec = {"Nlo": n, "Nhi": min(hi, n + w), "n_uncovered": len(u), "uncovered": [list(x) for x in u], "retry": False}
        if u and w > 0:
            w = max(0, int(eps * n / 4)); u = blockcert.block_uncovered2(n, min(hi, n + w))
            rec.update({"Nhi": min(hi, n + w), "n_uncovered": len(u), "uncovered": [list(x) for x in u], "retry": True})
        rec["sec"] = round(time.time() - t, 1)
        fh.write(json.dumps(rec) + "\n"); fh.flush()
        n = rec["Nhi"] + 1
