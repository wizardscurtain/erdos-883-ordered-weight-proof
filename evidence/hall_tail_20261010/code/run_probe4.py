import sys, json, cert7
ns = [int(x) for x in open(sys.argv[1]).read().split()]
spf = cert7.spf_table(max(ns))
out = open(sys.argv[2], "a")
for n in ns:
    r = cert7.run(n, spf)
    out.write(json.dumps(r) + "\n"); out.flush()
