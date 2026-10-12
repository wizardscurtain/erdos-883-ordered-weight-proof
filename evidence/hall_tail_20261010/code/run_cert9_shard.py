"""Probe-10 / probe-11 runner: cert9 (families E, R, M; audit round 2) on one shard of a set of n.

Usage: python3 code/run_cert9_shard.py --ns 1501-4000,4025,4029,4035 [--shard i --shards k] --out FILE
The n set is sorted and interleaved across shards (shard i gets every k-th n) so shards carry similar load.
Rows are exactly cert9.run(n, spf) as written by cert9.py's own main; the output is appended and resumable.
"""
import sys, os, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cert9
from cert4 import spf_table


def parse_ns(spec):
    out = set()
    for part in spec.split(","):
        if "-" in part:
            a, b = map(int, part.split("-"))
            out.update(range(a, b + 1))
        elif part.strip():
            out.add(int(part))
    return sorted(out)


def main():
    a = sys.argv[1:]
    opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
    ns = parse_ns(opt("--ns"))
    shard, shards = int(opt("--shard", "0")), int(opt("--shards", "1"))
    out = opt("--out")
    mine = ns[shard::shards]
    done = set()
    if os.path.exists(out):
        with open(out) as fh:
            for line in fh:
                try:
                    done.add(json.loads(line)["n"])
                except Exception:
                    pass
    todo = [n for n in mine if n not in done]
    if not todo:
        print(f"shard {shard}/{shards}: nothing to do ({len(mine)} n)")
        return
    spf = spf_table(max(todo))
    with open(out, "a") as fh:
        for n in todo:
            fh.write(json.dumps(cert9.run(n, spf)) + "\n")
            fh.flush()
    print(f"shard {shard}/{shards}: {len(todo)} n computed, {len(mine)} in shard")


if __name__ == "__main__":
    main()
