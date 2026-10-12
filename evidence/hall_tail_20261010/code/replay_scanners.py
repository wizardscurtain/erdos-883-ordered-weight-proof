"""Re-run the per-n certificate scanners (families E/R/M) and compare every row with the recorded evidence.

Until 2026-10-10 the ledger credited n < 4000 from hash-bound result rows only; nothing re-ran the scanners.
This script recomputes those rows with the same scanner code and requires byte-for-byte equality (after JSON
normalisation) with the recorded rows:

  scanner   recorded rows                     n re-run with --scope needed (default)
  cert10    probes/probe6.jsonl               6..300                (sole source; incl. the 86 SAT residuals)
  cert9     probes/probe5.jsonl               301..1500             (sole source)
  cert7     probes/probe4_a.jsonl + _b.jsonl  1501..3999, 4025, 4029, 4035   (sole source)
  l1        probes/probe4_l1.jsonl            same n as cert7       (amended l = 1 rule)

--scope all re-runs every recorded row instead (probe-5 from 30, probe-4/l1 from 1000 incl. samples to 9000).
Work is split into contiguous ascending chunks, each run in a fresh worker process (fastcert's sieve cache
must only grow within a process). Results are appended to <out>/<scanner>.jsonl, so an interrupted run resumes.
Writes <out>/SCANNER_REPLAY.json; prints SCANNER_REPLAY_IDENTICAL and exits 0 only if every required row was
recomputed and matches. The public driver also rejects optimized Python so that
assertions in downstream historical routines cannot be disabled.

Usage: python3 code/replay_scanners.py [--root DIR] [--out DIR] [--jobs N] [--scope needed|all] [--only a,b]
Cost (--scope needed): about 5.5 CPU-hours, dominated by cert7; wall time divides by --jobs.
"""
import sys, os, json, hashlib, time
import argparse
from pathlib import Path
from multiprocessing import Pool

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Optimization disables historical assertions; run without -O or -OO.")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

SS10 = ((5, 7, 11, 13), (5, 7, 11), (5, 7), (5,), (5, 11), (5, 7, 13), (5, 11, 13), (7, 11, 13), ())  # = run_cert10.py
CHUNK = {"cert10": 20, "cert9": 10, "cert7": 5, "l1": 200}


def sha_file(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def norm(row):
    return json.loads(json.dumps(row))


def run_chunk(task):
    """One contiguous ascending chunk of n for one scanner, in a fresh process."""
    name, ns = task
    import cert4
    spf = cert4.spf_table(max(ns))
    out = []
    for n in ns:
        if name == "cert10":
            import cert10
            u = cert10.coverage_multi(n, spf, full_grid=True, sigsets=SS10)
            row = {"n": n, "m": n // 6, "n_uncovered": len(u), "uncovered": [list(x) for x in u[:12]]}
        elif name == "cert9":
            import cert9
            row = cert9.run(n, spf)
        elif name == "cert7":
            import cert7
            row = cert7.run(n, spf)
        elif name == "l1":
            import l1_check_fast
            u = l1_check_fast.l1_uncovered(n, spf)
            row = {"n": n, "l1_uncovered": u[:20], "n_l1_uncovered": len(u)}
        else:
            raise SystemExit(f"unknown scanner {name}")
        out.append(norm(row))
    return name, out


def load(path):
    with open(path) as fh:
        return [json.loads(l) for l in fh if l.strip()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=os.path.dirname(HERE))
    parser.add_argument("--out", required=True)
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--scope", choices=("needed", "all"), default="needed")
    parser.add_argument("--only", default="cert10,cert9,cert7,l1")
    options = parser.parse_args()
    root, outdir, jobs, scope = options.root, options.out, options.jobs, options.scope
    only = set(options.only.split(","))
    if not only or not only <= {"cert10", "cert9", "cert7", "l1"} or jobs < 1:
        parser.error("Require positive --jobs and a nonempty, known --only scanner set")
    output_path = Path(outdir)
    if not output_path.is_absolute() or output_path.resolve().is_relative_to(Path(root).resolve().parent):
        parser.error("--out must be absolute and outside evidence/")
    public_root = Path(root).resolve().parent
    sys.path.insert(0, str(public_root))
    from public_integrity import verify_package
    verify_package(public_root)
    os.makedirs(outdir, exist_ok=True)
    P = lambda *x: os.path.join(root, *x)

    recorded = {
        "cert10": {r["n"]: r for r in load(P("probes", "probe6.jsonl"))},
        "cert9": {r["n"]: r for r in load(P("probes", "probe5.jsonl"))},
        "cert7": {r["n"]: r for f in ("probe4_a.jsonl", "probe4_b.jsonl") for r in load(P("probes", f))},
        "l1": {r["n"]: r for r in load(P("probes", "probe4_l1.jsonl"))},
    }
    sole7 = list(range(1501, 4000)) + [4025, 4029, 4035]
    needed = {"cert10": range(6, 301), "cert9": range(301, 1501), "cert7": sole7, "l1": sole7}
    want = {k: sorted(recorded[k]) if scope == "all" else sorted(needed[k]) for k in recorded if k in only}
    for k, ns in want.items():
        missing = [n for n in ns if n not in recorded[k]]
        if missing:
            raise SystemExit(f"{k}: no recorded row for n = {missing[:10]}")

    done = {}
    for k in want:
        f = os.path.join(outdir, f"{k}.jsonl")
        done[k] = {r["n"]: r for r in load(f)} if os.path.exists(f) else {}
    tasks = []
    for k, ns in want.items():
        todo = [n for n in ns if n not in done[k]]
        c = CHUNK[k]
        tasks += [(k, todo[i:i + c]) for i in range(0, len(todo), c)]
    tasks.sort(key=lambda t: -max(t[1]) * (5 if t[0] == "cert7" else 1))   # longest first
    t0 = time.time()
    print(f"scanner replay: {sum(len(t[1]) for t in tasks)} rows to compute in {len(tasks)} chunks on {jobs} workers", flush=True)
    with Pool(jobs, maxtasksperchild=1) as pool:
        for i, (k, rows) in enumerate(pool.imap_unordered(run_chunk, tasks), 1):
            with open(os.path.join(outdir, f"{k}.jsonl"), "a") as fh:
                for r in rows:
                    fh.write(json.dumps(r) + "\n")
                    done[k][r["n"]] = r
            if i % 25 == 0 or i == len(tasks):
                print(f"  {i}/{len(tasks)} chunks, {time.time() - t0:.0f} s", flush=True)

    summary = {"scope": scope, "scanners": {}, "code_sha256": {}, "record_sha256": {}}
    for f in ("cert4.py", "cert7.py", "cert9.py", "cert10.py", "certM.py", "fastcert.py", "l1_check_fast.py", "replay_scanners.py"):
        if os.path.exists(os.path.join(HERE, f)):
            summary["code_sha256"][f] = sha_file(os.path.join(HERE, f))
    for f in ("probe6.jsonl", "probe5.jsonl", "probe4_a.jsonl", "probe4_b.jsonl", "probe4_l1.jsonl"):
        summary["record_sha256"][f] = sha_file(P("probes", f))
    ok_all = True
    for k, ns in want.items():
        mism = [n for n in ns if n in done[k] and norm(recorded[k][n]) != done[k][n]]
        miss = [n for n in ns if n not in done[k]]
        ok = not mism and not miss
        ok_all &= ok
        summary["scanners"][k] = {"n_required": len(ns), "n_recomputed": len(ns) - len(miss), "mismatches": mism[:50],
                                  "n_mismatches": len(mism), "missing": miss[:50], "identical": ok,
                                  "n_set_sha256": hashlib.sha256(json.dumps(ns).encode()).hexdigest(),
                                  "identical_n": ns if ok else [n for n in ns if n in done[k] and n not in set(mism)]}
    summary["identical"] = ok_all
    with open(os.path.join(outdir, "SCANNER_REPLAY.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
    print(json.dumps({k: {x: v[x] for x in ("n_required", "n_recomputed", "n_mismatches")} for k, v in summary["scanners"].items()}))
    if not ok_all:
        print("SCANNER_REPLAY_FAILED")
        sys.exit(1)
    print("SCANNER_REPLAY_IDENTICAL (%s scope)" % scope)


if __name__ == "__main__":
    main()
