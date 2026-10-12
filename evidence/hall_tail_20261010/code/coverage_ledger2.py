"""Public-derivative coverage ledger for Erdős #883(i).

This is a disclosed derivative, not the original historical-manifest checker.
Quick mode checks stored records and certificate hashes; it does not replay SAT,
all scanners, all blocks, or the analytic computation.

Unlike v1 it does not trust result flags alone:
  * every public evidence file is checked against ../PUBLIC_MANIFEST.json (sha256);
  * Families G/GA are credited from the EXACT-arithmetic replay (famG_exact.py: integer decisions for all
    borderline comparisons), not from the float pipeline;
  * the exact base is credited only for instances whose SAT certificate was checked (drat-trim + lrat-check) and
    whose stored artifacts hash to the recorded values; with --deep the CNF is rebuilt from the witness file by the
    independent builder (sat_cert.py), every witness cycle is re-checked, and the LRAT proof is re-checked with
    lrat-check (path in $DRAT_TOOLS);
  * the analytic tail is credited from the interval-arithmetic replay (analytic_interval.py);
  * with --scanners FILE (written by replay_scanners.py) the per-n families E/R/M are credited only for rows that the
    scanner re-run reproduced exactly, and the re-run must cover every n for which E/R/M is the sole source
    (6..3999 and 4025, 4029, 4035) with the current scanner code and the current recorded rows.
What remains trusted: the mathematical reductions in the version 1.1 paper, Python/NumPy integer arithmetic, the drat-trim and
lrat-check binaries (for SAT), mpmath's interval arithmetic (for the tail).

  * probes/probe10_11_cert9_rows.jsonl (cert9 on 1501..4000 and 4025, 4029, 4035; probe-10/11) is credited as a second
    certificate source for the range cert7 covers; --require-second-source fails unless every such n has two sources.

Usage: python3 coverage_ledger2.py [--root DIR] [--deep] [--scanners replay_out/SCANNER_REPLAY.json] [--require-second-source]
"""
import sys, os, json, hashlib, lzma, subprocess, tempfile
import argparse
from pathlib import Path

sys.dont_write_bytecode = True
if not __debug__:
    raise SystemExit("Optimization disables historical assertions; run without -O or -OO.")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for c in iter(lambda: fh.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    args = sys.argv[1:]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=os.path.dirname(HERE))
    parser.add_argument("--deep", action="store_true")
    parser.add_argument("--scanners")
    parser.add_argument("--require-second-source", action="store_true")
    options = parser.parse_args(args)
    root = options.root
    deep = options.deep
    if deep and not os.environ.get("DRAT_TOOLS"):
        parser.error("--deep requires explicit DRAT_TOOLS")
    P = lambda *a: os.path.join(root, *a)
    load = lambda f: [json.loads(l) for l in open(f)]
    report = {}

    # 1. Explicit new public inventory; never rewrite or impersonate the old manifest.
    public_root = Path(root).resolve().parent
    sys.path.insert(0, str(public_root))
    from public_integrity import verify_package
    integrity = verify_package(public_root)
    report["manifest_files"] = integrity.files
    report["manifest_mismatches"] = []
    report["public_manifest_sha256"] = integrity.manifest_sha256
    report["verification_scope"] = {
        "stored_records_and_hashes": True,
        "sat_cnf_witness_lrat_replay": deep,
        "scanner_receipt_supplied": options.scanners is not None,
        "all_blocks_recomputed_by_this_command": False,
        "analytic_tail_recomputed_by_this_command": False,
        "mathematical_or_organizer_acceptance": False,
    }

    # 2. exact base (checked SAT certificates)
    ob = json.load(open(P("SAT_OBLIGATIONS.json")))
    ver = set()
    for inst in ob["instances"]:
        c = inst["certificate"]
        assert c["drat_trim_verified"] and c["lrat_check_verified"] and c["witnesses_ok"], inst["id"]
        for kind, key in (("blocks.json", "blocks_sha256"), ("cnf", "cnf_sha256"), ("lrat", "lrat_sha256")):
            raw = lzma.open(P("sat_certificates", f"{inst['id']}.{kind}.xz")).read()
            assert sha_bytes(raw) == c[key], (inst["id"], kind)
        ver.add((inst["n"], inst["l"], inst["b"]))
    report["sat_instances_hash_checked"] = len(ver)
    if deep:
        import sat_cert
        tools = os.environ.get("DRAT_TOOLS", sat_cert.TOOLS)
        for inst in ob["instances"]:
            with tempfile.TemporaryDirectory() as td:
                blk = os.path.join(td, "b.json"); cnf = os.path.join(td, "x.cnf"); lrat = os.path.join(td, "x.lrat")
                open(blk, "wb").write(lzma.open(P("sat_certificates", f"{inst['id']}.blocks.json.xz")).read())
                R = json.load(open(blk))
                F, classes, supp, size = sat_cert.base_cnf(R["n"], R["b"], R["cmax"], R["symm"])
                sat_cert.check_witnesses(R["n"], R["k"], R["blocks"], classes, supp)
                for b in R["blocks"]:
                    F.add([-v for v in b["lits"]])
                text = f"p cnf {F.top} {len(F.clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in F.clauses)
                assert sha_bytes(text.encode()) == inst["certificate"]["cnf_sha256"], ("rebuilt CNF differs", inst["id"])
                open(cnf, "w").write(text)
                open(lrat, "wb").write(lzma.open(P("sat_certificates", f"{inst['id']}.lrat.xz")).read())
                checked = subprocess.run([os.path.join(tools, "lrat-check"), cnf, lrat], capture_output=True, text=True)
                out = checked.stdout
                assert checked.returncode == 0 and (("c VERIFIED" in out) or ("s VERIFIED" in out)), ("lrat-check failed", inst["id"])
        report["sat_deep_checked"] = len(ob["instances"])

    # per-c Family M for the c-restricted instances
    import cert10, certM
    SS = ((5, 7, 11, 13), (5, 7, 11), (5, 7), (5,), (5, 11), (5, 7, 13), (5, 11, 13), (7, 11, 13), ())
    spf = cert10.spf_table(100)
    for inst in ob["instances"]:
        if inst["cmax"] is None:
            continue
        n, b, l, cm = inst["n"], inst["b"], inst["l"], inst["cmax"]
        Ms = [certM.MFam(cert10.Cert8(n, spf, sig=sg, full_grid=True)) for sg in SS]
        h = n // 3 - n // 6
        assert all(any(M.ok_c(b, l, c) for M in Ms) for c in range(cm + 1, h + 1)), ("per-c M gap", n, b, l)

    # 3. per-n sources
    rerun = None
    if options.scanners is not None:
        scan = json.load(open(options.scanners))
        sole7 = list(range(1501, 4000)) + [4025, 4029, 4035]
        need = {"cert10": range(6, 301), "cert9": range(301, 1501), "cert7": sole7, "l1": sole7}
        rerun = {}
        for k, ns in need.items():
            s = scan["scanners"].get(k)
            if not s or not s["identical"] or not set(ns) <= set(s["identical_n"]):
                raise SystemExit(f"scanner re-run incomplete or not identical: {k}")
            rerun[k] = set(s["identical_n"])
        for f, h in scan["record_sha256"].items():
            if sha_file(P("probes", f)) != h:
                raise SystemExit(f"scanner re-run was compared with a different {f}")
        for f, h in scan["code_sha256"].items():
            if sha_file(os.path.join(HERE, f)) != h:
                raise SystemExit(f"scanner re-run used different code: {f}")
        report["scanner_rerun_rows"] = {k: len(v) for k, v in rerun.items()}
    ok_rerun = lambda k, n: rerun is None or n in rerun[k]
    src = {}
    add = lambda n, s: src.setdefault(n, []).append(s)
    for r in load(P("probes", "probe6.jsonl")):
        n, m = r["n"], r["m"]
        assert r["n_uncovered"] == len(r["uncovered"])
        if ok_rerun("cert10", n) and all(all((n, lp, b) in ver for lp in range(l, m + 1)) for b, l, _ in r["uncovered"]):
            add(n, "E/R/M+SAT" if r["uncovered"] else "E/R/M")
    for r in load(P("probes", "probe5.jsonl")):
        if r["n_uncovered"] == 0 and ok_rerun("cert9", r["n"]):
            add(r["n"], "E/R/M(cert9)")
    l1 = {r["n"]: r["n_l1_uncovered"] for r in load(P("probes", "probe4_l1.jsonl"))}
    for f in ("probe4_a.jsonl", "probe4_b.jsonl"):
        for r in load(P("probes", f)):
            if r["n_uncovered"] == 0 and l1.get(r["n"], 1) == 0 and ok_rerun("cert7", r["n"]) and ok_rerun("l1", r["n"]):
                add(r["n"], "E/R(cert7)")
    for r in load(P("probes", "exact_pern.jsonl")):
        if r["ok"]:
            add(r["n"], "G/GA exact")
    # second certificate source for the range that cert7 alone covered (probe-10/11: cert9 run on GitHub Actions)
    sec = P("probes", "probe10_11_cert9_rows.jsonl")
    if os.path.exists(sec):
        for r in load(sec):
            if r["n_uncovered"] == 0:
                add(r["n"], "E/R/M(cert9, probe-10/11)")
    sole7 = list(range(1501, 4000)) + [4025, 4029, 4035]
    single = [n for n in sole7 if len(set(src.get(n, []))) < 2]
    report["second_source_1501_3999"] = {"n": len(sole7), "with_two_sources": len(sole7) - len(single), "single": single[:20]}
    if options.require_second_source and single:
        raise SystemExit(f"{len(single)} n in the cert7 range have only one certificate source, e.g. {single[:10]}")
    missing = [n for n in range(6, 30001) if n not in src]
    report["per_n_missing"] = missing
    assert not missing, missing[:10]

    # 4. blocks (exact)
    B = load(P("probes", "exact_blocks.jsonl"))
    assert B[0]["Nlo"] == 30001 and B[-1]["Nhi"] == 10 ** 8
    assert all(B[i + 1]["Nlo"] == B[i]["Nhi"] + 1 for i in range(len(B) - 1))
    assert all(b["ok"] and b["NGA"] <= b["y1"] - b["mhi"] for b in B)
    report["blocks_exact"] = len(B)

    # 5. analytic tail (interval replay)
    an = json.load(open(P("probes", "analytic_interval.json")))
    assert an["ALL_OK"] and an["A1_high_margin_lower"] > 0 and an["A2_margin_lower"] > 0 and an["A1_low_margin_lower"] > 0
    report["analytic_interval"] = {k: an[k] for k in ("A1_high_margin_lower", "A1_low_margin_lower", "A2_margin_lower")}

    from collections import Counter
    report["first_source_counts"] = dict(Counter(v[0] for v in src.values()))
    print(json.dumps(report, indent=1))
    print("PUBLIC_COVERAGE_RECORDS_PASSED"
          + ("; SAT CNFs, witnesses and LRAT freshly checked" if deep else "; SAT artifacts hash-checked only")
          + ("; scanner receipt validated" if rerun is not None else "; scanner rows not recomputed")
          + "; block and analytic records not recomputed by this command")


if __name__ == "__main__":
    main()
