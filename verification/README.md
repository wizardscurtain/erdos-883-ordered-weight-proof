# Verification record

## Integer-only G/GA checker

`integer_replay.py` implements the stronger G/GA sufficient criterion using directed rational bounds and an exact integer predicate at uncertain boundaries. Floating-point values do not decide acceptance. Appendix B of the manuscript explains the bounds and fixed-width arithmetic conditions.

The recorded full per-n run covers every integer in the closed interval **4000–30000**. It has **26,001 rows**, **25,998 successful certificates**, and the expected exceptions **4025, 4029, 4035**. Those three parameters require the separate historical E/R/M certificates; they are not theorem counterexamples.

`COMPLETE_PER_N_REPLAY.json` is the summary. The full `INTEGER_PER_N_4000_30000.jsonl` output must accompany it. The output's SHA-256 is:

```text
78589bde77d8dd2c3447556ba97a4c67365f81a1799c792942ff03dc23f8dc84
```

The minimum successful integer slack is 116. The complete row file is present and its 26,001 records were checked for integrity and consistency; this does not mean the full calculation was regenerated.

## Reproduction

The originally recorded environment is Python 3.13.5 with NumPy 2.3.5. Later validation records name their actual versions separately. In a clean environment, from the repository root:

```sh
python -m pip install -r verification/requirements.txt
python verification/test_integer_replay.py
python verification/integer_replay.py pern 4000 30000 --output fresh.jsonl
```

The bounded tests write their results to standard output. Preserve any new results separately instead of overwriting the historical receipt. The per-n command performs new computation; a file-hash comparison does not.

With the supplied historical block data, the new checker also accepts:

```sh
python verification/integer_replay.py blocks \
  evidence/hall_tail_20261010/probes/exact_blocks.jsonl \
  --output fresh_integer_blocks.jsonl
```

The final endpoint is 100,000,000 and requires large arrays. A complete new block replay is not claimed here. Compare mathematical outputs, not run times or the number of fallback operations.

## Bounded tests

`TEST_RESULTS.json` records the supplied bounded checks. `PUBLICATION_TEST_20261012.json` records their successful rerun while preparing this public repository. Each includes 150,000 least-threshold checks, 500,000 threshold comparisons, 10,000 wide-product checks, 58,471 equality cases, 20,200 marked-gap configurations, 4,108 reserve/deletion configurations, and one worked example.

These tests support specific code and combinatorial components. They are not independent proofs of the entire all-n result.

## Historical proof evidence

The complete argument additionally requires the finite E/R/M scans, 167 block certificates, all 99 SAT/LRAT obligations and their graph-to-CNF reductions, and the uniform analytic-tail estimates. Their mathematical data and checker code are supplied in the public derivative under `../evidence/`, with a new manifest and explicit source-byte lineage.

The historical G/GA checker uses a floating-point filter with exact fallback; it is not literally integer-only. The current manuscript describes the filter under explicit arithmetic assumptions and supplies the separate integer-only route above.

A manifest check establishes file identity. A coverage ledger checks the relationship between stored records. Deep SAT checking and scanner replay do additional work. None of these should be described as organizer verification, a complete Lean proof, or external human peer review.

The current publication work does not claim a fresh execution of every historical computation. See [`../EVIDENCE_MAP.md`](../EVIDENCE_MAP.md) and the manuscript for the complete dependency chain.

Public-derivative validation freshly replayed all 99 SAT CNF/witness/LRAT instances and the analytic interval calculation, not every scanner or block. See `../provenance/PUBLIC_PACKAGE_VALIDATION_20261012.json` for the actual scope. Setup and test execution are separated in `../evidence/REPRODUCTION.md` and `../evidence/VALIDATION_PROTOCOL.md`.
