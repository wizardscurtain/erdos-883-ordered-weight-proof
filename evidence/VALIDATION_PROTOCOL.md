# Public evidence validation protocol

These checks have different scopes and must not be conflated. Execute from the repository root after following `REPRODUCTION.md`; keep newly generated outputs outside `evidence/`.

## Integrity and packaging tests

```sh
python -B evidence/public_integrity.py
python -B evidence/test_public_integrity.py
```

The first checks the new inventory, file sizes, hashes, provenance consistency, and safe paths. The second exercises malformed and missing artifacts, tampering, unsafe paths, symlinks, unexpected files, and trust-anchor failure with synthetic fixtures.

An independently obtained manifest hash can be supplied using `--expect-manifest HEX`. Without a trusted version or digest, a manifest and its contents changed together are not authenticated.

After installing the mathematical dependencies, run `python -B evidence/test_public_modes.py`.
These regression tests reject mode-selection typos, optimized Python, missing deep-checker configuration,
and a fake checker that prints VERIFIED while returning a failure code.

## Recorded coverage

```sh
sh evidence/hall_tail_20261010/replay.sh --quick
```

This checks stored SAT-artifact hashes, coverage relationships, the per-c arithmetic complements, complete per-n source coverage, adjacency and successful criteria for 167 recorded blocks, and positive recorded analytic margins. It does not regenerate the scanners, blocks, analytic intervals, or LRAT checks.

## Deep SAT replay

```sh
DRAT_TOOLS=/absolute/path/to/drat-trim \
  sh evidence/hall_tail_20261010/replay.sh --deep
```

For all 99 instances, this reconstructs the CNF from the structural encoding and recorded cycle blocks, checks the canonical witness cycles, compares the CNF digest, and runs `lrat-check` on the archived proof. A nonzero checker exit is a failure, even if a VERIFIED marker is printed.

The graph-to-CNF mathematical reductions in the paper remain part of the proof. Successful LRAT checks alone do not prove those reductions, and this command does not rerun all scanners or blocks.

## E/R/M scanners

```sh
REPLAY_OUT="$(pwd)/validation_out/scanners" JOBS=2 \
  sh evidence/hall_tail_20261010/replay.sh --scanners
```

This recomputes every designated required row for cert10, cert9, cert7, and the single-gap checker and compares the outputs. Resume behavior belongs to the historical runner; a resumed receipt includes previously generated output and must not be described as an entirely fresh execution without further provenance.

## Analytic and block computation

```sh
mkdir -p validation_out
python -B evidence/hall_tail_20261010/code/analytic_interval.py \
  > validation_out/analytic_interval.json
python -B verification/integer_replay.py blocks \
  evidence/hall_tail_20261010/probes/exact_blocks.jsonl \
  --output validation_out/integer_blocks.jsonl
```

Check analytic `ALL_OK`, A0, and all three strictly positive margins, using the interval decisions rather than treating displayed floating decimals as rigorous endpoints. The supplemental argument explains why the finite grids establish the stated uniform inequalities.

The block command may require substantial memory and computation at the largest endpoints. Neither a quick integrity pass nor a fresh analytic pass establishes that all 167 blocks have just been recomputed.

## Integer-only per-n route

```sh
python -B verification/test_integer_replay.py
python -B verification/integer_replay.py pern 4000 30000 \
  --output validation_out/integer_per_n.jsonl
```

The bounded tests and the full per-n replay are distinct commands. Expect 26,001 rows, 25,998 stronger sufficient-criterion successes, and exactly 4025, 4029, and 4035 as exceptions requiring the separate E/R/M evidence.

## Required reporting

Record exit codes, exact commands, actual dependency versions, relevant file digests, and which computations were new versus read from stored records. A packaging pass is not a theorem proof, human endorsement, complete Lean formalization, or organizer acceptance.
