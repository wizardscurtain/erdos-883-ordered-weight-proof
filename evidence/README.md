# Public mathematical evidence for Erdős 883

Cecil Jentges, public derivative dated 12 October 2026. This package supplies mathematical certificates and replay tools for the manuscript's all-n odd-cycle assertion, with explicit separation between stored evidence, newly executed checks, and mathematical review.

The controlling exposition is the unchanged manuscript version 1.1 in `../paper/`. Its Theorem 1.1 concerns part (i); section 7 accounts for part (ii) using Gábor N. Sárközy's historical theorem without claiming that discovery as new.

## Start here

- **Setup:** `REPRODUCTION.md` contains the environment and dependency instructions.
- **Test execution:** `VALIDATION_PROTOCOL.md` distinguishes integrity, quick coverage, deep SAT, scanners, blocks, and analytic replay.
- **Public derivation:** `PUBLIC_REVISION.md` explains the deliberately revised inventory and omitted source materials.
- **Integrity:** `PUBLIC_MANIFEST.json` covers every public evidence file except itself; `public_integrity.py` rejects missing, extra, unsafe, and hash-mismatched files.
- **Certificates:** `hall_tail_20261010/` retains the mathematical tables, checkers, and all 99 SAT obligations.
- **Analytic supplement:** `submission_math_only_20261011/` preserves the dated supplement and its recorded interval output.
- **Conditional Lean material:** `lean/` is retained for context, not as a completed Lean proof or a buildable standalone submission.

The original source commit is `a04e7031546461920d8a3ac3f920447f1e689feb`, and the original manifest Git blob is `53b14de9be27da9e31d4be9614a08f72c8a70697`. Those identify the historical source; this package is a new, disclosed derivative and does not claim the original manifest passes over its reduced inventory.

AI substantially assisted the mathematical reasoning, programming, checking, and writing. Passing these checks does not establish independent external human endorsement, complete formalization, organizer acceptance, or priority.
