# Historical mathematical certificates: public derivative

Cecil Jentges, Erdős 883 / JSP-000734. This directory contains selected mathematical evidence from the frozen 10 October 2026 archive, with a new public integrity boundary dated 12 October 2026.

This is not the unchanged original archive. `../PUBLIC_REVISION.md` explains every exclusion and revision; `../PUBLIC_MANIFEST.json` identifies this package. No command here claims the omitted original manifest still passes.

## Reading order

The controlling mathematical exposition is the unchanged main paper, `../../paper/Manuscript.tex`, version 1.1, and its paired PDF. Theorem 1.1 is the all-n odd-cycle assertion; Appendix A consolidates the small-parameter reductions, and section 6 explains the graph-to-SAT connection and full finite assembly.

- **`proof/PER_N_CERTIFICATE_THEOREM.md`:** Consolidated E/R/M families and their finite quantifiers.
- **`proof/FAMILY_G.md`:** Complementary G/GA certificates and block domination.
- **`proof/ANALYTIC_TAIL_G.md`:** Analytic bounds, read with `../submission_math_only_20261011/ANALYTIC_TAIL_REPLAY.md`.
- **`SAT_OBLIGATIONS.json` and `sat_certificates/`:** The 99 obligations and 297 compressed witness/CNF/LRAT files.
- **`probes/`:** Mathematical rows and outputs, not general experimental process metadata.
- **`code/`:** Mathematical computations, independent implementations, and replay tools.

Earlier exploratory outputs and implementations are retained for mathematical context. They do not override the current manuscript, the exact replay files, or the scope stated by the public checker.

## Verification

Use `../REPRODUCTION.md` for environment setup and `../VALIDATION_PROTOCOL.md` for the distinct checks. No driver installs software, downloads tools, or silently ignores dependency failure.

```sh
sh replay.sh --quick
DRAT_TOOLS=/absolute/path/to/drat-trim sh replay.sh --deep
REPLAY_OUT=/absolute/path/outside/evidence JOBS=2 sh replay.sh --scanners
```

Quick mode verifies integrity and relationships among recorded certificates. Deep mode additionally reconstructs CNFs, checks the cycle witnesses, and runs LRAT checks; it does not rerun all finite scanners, all blocks, or the analytic tail. Scanner mode performs those specified E/R/M scanner computations and then validates their receipt.

Historical G/GA arithmetic uses floating-point filtering with exact fallback under the assumptions in the paper. The separate checker in `../../verification/integer_replay.py` supplies the integer-only route. The stronger criterion's exceptions 4025, 4029, and 4035 retain their E/R/M evidence.

## Responsibility

AI substantially assisted the reasoning, code, checks, and writing. No external human mathematical endorsement, complete Lean proof, organizer acceptance, or priority determination is asserted.
