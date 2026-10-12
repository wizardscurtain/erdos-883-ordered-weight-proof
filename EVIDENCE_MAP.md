# Mathematical evidence map

**Cecil Jentges · Erdős 883 / JSP-000734**

Theorem 1.1 and the following proof components form one mathematical argument. The certificate data and the explanations of what they certify are indispensable, not optional experimental supplements.

| Question for the reader | Mathematical location | Supporting evidence |
|---|---|---|
| Is the original odd-cycle statement retained? | Theorem 1.1 and Section 1 | All n and all admissible sets; strict threshold; simple cycles; full required odd-length range. |
| Why do the weight counts produce a cycle? | Section 2 | Discarded-tail lemma, ordered-gap lemma, sufficient ordered Hall condition, and distinct connectors outside the skeleton. |
| Why are the arithmetic weights valid? | Section 3 | Finite inclusion–exclusion and the adjusted-product bound, with positive x and nonnegative adjusted endpoint weights. |
| Why do G and GA cover every missing-even parameter? | Section 4 | Complementary criteria and their overlap argument, including first-rank and boundary cases. |
| Why does the analytic argument cover every remaining n? | Section 5 | Primorial bounds, prime-class estimates, Euler-product tails, and cell-to-interval deductions; historical analytic code and interval outputs. |
| Why are all finite integers covered? | Section 6 | Per-n certificates, 167 adjacent block certificates, and the small-parameter exceptions assigned to the appropriate families. |
| Why do the SAT results imply the graph claim? | Section 6 and Appendix A | Counterexample-preserving reductions, canonical cycle witnesses, reconstructed CNFs, and the 99 LRAT proof obligations. |
| What was checked with the new implementation? | Section 8.3 and `verification/` | The full 4000–30000 output and bounded test receipts. Not a new replay of the entire historical archive. |
| Why is the new arithmetic route integer-only? | Appendix B | Directed rational enclosures, exact fallback predicate, fixed-width range arguments, code, and tests. |
| How is question (ii) accounted for? | Section 7 and bibliography | Sárközy's published 1999 theorem, with density and uniform quantifiers matched; historical credit retained. |
| What contribution is attributed to me? | Section 1.1 and `AUTHORSHIP.md` | The specific adjusted-weight construction and certificate assembly, with AI assistance and related work disclosed. |

## Historical evidence layout

The designated location is `evidence/hall_tail_20261010/`, retaining mathematical notes, arithmetic code, finite and block records, `SAT_OBLIGATIONS.json`, and all SAT/LRAT artifacts. The later analytic supplement is kept separately. The frozen source version is `a04e7031546461920d8a3ac3f920447f1e689feb`.

This repository version supplies a deliberately revised public derivative, governed by `evidence/PUBLIC_MANIFEST.json` and `evidence/public_integrity.py`. It is not the unchanged historical archive, and no claim is made that the original manifest passes after exclusions. `evidence/PUBLIC_REVISION.md` maps omitted experimental metadata and redundant draft exposition to the controlling manuscript and retained mathematical dependencies.

Adjacent conditional Lean-reduction files are retained under `evidence/lean/` and explicitly labeled as historical context, not as a complete standalone build or completed Lean contribution. Applicable copied-statement attribution and license text are preserved. No Lean credit is requested by this mathematical submission.

## Corrections and checking scope

The current manuscript governs the corrected exposition described in `provenance/REVISION_RECORD.md`. Original numerical and SAT evidence bytes and dates are preserved; later packaging and editorial revisions are explicit in `evidence/PUBLIC_REVISION.md`. Fresh validation of the public derivative includes the 99 SAT CNF/witness/LRAT instances and analytic interval computation, but not all historical scanner and block computations.

A supplied execution receipt reports its own scope; a successful integrity check or a bounded test suite does not certify every mathematical premise or establish organizer acceptance. See `provenance/PUBLIC_PACKAGE_VALIDATION_20261012.json`, `evidence/REPRODUCTION.md`, and `evidence/VALIDATION_PROTOCOL.md`.
