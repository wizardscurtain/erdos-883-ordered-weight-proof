# Public-evidence revision record

Cecil Jentges, 12 October 2026. This record describes a deliberate public derivative of the frozen mathematical evidence, not an alteration of the private historical source or a claim that its old manifest remains valid.

## Preservation and replacement

Every retained numerical output, every SAT obligation, and every compressed witness, CNF, and LRAT artifact is copied byte-for-byte from the source. The arithmetic certificate routines, exact-comparison routines, analytic interval calculation, and scanner functions are unchanged; changes to import paths, verification boundaries, and reporting are identified separately below.

The main manuscript's six TeX source files and its paired PDF are unchanged. The existing integer-only checker and its supplied complete row file are also unchanged.

The new `PUBLIC_MANIFEST.json` records each artifact's byte length, SHA-256, and origin classification: `unchanged`, `revised`, or `new`. A retained source artifact also carries its source SHA-256. The manifest excludes itself to avoid a self-hash cycle; anchor its identity in the public Git commit or a separately trusted manifest digest.

## Deliberately omitted source files

These omissions are explicit, not a claim that the old dependency inventory was satisfied:

- **33 experimental metadata files:** `hall_tail_20261010/probes/probe{1..11}_{protocol,measurements,scores}.json`. The mathematical replay code does not read them; all corresponding mathematical result rows remain.
- **Three superseded exposition files:** `proof/MANUSCRIPT.md`, `proof/PROOF_883i_ALL_N.md`, and `proof/REDUCTION_LEMMA.md` under the historical directory. Their private-process discussion is excluded. Mathematical replacements are mapped below.
- **Original `MANIFEST.json` and `code/build_manifest.py`:** Replaced by the new public schema and read-only verifier. The original remains frozen privately and is not regenerated or presented as passing here.
- **`code/coverage_ledger.py` and `probes/coverage_ledger.out`:** Superseded non-hash-bound ledger and its output. The public derivative uses the stronger v2 coverage logic.

No original mathematical dataset or SAT proof artifact is omitted. There is no hidden dependency on the omitted experimental metadata.

## Mathematical replacement map

| Superseded document or material | Controlling public replacement |
|---|---|
| Original assembled `MANUSCRIPT.md` | `../paper/Manuscript.tex` and its five component files, version 1.1, with its unchanged PDF |
| All-n statement and cycle construction | Main paper Theorem 1.1 and sections 2–4 |
| Original `REDUCTION_LEMMA.md`, including mathematical amendments | Main paper Appendix A and `hall_tail_20261010/proof/PER_N_CERTIFICATE_THEOREM.md` |
| Exact SAT counterexample-preserving reductions | Main paper section 6, `code/sat_cert.py`, `SAT_OBLIGATIONS.json`, and all 297 compressed artifacts |
| Finite-to-infinite assembly formerly in `PROOF_883i_ALL_N.md` | Main paper sections 5–6, retained G/GA and analytic notes, full recorded tables, and the public coverage checker |
| Infinite primorial continuation, Euler-product tails, and grid reasoning | Main paper section 5 plus the unchanged 11 October analytic supplement |

The omission of redundant draft exposition is not a claim that stored computation proves the prose lemmas. Those lemmas remain mathematical proof obligations in the publicly supplied paper.

## Revised source files

- **`code/coverage_ledger2.py`:** Uses the new public manifest; rejects optimized Python because historical assertions are essential; rejects unknown command-line flags instead of silently selecting quick mode; requires explicit tool configuration and both a successful LRAT exit code and a VERIFIED marker in deep mode; reports exactly which checks were and were not executed. Mathematical coverage tests and certificate reconstruction are retained.
- **`code/sat_cert.py`:** Replaces a machine-specific tool path with a local path or explicit `DRAT_TOOLS`; points its explanatory reference to the controlling public paper. The encoder and witness-checking functions are unchanged.
- **Seven independent-checker scripts:** `cert1_indep.py`, `cert2_indep.py`, `cert3_indep.py`, `cert7_indep.py`, `cert9_indep.py`, `cert10_indep.py`, and `lamprime_indep.py` resolve their own directory instead of a private machine path. Their mathematical functions are unchanged.
- **`replay.sh`:** Replaced with an explicit, fail-closed local driver. It does not install dependencies, download tools, suppress failure, regenerate manifests, or write outputs inside the integrity-controlled package.
- **`code/replay_scanners.py`:** Retains every scanner function and row comparison, while rejecting unknown flags, invalid scanner names, unsafe output placement, and optimized Python. It verifies the public inventory before execution; its CLI now requires an explicit output directory.
- **Three retained proof notes and historical README:** Remove process/endorsement claims and stale private references. The G/GA note withdraws the already-corrected impossible 0.10 margin sentence; the analytic note states the A2 margin conservatively, consistently with the existing revision record and supplement. No new mathematical theorem is asserted by these editorial changes.
- **`lean/Erdos883Proof/FidelityMin.lean`:** Restores the upstream copyright/license attribution for copied statement text and labels the modification. The Lean declarations remain unchanged.

The corrected Family M threshold, single-gap treatment, cost-sorted chunk bound, three sufficient-criterion exceptions, floating-filter qualifications, and finite quantifiers are all retained. Historical dates are not reassigned to these later packaging and editorial revisions.

## Trust and rights

The package is supplied for mathematical review. The validity of the mathematical reductions, interpreter and numerical operations, and any explicitly invoked proof-checker binaries remains part of the trust boundary.

No project-wide license is added. Applicable third-party attribution and license text are preserved narrowly for copied upstream material; see `THIRD_PARTY_NOTICES.md`. AI assistance remains disclosed, and no external human verifier, complete Lean proof, or organizer finding is invented.
