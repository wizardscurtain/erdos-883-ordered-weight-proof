# Mathematical manuscript

**Cecil Jentges**  
*Ordered-weight certificates for odd cycles in dense coprime graphs*  
Version 1.1 · 12 October 2026 UTC

## Reading order

| Location | Content |
|---|---|
| Theorem 1.1 and Section 1 | Exact all-n statement, strict density threshold, sharpness, and antecedents. |
| Section 2 | Abstract ordered-weight connector mechanism, with complete proofs. |
| Sections 3–4 | Adjusted totient pair bound, arithmetic specialization, and complementary G/GA criteria. |
| Sections 5–6 | Uniform analytic tail, finite certificates, and proof-producing SAT reductions. |
| Section 7 | Original-problem coverage using the historically attributed second-question theorem. |
| Section 8 | Evidence, reproducibility, authorship, and the scope of actual checking. |
| Appendices | Consolidated small-parameter construction and arithmetic-verification details. |

The manuscript is a computer-assisted mathematical argument. Its necessary certificate archive must be read as part of the proof; the paper does not become a complete public evidence release merely because its source compiles.

## Files and build

The entry point is `Manuscript.tex`. Keep `preamble.tex`, `analytic.tex`, `finite.tex`, `appendices.tex`, and `references.tex` in the same directory. With a LaTeX installation providing the packages named in the preamble, run from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error Manuscript.tex
```

Inspect the compiler log and the rendered document. The second pass resolves internal references. Do not use shell-escape. Generated auxiliary files are not part of the evidence release.

The prepared 19-page `Manuscript.pdf` is present alongside these unchanged sources. Its 404,447 bytes have SHA-256:

```text
3049e1dff147e017ba81e4babea5ec9153df7c12fbce1ad49ba875218ddcd546
```

The downloaded public bytes matched this checksum. The source version and PDF remain paired; neither was changed by the public-evidence revision. A later changed source requires a rebuilt PDF and new hash; PDF metadata can also make a fresh build byte-different without changing the mathematics.

## Revision and attribution

The current exposition incorporates the numerical and small-parameter wording corrections documented in [`../provenance/REVISION_RECORD.md`](../provenance/REVISION_RECORD.md). The public derivative preserves certificate data unchanged and explicitly documents editorial changes to historical notes in [`../evidence/PUBLIC_REVISION.md`](../evidence/PUBLIC_REVISION.md); it does not silently edit the historical source.

See [`../AUTHORSHIP.md`](../AUTHORSHIP.md) and [`../EVIDENCE_MAP.md`](../EVIDENCE_MAP.md). The broader private research-methodology account is not a manuscript dependency and is not included here.
