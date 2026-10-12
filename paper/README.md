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

The prepared 19-page `Manuscript.pdf` is to be uploaded here alongside these sources. Its SHA-256 is:

```text
PAPER_PDF_HASH_TO_BE_RECORDED
```

This placeholder is publication metadata, not a mathematical premise. Replace it with the hash of the actual uploaded PDF before the final release. The source version and PDF must agree; a later changed source requires a rebuilt PDF and new hash.

## Revision and attribution

The current exposition incorporates the numerical and small-parameter wording corrections documented in [`../provenance/REVISION_RECORD.md`](../provenance/REVISION_RECORD.md). Historical certificate files are not silently edited to conceal earlier wording.

See [`../AUTHORSHIP.md`](../AUTHORSHIP.md) and [`../EVIDENCE_MAP.md`](../EVIDENCE_MAP.md). The broader private research-methodology account is not a manuscript dependency and is not included here.
