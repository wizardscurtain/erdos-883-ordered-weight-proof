# Ordered-weight certificates for odd cycles in dense coprime graphs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23482077.svg)](https://doi.org/10.5281/zenodo.23482077)

**Cecil Jentges**  
Independent researcher · Mathematical contribution to **Erdős Problem 883 / JSP-000734**

**Cite this work.** Concept DOI (all versions): [10.5281/zenodo.23482077](https://doi.org/10.5281/zenodo.23482077). Version DOI (v1.1): [10.5281/zenodo.23482078](https://doi.org/10.5281/zenodo.23482078).

This repository accompanies my computer-assisted argument for the all-\(n\) odd-cycle assertion in Erdős Problem 883. The approach combines adjusted arithmetic weights, an ordered connector construction, and finite-to-infinite certificate coverage.

## Read the paper

The main source is [`paper/Manuscript.tex`](paper/Manuscript.tex), version 1.1, dated 12 October 2026 UTC. Its component files are in [`paper/`](paper/). Theorem 1.1 states the result; Sections 2–4 develop the method; Sections 5–6 and the appendices supply the analytic and finite reductions; Section 7 accounts for the historically established second question. See [`paper/README.md`](paper/README.md) for the reading order and build instructions.

**Status: Mathematical evidence release supplied for review.** This version contains the mathematical sources and paired PDF, the new checker and complete per-\(n\) output, and a deliberately revised public historical evidence package. The derivative has its own manifest and explicit migration record; it is not presented as the unchanged historical archive. No prize acceptance or complete Lean formalization is claimed.

## The mathematical statement

Let \(A\subseteq\{1,\ldots,n\}\), and join distinct elements when their greatest common divisor is one. If

\[
|A|>\left\lfloor\frac n2\right\rfloor+\left\lfloor\frac n3\right\rfloor-\left\lfloor\frac n6\right\rfloor,
\]

then the proposed theorem supplies a simple cycle of every odd length \(L\) with

\[
3\le L\le\left\lfloor\frac n3\right\rfloor+1.
\]

The statement quantifies over every positive integer \(n\) and every admissible set \(A\). For \(n<6\), the requested length range is empty. The density threshold is sharp: the integers divisible by 2 or 3 form a set of exactly the threshold size whose coprime graph is bipartite.

## What distinguishes the approach

Choose an odd skeleton with a coprime closing pair. An adjusted totient weight bounds the supply of common-neighbor connectors. Ordering the interior vertices controls the number of deficient connector lists through an arithmetic cumulative count. A sufficient size-based Hall condition then supplies distinct connectors outside the skeleton.

Even connectors and arbitrary unused connectors cover complementary parameter ranges. Arithmetic certificates and proof-producing SAT calculations handle the finite range; explicit bounds handle the infinite tail. The required certificate archive is part of the proof, not optional experimental support.

The paper identifies this particular combination of ideas without claiming invention of Hall's theorem, inclusion–exclusion, totient products, or standard computational proof techniques. Related work by Donald Della Pietra and Yicheng Pan is cited. The related prize [PR #4972](https://github.com/TheJustinSunPrize/awards/pull/4972) is not alleged to be incorrect, and no priority ruling is asserted.

## Verification and evidence

Start with [`verification/README.md`](verification/README.md) and [`EVIDENCE_MAP.md`](EVIDENCE_MAP.md). The new integer-only checker and its bounded tests are already available. The recorded complete replay covers 26,001 integers from 4,000 through 30,000: 25,998 satisfy the stronger G/GA criterion; 4025, 4029 and 4035 retain their separate E/R/M treatment. A failure of this sufficient criterion is not a counterexample to the theorem.

The new finite replay does not replace the historical block certificates, small-parameter scans, SAT/LRAT certificates, or analytic interval bounds. Integrity checks, bounded mathematical tests, full proof review, and organizer verification are distinguished throughout.

The public derivative is described in [`evidence/README.md`](evidence/README.md). Use [`evidence/REPRODUCTION.md`](evidence/REPRODUCTION.md) for setup and [`evidence/VALIDATION_PROTOCOL.md`](evidence/VALIDATION_PROTOCOL.md) for the separate execution modes. All 99 SAT CNF/witness/LRAT instances and the analytic interval calculation were freshly checked during derivative validation; all historical scanners and blocks were not freshly recomputed. The actual check scope is recorded in `provenance/PUBLIC_PACKAGE_VALIDATION_20261012.json`.

## Scope and authorship

My proposed new contribution concerns question (i). Question (ii) is supplied by the historical theorem of Gábor N. Sárközy, *Complete tripartite subgraphs in the coprime graph of integers*, Discrete Mathematics 202 (1999), 227–238, DOI `10.1016/S0012-365X(98)00359-8`. Section 7 matches its density hypothesis and uniform quantifiers to the requested conclusion. I do not claim that historical discovery.

I selected and directed this research. AI systems substantially assisted the mathematical development, programming, checking, and writing. See [`AUTHORSHIP.md`](AUTHORSHIP.md) for contribution boundaries and [`provenance/REVISION_RECORD.md`](provenance/REVISION_RECORD.md) for corrections. No independent external human referee endorsement is asserted.

This repository contains the mathematical contribution and its public verification material, not my private research-process account or unrelated work.

[`evidence/PUBLIC_REVISION.md`](evidence/PUBLIC_REVISION.md) records the deliberate exclusion of experimental metadata, replacement of superseded draft exposition, unchanged certificate bytes, and revised public verification boundary. No claim is made that the original historical manifest passes over this reduced inventory.

## Companion papers from the same project

These additional documents explain the construction and its evidence without claiming a second independent solution. They retain their supplied versions, author attribution, and AI-assistance disclosures.

- **Methods note, version 1.1:** [Ordered-weight connector certificates in finite graphs](methodology/Ordered_Weight_Connector_Certificates_v1_1.pdf), with its [self-contained LaTeX source](methodology/Ordered_Weight_Connector_Certificates_v1_1.tex).
- **Evidence guide, version 1.0:** [Computational evidence and reproducibility for Erdős 883(i)](paper/Computational_Evidence_and_Reproducibility_v1_0.pdf), with its [LaTeX source](paper/Computational_Evidence_and_Reproducibility_v1_0.tex).
- **Short exposition, version 1.0:** [An ordered-weight construction of odd cycles in dense coprime graphs](paper/Ordered_Weight_Construction_Proof_Guide_v1_0.pdf), with its [LaTeX source](paper/Ordered_Weight_Construction_Proof_Guide_v1_0.tex).

The evidence guide and short exposition describe the earlier checkpoint `27fcb6e64e9f701ee84a43523e825cc84c93c6a2` as a dated inventory, not the current release state. The complete reviewed public derivative was subsequently published at `b5738d8944340f0ac9434f70f689316b18497026`; its [revision record](evidence/PUBLIC_REVISION.md), [manifest](evidence/PUBLIC_MANIFEST.json), and [validation scope](provenance/PUBLIC_PACKAGE_VALIDATION_20261012.json) govern the evidence actually supplied. None of these companion documents substitutes for the certificate archive.

## Prize submission

This is the external evidence repository. A mathematics-only submission belongs in a fork of [`TheJustinSunPrize/awards`](https://github.com/TheJustinSunPrize/awards), with a narrowly scoped catalog change and links to the completed public evidence. See the official [contribution instructions](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and [PR template](https://github.com/TheJustinSunPrize/awards/blob/main/.github/PULL_REQUEST_TEMPLATE.md). The mathematical and Lean contributions are separate; this repository does not register a completed Lean proof.

The mathematics-only submission is already filed as [awards PR #5021](https://github.com/TheJustinSunPrize/awards/pull/5021). It is pending organizer review; the companion documents are not a duplicate prize submission or an acceptance claim.

## License

This repository uses two licenses:

- **Paper and text** (`paper/`, the companion PDFs, and the documentation) are licensed under the [Creative Commons Attribution 4.0 International License (CC-BY-4.0)](https://creativecommons.org/licenses/by/4.0/). See `LICENSE-CC-BY-4.0`.
- **Code** (the scripts, verification tools, and certificate generators) is licensed under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0). See `LICENSE`.

Copyright © 2026 Cecil Jentges.
