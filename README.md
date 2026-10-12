# Ordered-weight certificates for odd cycles in dense coprime graphs

**Cecil Jentges**  
Independent researcher · Mathematical contribution to **Erdős Problem 883 / JSP-000734**

This repository accompanies my computer-assisted argument for the all-\(n\) odd-cycle assertion in Erdős Problem 883. The approach combines adjusted arithmetic weights, an ordered connector construction, and finite-to-infinite certificate coverage.

## Read the paper

The main source is [`paper/Manuscript.tex`](paper/Manuscript.tex), version 1.1, dated 12 October 2026 UTC. Its component files are in [`paper/`](paper/). Theorem 1.1 states the result; Sections 2–4 develop the method; Sections 5–6 and the appendices supply the analytic and finite reductions; Section 7 accounts for the historically established second question. See [`paper/README.md`](paper/README.md) for the reading order and build instructions.

**Publication status:** the mathematical sources and the new checker are public. The historical certificate archive and the complete new per-\(n\) output still need to be uploaded. The typeset paper is also being added. Until the indispensable evidence is available, this repository is not a complete public submission package. No prize acceptance or complete Lean formalization is claimed.

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

## Scope and authorship

My proposed new contribution concerns question (i). Question (ii) is supplied by the historical theorem of Gábor N. Sárközy, *Complete tripartite subgraphs in the coprime graph of integers*, Discrete Mathematics 202 (1999), 227–238, DOI `10.1016/S0012-365X(98)00359-8`. Section 7 matches its density hypothesis and uniform quantifiers to the requested conclusion. I do not claim that historical discovery.

I selected and directed this research. AI systems substantially assisted the mathematical development, programming, checking, and writing. See [`AUTHORSHIP.md`](AUTHORSHIP.md) for contribution boundaries and [`provenance/REVISION_RECORD.md`](provenance/REVISION_RECORD.md) for corrections. No independent external human referee endorsement is asserted.

This repository contains the mathematical contribution and its public verification material, not my private research-process account or unrelated work. No blanket license is assigned here to third-party material.

## Prize submission

This is the external evidence repository. A mathematics-only submission belongs in a fork of [`TheJustinSunPrize/awards`](https://github.com/TheJustinSunPrize/awards), with a narrowly scoped catalog change and links to the completed public evidence. See the official [contribution instructions](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and [PR template](https://github.com/TheJustinSunPrize/awards/blob/main/.github/PULL_REQUEST_TEMPLATE.md). The mathematical and Lean contributions are separate; this repository does not register a completed Lean proof.
