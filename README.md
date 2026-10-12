# Ordered-weight certificates for odd cycles in dense coprime graphs

**Cecil Jentges**  
Mathematical submission preparation for **JSP-000734 / Erdos Problem 883**.

This repository presents an alternative computer-assisted mathematical proof candidate using adjusted arithmetic weights, ordered connector lists, and a finite-to-infinite certificate assembly. It is separate from the author's Lean formalization and private research process.

## Current release status

**Publication in progress; not yet a complete public evidence release.** The historical finite/block certificate and SAT/LRAT archive has not been transferred here. Do not submit this repository as a complete mathematical evidence package until the indispensable evidence is present and its links and hashes have been checked. This is an evidence-publication limitation, not a claim that a counterexample has been found.

The original private research repository has not been made public, and its history is not part of this repository. A direct automated transfer of the private certificate tree was blocked. No contest pull request, organizer acceptance, award, DOI, first-priority determination, or completed Lean proof is claimed.

## Mathematical target

For every positive integer n, let A be a subset of {1,...,n} satisfying

    |A| > floor(n/2) + floor(n/3) - floor(n/6).

The coprime graph on A joins distinct integers exactly when their gcd is 1. The proposed part-(i) theorem supplies a genuine simple cycle of every odd length L with

    3 <= L <= floor(n/3) + 1.

The requested length range is empty for n < 6. The strict density threshold is sharp, as witnessed by the bipartite coprime graph on the integers divisible by 2 or 3.

## Approach

An odd skeleton supplies the closing edge. An adjusted totient weight bounds common-neighbor counts. Ordering its interior limits the number of deficient connector lists. A sufficient size-based Hall condition supplies distinct connectors, producing each requested cycle. Complementary connector families, finite certificates, and a uniform analytic tail provide the proposed all-n argument.

The paper identifies its particular contribution without claiming invention of Hall's theorem, inclusion-exclusion, totient products, or standard computational proof techniques. It acknowledges prior and contemporaneous work, including the related prize submission #4972. Equal theorem statements do not establish equal verification or settled priority.

## Original-problem coverage

The new proposed contribution concerns part (i). Part (ii), the fixed-l, sufficiently-large-n complete-tripartite assertion, is attributed to G. N. Sarkozy, *Complete tripartite subgraphs in the coprime graph of integers*, Discrete Mathematics 202 (1999), 227-238, DOI 10.1016/S0012-365X(98)00359-8. Its hypotheses and quantifiers must be explicitly matched in the submission; no new historical discovery credit for part (ii) is claimed.

## Contest submission route

This is the external mathematical-evidence repository, **not a fork of the awards repository**. The eventual contest PR belongs in a fork of `TheJustinSunPrize/awards` and changes only the permitted fields for JSP-000734 in `problems/catalog-0701-0800.md`. It links to an accessible, fixed version of the paper and all necessary evidence here. Manuscript binaries, archives, proof source, dependencies, private research, identity documents, and payment details do not belong in that awards PR.

Mathematics-only submissions do not require a Lean repository or Lean self-check. Completion, mathematical review, attribution, priority, formalization, and eventual award eligibility are distinct matters.

Official instructions: [Contributing](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) and [PR template](https://github.com/TheJustinSunPrize/awards/blob/main/.github/PULL_REQUEST_TEMPLATE.md).

## Attribution and disclosure

Cecil Jentges directed the research. AI systems substantially assisted reasoning, programming, checking, and writing. No independent external human referee endorsement is asserted. Code-disjoint checks and AI-assisted audits are not relabeled as human peer review. Historical mathematical evidence and later presentation/verification revisions must retain their actual dates and provenance.

The detailed private research-process account, general operating protocol, unrelated projects, and private repository history are excluded. No blanket license or retroactive public-priority claim is introduced by this setup.
