# Revision record

**Cecil Jentges · Mathematical manuscript version 1.1 · 12 October 2026 UTC**

This record separates the revised exposition and new checking route from the original mathematical evidence dated 10 October 2026 and the analytic supplement dated 11 October.

## Mathematical presentation

The paper first proves the ordered-weight connector mechanism, then specializes it to the adjusted totient profile. The complementary G/GA criteria, analytic tail, finite-block domination, small-parameter constructions, and SAT-to-graph connection are presented as separate proof obligations. The second question is supplied by Sárközy's historically attributed result, not claimed as a new discovery.

## Corrections incorporated

1. The historical sentence claiming a margin of at least 0.10 for `u^2 - F(u)` throughout an interval starting at `u = 0.3` is removed. Since `F(u) >= 0`, that assertion cannot hold at the endpoint. The operative tail proof uses the explicit A0, A1, and A2' inequalities, not that commentary.
2. The reported A2' margin of approximately 0.058964 is stated conservatively as greater than 0.058, rather than rounded upward to at least 0.059.
3. The adjusted-weight lemma explicitly requires positive x and distinct positive odd endpoints; its nonnegativity hypotheses are retained. The combined prime support is therefore nonempty.
4. The simple `N_GA` condition is identified as a stronger sufficient criterion, not a necessary condition or a weaker hypothesis.
5. The Family M branch using Family R requires `|X| >= max(l+1, g_C+1)`. Earlier wording that omitted the endpoint-selection threshold does not govern the revised proof.
6. Integer loss counts and the totient-density symbol are distinguished to avoid a notation collision.
7. The historical arithmetic replay is accurately described as a floating-point filter with exact fallback. Appendix B gives an error argument under explicit arithmetic assumptions; the new checker supplies a separate integer-only route.
8. Project audit labels and code-disjoint checks are not presented as organizer acceptance or independent external human peer review.

The revised wording does not silently alter the original evidence hashes. When the historical archive is published, it must remain distinguishable from this later exposition.

## New checking

The new implementation uses directed rational bounds and exact polynomial fallback. The complete recorded per-n replay covers 4000–30000, with exactly three expected failures of the stronger sufficient criterion. Their separate small-case certificates remain necessary.

The bounded tests were rerun successfully during this repository preparation; the separate receipt records that execution. This preparation did not newly replay all historical blocks, E/R/M scans, SAT/LRAT proofs, or analytic interval bounds.

## Attribution

The revised exposition followed a comparison with related work linked by prize PR #4972. It does not assign later changes an earlier completion date. The paper makes no settled historical-priority claim and does not claim invention of its standard mathematical ingredients. See [`../AUTHORSHIP.md`](../AUTHORSHIP.md).
