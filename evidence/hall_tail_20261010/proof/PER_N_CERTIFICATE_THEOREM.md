# Per-n Hall-tail certificates for Erdős #883(i) — consolidated statement (v2)

Public derivative of a mathematical note dated 2026-10-10; no independent human endorsement is asserted.
The Family M admissibility condition for its R branch is |X| ≥ s0 = max(l+1, g_C+1), as in
Family R; the earlier prose said |X| ≥ l+1. The scanners cert8/9/10 always used s0. Certificates
evaluated by computer are VERIFIED_FINITE evidence for the specific n evaluated. This document
incorporates the corrected single-gap rule, absolute counts, cost-sorted chunks and signature-prime choices.
The unchanged main manuscript version 1.1, Appendix A, is the controlling consolidated exposition.

## 1. Target

For every n ≥ 1 and every A ⊆ [n] with |A| > T(n) := ⌊n/2⌋+⌊n/3⌋−⌊n/6⌋, the coprime graph G(A)
contains C_{2l+1} for every 1 ≤ l ≤ m := ⌊n/6⌋. (Canonical statement: google-deepmind/formal-conjectures
`Erdos883.erdos_883.parts.i`, all n.) It suffices to treat |A| = T+1.

## 2. Notation

q = ⌊n/2⌋, Δ = ⌊q/3⌋ = m, β0 = q − Δ, h = ⌊n/3⌋ − ⌊n/6⌋, b = #{k ≤ q : 2k ∉ A}, Y = odd part of A
(|Y| = h+1+b), X = A ∩ C where C = {v ≤ n : gcd(v,6) = 1} (|X| = b+c+1 with c = #(odd multiples of 3 not in A)).
A signature set P is a finite set of primes ≥ 5; S(v) = P ∩ primes(v), L(v) = primes(v) ∖ ({2,3} ∪ P),
key(v) = (3 | v, S(v)); K(P), K_C(P) = number of keys realised by odd v ≤ n, resp. by v ∈ C.

Exact per-vertex integers (v odd):
ρ(v) = #{k ≤ q : 3∤k, gcd(k,v) > 1};  ρN(v) = #{u ≤ n : gcd(u,v) > 1} (used for v ∈ C);
σ3(S) = #{k ≤ q : 3∤k, gcd(k,∏S) > 1}, λ3(v) = Σ_{p∈L(v)} #{k ≤ q : 3∤k, p | k};
σA(S) = #{k ≤ q : gcd(k,∏S) > 1},      λA(v) = Σ_{p∈L(v)} ⌊q/p⌋;
σN(S) = #{u ≤ n : gcd(u,∏S) > 1},      λN(v) = Σ_{p∈L(v)} ⌊n/p⌋.
Costs: c3(v) = σ3(S)+2λ3(v) (3 | v);  cδ(v) = σA(S)+2λA(v) − δ (v ∈ C, 0 ≤ δ ≤ Δ);  cR(v) = σN(S)+2λN(v) (v ∈ C).

## 3. Lemmas

L1 (odd partition): the odd integers ≤ n split into h pairwise-coprime groups; any h+1 odd integers ≤ n
contain a coprime pair. L2 (C partition): C ∩ [n] = {1} ∪ blocks {6j+5,6j+7,6j+11,6j+13} (j even), each
pairwise coprime; with g_C(n) groups, any g_C+1 elements of C contain a coprime pair. L3 (ordered Hall):
lists L_1..L_l have an SDR if #{i : |L_i| ≤ j−1} ≤ j−1 for all j ≤ l. L4 (tail lemma): if Y0 is the set of
the s smallest-cost elements of a set Y' and |Y'| − s ≥ β, then for every set W, #(Y0 ∩ W) ≤
max(0, R(τ(W)) − β) where τ(W) = min cost over W and R(t) counts the ambient universe with cost ≥ t.
L5 (absolute counts): #(Y0 ∩ W) ≤ #(W ∩ universe). Hence every rough count below is
min(absolute, tail) — written ⟨W⟩ for the relevant universe, cost and subtraction.
Template: distinct odd o_0..o_l in A with gcd(o_0,o_l) = 1 and an SDR u_i ∈ L_i ⊆ A ∖ {o_*} with
u_i coprime to o_{i−1}o_i give C_{2l+1}.

## 4. Families (the constructor knows n, b, l, c and chooses P and the parameters)

### Family E (even connectors)
Y0 = h+1 smallest-cost vertices of Y (cost c3 or cδ); coprime a,a' ∈ Y0 (L1); tail subtraction β = b.
l = 1: V = {a,a'}; certified if ⟨{ρ ≥ ⌈(β0−b)/2⌉}⟩ = 0.
l ≥ 2: separators Sep = {v ∈ Y0 : ρ(v) ≤ gr}, need h+1 − ⟨{ρ ≥ gr+1}⟩ ≥ K+3. V = {a,a'} ∪ min(K+1,l−1)
dividers ∪ further Y0 vertices; arrangement a, s_0, chunk, s_1, …, chunk, s_r, [left-over dividers], a',
chunks = one per key of the non-divider vertices, each sorted by increasing cost.
Lists: even vertices 2k ∈ A with gcd(k, o o') = 1.
Rank-j bound (θ_j = β0 − b − j + 1), certificate E(P,δ,gr): for all 1 ≤ j ≤ l
  ⟨{O3: c3 ≥ θ_j} ∪ {C: cδ ≥ θ_j + Δ − δ}⟩ + min(2K+2, 2⟨{ρ ≥ θ_j − gr}⟩) + K·[θ_j ≤ 2gr] ≤ j − 1.

### Family R (skeleton inside X; any unused vertex as connector)
Requires b+1 ≥ s0 := max(l+1, g_C+1). X0 = s0 smallest-cR vertices of X; coprime a,a' ∈ X0 (L2);
universe C, cost cR, subtraction sub = b+1−s0 (valid for every c since |X| ≥ b+1).
l = 1: certified if ⟨{ρN ≥ ⌈(T−1)/2⌉}⟩ = 0.
l ≥ 2: separators ρN ≤ gN, need s0 − ⟨{ρN ≥ gN+1}⟩ ≥ K_C+3; arrangement as in E (C-keys, chunks sorted
by cR). Lists: u ∈ A ∖ V coprime to both endpoints; |A∖V| = T − l.
Rank-j bound (θR_j = T − l − j + 1): ⟨{cR ≥ θR_j}⟩ + min(2K_C+2, 2⟨{ρN ≥ θR_j − gN}⟩) + K_C·[θR_j ≤ 2gN] ≤ j−1.

### Family M (mixed; for every c ∈ [0,h])
If |X| = b+c+1 ≥ s0 := max(l+1, g_C+1): Family R with skeleton pool X0 = the s0 smallest-cR elements of X and
sub = |X| − s0 (monotone in c; s0 ≥ g_C+1 is what makes L2 give the coprime pair). If |X| < g_C+1, Family M does
not apply. Otherwise g_C+1 ≤ |X| ≤ l (so l ≥ 2):
all of X plus z = l+1−|X| smallest-c3 odd multiples of 3 of A (subtraction sub3 = h−c−z for them);
C-separators by ρN ≤ gN, need |X| − #{x ∈ C : ρN(x) ≥ gN+1} ≥ K_C+3+z; arrangement
a, s, chunk, s, …, chunk, s, o_1, s, o_2, …, s, o_z, s, a', where exactly K_C+1+z separators serve as the
dividers s (dividers left over when fewer than K_C chunks are non-empty stand consecutively, which the
separator–separator term counts) and any further separators are ordinary vertices of the chunk of their key.
Lists: C–C gaps from A ∖ V; (s, o_i) gaps from 3-free evens, |L| ≥ β0 − b − gρ − ρ(o_i),
gρ = max{ρ(x) : x ∈ C, ρN(x) ≤ gN}. Rank-j bound (all C counts absolute):
#{cR ≥ θR_j} + min(2K_C+2, 2#{ρN ≥ θR_j−gN}) + (K_C+z)[θR_j ≤ 2gN] + min(2z, 2⟨O3: ρ ≥ θ_j − gρ⟩_{c3,sub3}) ≤ j−1.

## 5. Per-n theorem

If for every 0 ≤ b ≤ b_max(n) = #odd(n) − h − 1 and every 1 ≤ l ≤ m some certificate of §4 holds
(for M: for every c ∈ [0,h]), then every threshold set A ⊆ [n] contains C_{2l+1} for all l ≤ m.

## 6. Exact base (complement)

For (n,b,l) not certified, an exact SAT/CEGAR search over threshold sets with that b (parity-preserving
support compression, prefix symmetry within support classes, blocking of cycle class patterns)
decides existence; UNSAT certifies the triple. Negative control: at size T the search returns the
extremal set {v : 2|v or 3|v}.

## 7. Recorded computations

Probe-6 (cert10, E/R/M): n ∈ [6,300]; probe-5 (cert9): n ∈ [30,1500]; probe-4 (cert7 + amended l = 1 rule):
n ∈ [1000,4500] and samples to 9000; probe-7 (E/R block certificates, refined λ′ costs): [4501,30000]. Residual triples
(n ≤ 79) are settled by the exact base. For n ≥ 4000 the new Families G/GA (FAMILY_G.md) take over, and the whole
chain for every n is assembled in the main manuscript version 1.1, sections 5 and 6.
