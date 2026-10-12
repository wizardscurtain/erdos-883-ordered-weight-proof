# Families G and GA: multiplicative zigzag certificates for Erdős #883(i)

Public derivative of a mathematical note dated 2026-10-10; no independent human endorsement is asserted.
These are
certificate families that can be used alongside E/R/M of PER_N_CERTIFICATE_THEOREM.md.

## 0. Setting

n ≥ 6, q = ⌊n/2⌋, m = ⌊n/6⌋, h = ⌊n/3⌋ − ⌊n/6⌋, T = ⌊n/2⌋ + ⌊n/3⌋ − ⌊n/6⌋, A ⊆ [n] with |A| = T+1
(WLOG: any larger A contains such a subset), b = #{k ≤ q : 2k ∉ A}, Y = A ∩ odd, |Y| = T + 1 − (q − b) = h+1+b.
For an odd v: G(v) = ∏_{p | v} (1 − 1/p), ω(v) = number of distinct prime factors, and for x ∈ {q, n}

  G̃_x(v) = G(v) − 2^{ω(v)} / √(2x).

Lemmas used from PER_N_CERTIFICATE_THEOREM.md: L1 (any h+1 odd integers ≤ n contain a coprime pair),
L3 (ordered Hall: lists L_1..L_l have an SDR if #{i : |L_i| ≤ j−1} ≤ j−1 for every 1 ≤ j ≤ l),
L4 (tail lemma), and the cycle template (distinct odd o_0..o_l ∈ A with gcd(o_0,o_l) = 1 and an SDR
u_i ∈ L_i ⊆ A ∖ {o_0..o_l} with u_i coprime to o_{i−1} o_i give C_{2l+1}).

## 1. Counting lemma

C1. For an integer D ≥ 2 and real x ≥ 1: #{k ≤ x : gcd(k, D) = 1} > x·φ(D)/D − 2^{ω(D)−1}.
Proof. Legendre: the count is Σ_{d | rad D} μ(d)⌊x/d⌋ = x φ(D)/D − Σ_{d|rad D} μ(d){x/d}. Exactly 2^{ω(D)−1} divisors
have μ = +1, each with {x/d} ∈ [0,1), so Σ μ(d){x/d} < 2^{ω(D)−1}. ∎

C2. Let o ≠ o′ be odd integers ≤ n and x ∈ {q, n}. If G̃_x(o) ≥ 0 and G̃_x(o′) ≥ 0 then
  #{k ≤ x : gcd(k, o o′) = 1} > x · G̃_x(o) G̃_x(o′).
Proof. D = o o′ ≥ 3 has φ(D)/D = ∏_{p | oo′}(1 − 1/p) ≥ G(o)G(o′) (a prime dividing both contributes one factor
on the left and two on the right, each ≤ 1), and 2^{ω(D)−1} ≤ 2^{ω(o)+ω(o′)−1} = x·e e′ with e = 2^{ω(o)}/√(2x),
e′ = 2^{ω(o′)}/√(2x). By C1 the count exceeds x(GG′ − ee′), and GG′ − ee′ − (G−e)(G′−e′) = e′(G−e) + e(G′−e′) ≥ 0. ∎

## 2. The path and the bad-gap count

Fix l with 1 ≤ l ≤ m and a weight G̃ ∈ {G̃_q, G̃_n}. Let Y0 be h+1 elements of Y of largest G̃ (ties arbitrary).
By L1 choose a coprime pair a, a′ ∈ Y0. Let o_1, …, o_{l−1} be l−1 elements of Y0 ∖ {a,a′} of largest G̃,
ordered so that G̃(o_1) ≥ … ≥ G̃(o_{l−1}) (possible since |Y0| − 2 = h − 1 ≥ m − 1 ≥ l − 1).
Path: a, o_1, …, o_{l−1}, a′ (for l = 1 just a, a′); V = its vertex set (l+1 distinct odd elements of A); gaps
g_0 = (a,o_1), g_i = (o_i, o_{i+1}) (1 ≤ i ≤ l−2), g_{l−1} = (o_{l−1}, a′).

P1. For a threshold t ≥ 0 let W = {v : G̃(v) < t}. Suppose every gap that is "bad" has an endpoint in W.
Then #bad gaps ≤ |W ∩ V| + [W ∩ {o_1..o_{l−1}} ≠ ∅] ≤ w + [w ≥ 1], w = |W ∩ V|.
Proof. L := l−1. W ∩ {o_i} is a suffix {o_k..o_L} (sorted decreasingly, W a down-set); s := L − k + 1.
s = 0: only g_0 (iff a ∈ W) and g_L (iff a′ ∈ W) can have an endpoint in W: ≤ |W ∩ V|.
s ≥ 1, k ≥ 2: g_0 needs a ∈ W; g_i (1 ≤ i ≤ L−1) has an endpoint in W iff o_{i+1} ∈ W iff i ≥ k−1 (s gaps);
g_L qualifies: total ≤ [a∈W] + s + 1 ≤ |W∩V| + 1.  k = 1: all l = s+1 gaps: ≤ |W∩V| + 1.  l = 1: one gap, ≤ |W ∩ V|. ∎

P2 (tail). w ≤ |W ∩ Y0| ≤ max(0, N_{G̃}(t) − b), where N_{G̃}(t) = #{odd v ≤ n : G̃(v) ≤ t}.
Proof. L4 with Y′ = Y, s = h+1, β = |Y| − s = b, cost = −G̃: every element of Y ∖ Y0 has G̃ ≤ min_{Y0} G̃, so if
Y0 ∩ W ≠ ∅ then (Y0 ∩ W) ∪ (Y ∖ Y0) ⊆ {odd v ≤ n : G̃(v) ≤ max_{W} G̃} ⊆ {G̃ ≤ t}. ∎

## 3. Family G (even connectors)

Weight G̃_q. Lists L_i = {2k ∈ A : gcd(k, x y) = 1} for the gap g_i = (x, y) (even, so disjoint from V).
|L_i| ≥ #{k ≤ q : gcd(k, xy) = 1} − b. If g_i is bad at rank j (|L_i| ≤ j − 1) then min(G̃_q(x), G̃_q(y)) < t_j :=
√((b + j − 1)/q): if both weights are ≥ 0 this follows from C2 (q G̃_q(x)G̃_q(y) < b + j − 1); if one is negative it is
trivial since t_j ≥ 0. (The product inequality itself need not hold when both are negative.)
By P1, P2 with W_j = {G̃_q < t_j}: #bad_j ≤ w_j + [w_j ≥ 1], w_j ≤ max(0, Ñ(b+j−1) − b), where
Ñ(y) := #{odd v ≤ n : G̃_q(v) ≤ √(y/q)}.

Certificate G(b,l): for every 1 ≤ j ≤ l, max(0, Ñ(b+j−1) − b) + [Ñ(b+j−1) > b] ≤ j − 1.
Then L3 gives an SDR and the template gives C_{2l+1}.

Equivalently (y = b + j − 1): G(b,l) ⟺ Ñ(b) ≤ b and Ñ(y) ≤ y − 1 for every y ∈ (b, b + l − 1].
Define y1 := 0 if Ñ(0) > 0, else y1 := min{ y ≥ 1 : Ñ(y) ≥ y } (this exists: Ñ(#odd) = #odd).
G1. G(b,l) holds whenever b + l ≤ y1. (For y ∈ [b, b+l−1]: if y ≥ 1 then y < y1 gives Ñ(y) ≤ y − 1;
if y = 0 = b then y1 ≥ 1 gives Ñ(0) = 0 ≤ b.)

## 4. Family GA (arbitrary connectors)

Weight G̃_n. Lists L_i = {u ∈ A ∖ V : gcd(u, xy) = 1}. |A ∖ V| = T − l, so
|L_i| ≥ #{u ≤ n : gcd(u, xy) = 1} − (n − T + l). Bad at rank j ⇒ min(G̃_n(x), G̃_n(y)) < t^A_j := √((n − T + l + j − 1)/n)
(via C2 when both weights are ≥ 0, trivially otherwise).
Certificate GA(b,l): for every j ≤ l, max(0, N_A(t^A_j) − b) + [N_A(t^A_j) > b] ≤ j − 1, N_A(t) := #{odd v ≤ n : G̃_n(v) ≤ t}.
GA1. If b ≥ N_GA := N_A(√((n − T + 2m − 1)/n)) then GA(b,l) holds for every l ≤ m (all w_j = 0, as t^A_j ≤ t^A at l=j=m).
GA2. GA(b,l) ⇒ GA(b′,l′) for b′ ≥ b and l′ ≤ l (t^A_j grows with l; each condition is monotone in N_A and b).
GA(b,m) ⟺ b ≥ b_A := max(0, N_A(t^A_1(m)), max_{2≤j≤m}(N_A(t^A_j(m)) − j + 2)) (for j = 1 the condition reads
N_A ≤ b; for j ≥ 2 it reads N_A ≤ b + j − 2). Note b_A ≤ N_GA.

## 5. Per-n theorem for G ∪ GA

Theorem G. If b_A(n) ≤ y1(n) − m(n) (in particular if N_GA(n) ≤ y1(n) − m(n)), then every A ⊆ [n] with
|A| > T(n) contains C_{2l+1} for all 1 ≤ l ≤ m.
Proof. Take b ∈ [0, b_max] and l ∈ [1, m]. If b ≥ b_A use GA2. Otherwise b ≤ y1 − m − 1, so b + l ≤ y1 − 1 and G1 applies. ∎
(The finite scans of probe-8 use the stronger simple form N_GA ≤ y1 − m; the analytic tail uses b_A.)

Block version. For Nlo ≤ n ≤ Nhi define Ñ⁺(y) = #{odd v ≤ Nhi : G(v) − 2^{ω(v)}/√(2 q_lo) ≤ √(y/q_lo)} and
N_GA⁺ = #{odd v ≤ Nhi : G(v) − 2^{ω(v)}/√(2 Nlo) ≤ √(1/3 + 7/(6 Nlo) + (2 m_hi − 1)/Nlo)}; y1⁺ from Ñ⁺ as above.
Since the universe grows with n, q_n ≥ q_lo, and (n − T_n)/n ≤ 1/3 + 7/(6n) (T_n ≥ 2n/3 − 7/6; the sharp bound is 1/3 + 2/(3n)),
Ñ_n ≤ Ñ⁺ pointwise, y1(n) ≥ y1⁺, N_GA(n) ≤ N_GA⁺, m_n ≤ m_hi. Hence N_GA⁺ ≤ y1⁺ − m_hi certifies every n in the block.

The earlier floating implementation subtracts 10⁻⁹ from every G̃ before comparing.
The operative historical replay is `famG_exact.py`, using a floating filter with exact fallback;
its stated execution assumptions and the separate integer-only route are in the main paper, Appendix B.

## 6. Asymptotic form (motivation for the analytic tail)

With F(u) = limiting proportion of odd v with G(v) ≤ u (Erdős–Wintner; G is multiplicative-type with Σ 1/p² < ∞),
Ñ(q u²)/q → F(u), and the criterion becomes, in the limit, F(u) < u² on (0, u*) together with
3F(√(2/3)) < 3u*² − 1.
The former sentence asserting a margin at least 0.10 throughout an interval starting at 0.3
is withdrawn, as already recorded in the public manuscript's revision record.
An explicit upper bound F⁺ (exact small-prime classes + Rankin for primes > z) satisfies u² − F⁺(u) ≥ 0.0427
on [0.30, 0.985] for z = 31 (≥ 0.077 on [0.3, 0.95] for z = 13). The analytic tail therefore reduces to explicit
error terms (class-count discrepancy, Rankin truncation, the 2^ω/√(2q) shift); see ANALYTIC_TAIL_G.md.
