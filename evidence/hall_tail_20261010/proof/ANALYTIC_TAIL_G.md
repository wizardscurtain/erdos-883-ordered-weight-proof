# Analytic tail for Theorem G: every n ≥ N0 = 10⁸

Public derivative of a mathematical note dated 2026-10-10; no independent human endorsement is asserted.
The interval checker is `code/analytic_interval.py`; the 2026-10-11 analytic supplement supplies the infinite-continuation and grid justifications.

## 1. What has to be shown

Refined full-coverage criterion (FAMILY_G.md §4–5 plus GA2 below): with
  Ñ(y) = #{odd v ≤ n : G̃_q(v) ≤ √(y/q)},  y1 = min{y ≥ 1 : Ñ(y) ≥ y} (y1 = 0 if Ñ(0) > 0),
  N_A(t) = #{odd v ≤ n : G̃_n(v) ≤ t},  t_j² = (n − T + m + j − 1)/n,
  b_A = max(0, N_A(t_1), max_{2≤j≤m} (N_A(t_j) − j + 2)),
every (b,l) is certified as soon as b_A ≤ y1 − m.

GA2. GA(b,l) is monotone: GA(b,l) ⇒ GA(b′,l′) for b′ ≥ b, l′ ≤ l (t_j(l) increases with l; the j-th condition
"N ≤ b or N − b + 1 ≤ j − 1" is easier for smaller N and larger b). GA(b,m) ⟺ b ≥ b_A (j = 1 needs N_A(t_1) ≤ b;
for j ≥ 2 the condition is N_A(t_j) ≤ b + j − 2). Hence: b ≥ b_A ⇒ GA(b,l) for all l ≤ m; b < b_A ≤ y1 − m ⇒
b + l ≤ y1 − 1 ⇒ G(b,l) by G1.

Sufficient conditions, for a parameter u1 (here 0.9) and Y1 = ⌊u1² q⌋:
 (A0) Ñ(0) = 0;  (A1) Ñ(y) ≤ y − 1 for 1 ≤ y ≤ Y1 (then y1 ≥ Y1 + 1);  (A2′) b_A ≤ Y1 + 1 − m.

## 2. Counting bound

Write N⁰(τ) = #{odd v ≤ n : G(v) ≤ τ}. Since G̃_x(v) ≤ t ⇒ G(v) ≤ t + 2^{ω(v)}/√(2x), Ñ(y) ≤ N⁰(√(y/q) + e_q),
N_A(t) ≤ N⁰(t + e_n), where e_x = 2^{ω_max(n)}/√(2x) and ω_max(n) = k for Π_k ≤ n < Π_{k+1} (Π_k = product of
the first k odd primes; k distinct odd primes have product ≥ Π_k). On each such interval e_x is largest at the
left end, and 2^k/√Π_k decreases in k (Π_{k+1}/Π_k ≥ 5 > 4); so e_sup := sup_{n ≥ N0} e_q(n) is the larger of
the values at N0 and at the next primorial (for N0 = 10⁸: e_sup,q = 0.02424 at n = Π_8 = 111546435, e_sup,n = 0.01714).

Small-prime classes. Q = odd primes ≤ z (z = 19), P = 2∏Q, κ = φ(P)/P, D⁺ = max_y (#{w ≤ y : (w,P) = 1} − κy)
(periodic; one-period scan gives D⁺ = 8.659…). For S ⊆ Q let S(v) = Q ∩ primes(v), dens(S) = ∏_{p∈S}(1/p)
∏_{p∈Q∖S}(1 − 1/p), G(S) = ∏_{p∈S}(1 − 1/p), U(S) = ∏_{p∈S} 1/(p^σ − 1) (σ = 1/2). Every odd v is uniquely u·w with
supp(u) = S(v) and (w,P) = 1, and G(v) = G(S)·G_L(w), G_L(w) = ∏_{p|w}(1 − 1/p).

 B1 (trivial)  #{odd v ≤ n : ∏S | v} ≤ n/(2∏S) + 1.
 B2 (class)    #{odd v ≤ n : S(v) = S} ≤ Σ_{u} (κ n/u + D⁺) ≤ (n/2) dens(S) + D⁺ n^σ U(S)
               (sums over u ≤ n with supp u = S, the only u with a nonzero count: κ Σ 1/u ≤ dens(S)/2;
               1 ≤ (n/u)^σ for u ≤ n;  Σ u^{−σ} ≤ U(S)).
 B3 (Rankin)   for τ < G(S), θ = τ/G(S), s > 0: 1[G_L(w) ≤ θ] ≤ θ^s g_s(w), g_s(w) = G_L(w)^{−s} = Σ_{d|w} h_s(d),
               h_s(p) = (1 − 1/p)^{−s} − 1 on squarefree d with prime factors > z. Then
               Σ_{w ≤ X, (w,P)=1} g_s(w) = Σ_d h_s(d) #{w′ ≤ X/d : (w′,P) = 1} ≤ κ X M_z(s) + D⁺ H(s,X),
               M_z(s) = ∏_{p>z}(1 + h_s(p)/p), H(s,X) = Σ_{d ≤ X} h_s(d) ≤ X^σ C_σ(s), C_σ(s) = ∏_{p>z}(1 + h_s(p)/p^σ);
               summing over u: count ≤ θ^s [ (n/2) dens(S) M_z(s) + D⁺ n^σ U(S) C_σ(s) ].
For n ≥ N0: n^σ ≤ (n/2)·2N0^{σ−1} and 1 ≤ (n/2)·2/N0, so N⁰(τ) ≤ (n/2) Φ(τ) with
 Φ(τ) = Σ_S min{ 1/∏S + 2/N0,  dens(S) + 2D⁺U(S)N0^{σ−1},  min_{s∈grid} θ^s [dens(S)M_z(s) + 2D⁺U(S)C_σ(s)N0^{σ−1}] }.
Φ is nondecreasing in τ. M_z, C_σ: exact products over primes ≤ X = 10⁷ times exp(tail), where (h_s(p) ≤ 1.001 s/p for
p > 10⁷ and s ≤ 80) log ∏_{p>X}(1 + h_s(p)/p^σ′) ≤ Σ_{p>X} 1.001 s p^{−1−σ′} ≤ 1.001 s X^{−σ′}/σ′, used with σ′ = 1 for M_z
(tail ≤ 1.001 s/X) and σ′ = σ for C_σ. (Using the σ-tail for M_z as well changes the margins only to 0.0241 / 0.0588.)

## 3. Verification (all n ≥ N0 simultaneously; δ = 1/(N0 − 1), so 1/(2q) ≤ δ, 1/q ≤ 2δ)

(A1-high) u ∈ [0.33, u1]: Ñ(y) ≤ N⁰(u + e_sup) ≤ q(1+δ)Φ(u + e_sup); suffices (1+δ)Φ(u_b + e_sup) + 2δ ≤ u_a² on
  grid cells [u_a, u_b] of width 5·10⁻⁴.  Result: min margin 0.0245 (at u ≈ 0.6335, where τ = u + e_sup ≈ 0.658
  and the Rankin bound for the class S = {3} is already close to that class's full size, before τ reaches 2/3).
(A1-low) u ≤ 0.33 and (A0): single Rankin over all odd primes, s = 4:
  N⁰(τ) ≤ τ⁴ Σ_{v odd ≤ n} G(v)^{−4} ≤ τ⁴[(n/2)M_odd(4) + n^σ C_odd,σ(4)]; N⁰(τ) = 0 for τ < G_min(n) = ∏_{first k odd p}(1 − 1/p).
  For τ = u + e ∈ [G_min(n), 0.33 + e_sup] it suffices that
  τ²(M_odd(1+δ) + 2(1+δ)N0^{σ−1}C_odd) + 1/(q G_min²) ≤ (1 − e/G_min)², with sup_{n≥N0} e/G_min = 0.0741 and
  sup 1/(q G_min²) taken over primorial intervals (both decrease in k from k = 8 on; the first interval starts at
  N0 = 10⁸, not at Π_7, so its values are taken at N0: e/G_min peaks at Π_8, 1/(q G_min²) at N0).
  Result: 0.4927 ≤ 0.8573. (A0) follows from e < G_min.
(A2′) j ∈ [1,m], ξ = (j−1)/n ∈ [0, 1/6]: t_j² ≤ 1/2 + 7/(6N0) + ξ (T ≥ 2n/3 − 7/6, m ≤ n/6), j − 2 ≥ 2qξ − 1,
  Y1 + 1 − m ≥ u1²q − q/3 − 1/6. Suffices (1+δ)Φ(√(1/2 + 7/(6N0) + ξ_b) + e_sup,n) − 2ξ_a + 3δ ≤ u1² − 1/3 on a
  401-point ξ grid. Recorded interval result: min margin approximately 0.058964, conservatively greater than 0.058 (at ξ = 0).

Floating point: the composite bounds (Euler products, Φ, class densities) carry a relative factor 1 + 10⁻⁹ in the
conservative direction; D⁺ (evaluated in exact integers: 8.65916745795…) and G(S) carry rounding below
10⁻¹¹ relative. The smallest margin (0.0245) exceeds all rounding effects by many orders of magnitude.

## 4. Conclusion

For every n ≥ 10⁸ the refined criterion b_A ≤ y1 − m holds, so Theorem G (FAMILY_G.md) gives #883(i) at n.
