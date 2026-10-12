import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

/-!
# Legendre-type counting with an explicit error term

`cnt P y` counts the integers `1 ≤ i ≤ ⌊y⌋` divisible by no element of the finite set of primes `P`.
We prove `|cnt P y - y ∏_{p∈P} (1 - 1/p)| < 2^(#P - 1)` for nonempty `P` (by induction on `P`, using
`cnt (insert p P) y = cnt P y - cnt P (y/p)`), and deduce the pair bound of FAMILY_G.md (C1, C2).
-/

namespace Erdos883Proof

open Finset

/-- Number of `i ∈ [1, ⌊y⌋₊]` divisible by no element of `P`. -/
noncomputable def cnt (P : Finset ℕ) (y : ℝ) : ℕ :=
  #{i ∈ Icc 1 ⌊y⌋₊ | ∀ p ∈ P, ¬ p ∣ i}

/-- `∏_{p ∈ P} (1 - 1/p)`. -/
noncomputable def dens (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

lemma cnt_empty (y : ℝ) : cnt ∅ y = ⌊y⌋₊ := by
  simp [cnt]

lemma cnt_split {p : ℕ} {P : Finset ℕ} (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hpP : p ∉ P)
    (y : ℝ) : cnt P y = cnt (insert p P) y + cnt P (y / p) := by
  classical
  unfold cnt
  rw [← Finset.card_filter_add_card_filter_not
    (s := (Icc 1 ⌊y⌋₊).filter (fun i => ∀ q ∈ P, ¬ q ∣ i)) (fun i => ¬ p ∣ i)]
  congr 1
  · rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro i _
    simp only [forall_mem_insert]
    tauto
  · rw [Finset.filter_filter, Nat.floor_div_natCast]
    symm
    refine Finset.card_bij (fun j _ => p * j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      obtain ⟨⟨hj1, hj2⟩, hjP⟩ := hj
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact le_trans hj1 (Nat.le_mul_of_pos_left j hp.pos)
      · have := (Nat.le_div_iff_mul_le hp.pos).mp hj2
        rw [mul_comm] at this; exact this
      · intro q hq hqd
        have hq' := hP q hq
        rcases (Nat.Prime.dvd_mul hq').mp hqd with h | h
        · have : q = p := (Nat.prime_dvd_prime_iff_eq hq' hp).mp h
          exact hpP (this ▸ hq)
        · exact hjP q hq h
      · exact not_not.mpr (dvd_mul_right p j)
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc, not_not] at hi
      obtain ⟨⟨hi1, hi2⟩, hiP, hpi⟩ := hi
      obtain ⟨j, rfl⟩ := hpi
      refine ⟨j, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · simp [h] at hi1
        · exact h
      · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact hi2)
      · intro q hq hqj
        exact hiP q hq (dvd_mul_of_dvd_right hqj p)

lemma dens_insert {p : ℕ} {P : Finset ℕ} (hpP : p ∉ P) :
    dens (insert p P) = (1 - 1 / (p : ℝ)) * dens P := by
  simp [dens, prod_insert hpP]

/-- The error `cnt P y - y · dens P`. -/
noncomputable def err (P : Finset ℕ) (y : ℝ) : ℝ := (cnt P y : ℝ) - y * dens P

lemma err_insert {p : ℕ} {P : Finset ℕ} (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hpP : p ∉ P)
    (y : ℝ) : err (insert p P) y = err P y - err P (y / p) := by
  have hc := cnt_split hp hP hpP y
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold err
  rw [dens_insert hpP]
  have : (cnt P y : ℝ) = cnt (insert p P) y + cnt P (y / p) := by exact_mod_cast hc
  rw [this]
  field_simp
  ring

lemma err_empty_bounds {y : ℝ} (hy : 0 ≤ y) : -1 < err ∅ y ∧ err ∅ y ≤ 0 := by
  unfold err
  simp only [cnt_empty, dens, prod_empty, mul_one]
  constructor
  · linarith [Nat.lt_floor_add_one y]
  · linarith [Nat.floor_le hy]

/-- Main error bound: for a nonempty finite set of primes, `|err P y| < 2^(#P - 1)`. -/
theorem err_bound (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) :
    ∀ y : ℝ, 0 ≤ y → (P = ∅ → -1 < err P y ∧ err P y ≤ 0) ∧
      (P ≠ ∅ → |err P y| < 2 ^ (#P - 1)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro y hy
    exact ⟨fun _ => err_empty_bounds hy, fun h => absurd rfl h⟩
  | insert p P hpP ih =>
    intro y hy
    have hp : p.Prime := hP p (mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hyp : 0 ≤ y / p := div_nonneg hy (Nat.cast_nonneg p)
    refine ⟨fun h => absurd h (insert_ne_empty p P), fun _ => ?_⟩
    rw [err_insert hp hP' hpP, card_insert_of_notMem hpP]
    by_cases hPe : P = ∅
    · obtain ⟨a1, a2⟩ := (ih hP' y hy).1 hPe
      obtain ⟨b1, b2⟩ := (ih hP' (y / p) hyp).1 hPe
      subst hPe
      simp only [card_empty, zero_add, Nat.sub_self, pow_zero]
      rw [abs_lt]
      constructor <;> linarith
    · have ha := (ih hP' y hy).2 hPe
      have hb := (ih hP' (y / p) hyp).2 hPe
      have hk : #P ≠ 0 := by
        rwa [Ne, card_eq_zero]
      have hpow : (2 : ℝ) ^ (#P + 1 - 1) = 2 ^ (#P - 1) + 2 ^ (#P - 1) := by
        rw [Nat.add_sub_cancel, ← two_mul, ← pow_succ']
        congr 1
        omega
      rw [hpow]
      calc |err P y - err P (y / p)| ≤ |err P y| + |err P (y / p)| := abs_sub _ _
        _ < 2 ^ (#P - 1) + 2 ^ (#P - 1) := add_lt_add ha hb

theorem cnt_lower {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (hne : P.Nonempty) {y : ℝ} (hy : 0 ≤ y) :
    y * dens P - 2 ^ (#P - 1) < cnt P y := by
  have h := ((err_bound P hP y hy).2 (nonempty_iff_ne_empty.mp hne))
  have := (abs_lt.mp h).1
  unfold err at this
  linarith

/-! ### From prime sets to coprimality -/

/-- `G v = ∏_{p | v} (1 - 1/p)`. -/
noncomputable def G (v : ℕ) : ℝ := dens v.primeFactors

/-- `ω v` = number of distinct prime factors. -/
def omega (v : ℕ) : ℕ := #v.primeFactors

lemma coprime_iff_forall_primeFactors {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0) :
    Nat.Coprime k m ↔ ∀ p ∈ m.primeFactors, ¬ p ∣ k := by
  rw [← Nat.disjoint_primeFactors hk hm, Finset.disjoint_right]
  apply forall₂_congr
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  simp [Nat.mem_primeFactors, hpp, hk]

lemma card_coprime_eq_cnt {m : ℕ} (hm : m ≠ 0) (x : ℕ) :
    #{k ∈ Icc 1 x | Nat.Coprime k m} = cnt m.primeFactors x := by
  unfold cnt
  rw [Nat.floor_natCast]
  congr 1
  apply Finset.filter_congr
  intro k hk
  have hk0 : k ≠ 0 := by
    have := (mem_Icc.mp hk).1
    omega
  exact coprime_iff_forall_primeFactors hk0 hm

lemma dens_nonneg_le_one {P : Finset ℕ} (hP : ∀ q ∈ P, 1 ≤ q) : 0 ≤ dens P ∧ dens P ≤ 1 := by
  unfold dens
  constructor
  · apply prod_nonneg
    intro q hq
    have : (1 : ℝ) ≤ q := by exact_mod_cast hP q hq
    have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
    linarith
  · apply prod_le_one
    · intro q hq
      have : (1 : ℝ) ≤ q := by exact_mod_cast hP q hq
      have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
      linarith
    · intro q hq
      have : (0 : ℝ) ≤ 1 / q := by positivity
      linarith

lemma dens_mul_le_union (A B : Finset ℕ) (hA : ∀ q ∈ A, 1 ≤ q) (hB : ∀ q ∈ B, 1 ≤ q) :
    dens A * dens B ≤ dens (A ∪ B) := by
  classical
  have hu : A ∪ B = A ∪ (B \ A) := by
    ext x; simp only [mem_union, mem_sdiff]; tauto
  have hd : Disjoint A (B \ A) := disjoint_sdiff
  have h1 : dens (A ∪ B) = dens A * dens (B \ A) := by
    rw [hu]; unfold dens; rw [prod_union hd]
  have hB2 : dens B = dens (B \ A) * dens (B ∩ A) := by
    unfold dens
    rw [← prod_union (disjoint_sdiff_inter B A), sdiff_union_inter]
  have hBA := dens_nonneg_le_one (P := B \ A) (fun q hq => hB q (mem_sdiff.mp hq).1)
  have hBi := dens_nonneg_le_one (P := B ∩ A) (fun q hq => hB q (mem_inter.mp hq).1)
  have hA' := dens_nonneg_le_one hA
  rw [h1, hB2]
  have : dens (B \ A) * dens (B ∩ A) ≤ dens (B \ A) := by
    nlinarith [hBA.1, hBi.2]
  exact mul_le_mul_of_nonneg_left this hA'.1

/-- C1 for a pair: `#{k ≤ x : gcd(k, o o') = 1} > x G(o) G(o') - 2^(ω o + ω o' - 1)`. -/
theorem pair_count (o o' x : ℕ) (ho : o ≠ 0) (ho' : o' ≠ 0) (h1 : 1 < o * o') :
    (x : ℝ) * (G o * G o') - 2 ^ (omega o + omega o' - 1) <
      #{k ∈ Icc 1 x | Nat.Coprime k (o * o')} := by
  have hm : o * o' ≠ 0 := mul_ne_zero ho ho'
  rw [card_coprime_eq_cnt hm]
  set P := (o * o').primeFactors with hPdef
  have hPp : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hne : P.Nonempty := Nat.nonempty_primeFactors.mpr h1
  have hlow := cnt_lower hPp hne (Nat.cast_nonneg x)
  have hunion : P = o.primeFactors ∪ o'.primeFactors := Nat.primeFactors_mul ho ho'
  have hG : G o * G o' ≤ dens P := by
    rw [hunion]
    exact dens_mul_le_union _ _ (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_lt.le)
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_lt.le)
  have hcard : #P ≤ omega o + omega o' := by
    rw [hunion]; exact card_union_le _ _
  have hpow : (2 : ℝ) ^ (#P - 1) ≤ 2 ^ (omega o + omega o' - 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hcard 1)
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have : (x : ℝ) * (G o * G o') ≤ x * dens P := mul_le_mul_of_nonneg_left hG hx
  linarith

/-- The shifted weight `G̃_x(v) = G(v) - 2^{ω(v)} / √(2x)`. -/
noncomputable def Gt (x : ℕ) (v : ℕ) : ℝ := G v - 2 ^ omega v / Real.sqrt (2 * x)

/-- C2: if both shifted weights are nonnegative, the coprime count exceeds `x G̃(o) G̃(o')`. -/
theorem pair_count_tilde (o o' x : ℕ) (ho : o ≠ 0) (ho' : o' ≠ 0) (h1 : 1 < o * o') (hx : 0 < x)
    (hg : 0 ≤ Gt x o) (hg' : 0 ≤ Gt x o') :
    (x : ℝ) * (Gt x o * Gt x o') < #{k ∈ Icc 1 x | Nat.Coprime k (o * o')} := by
  have hc := pair_count o o' x ho ho' h1
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  set s := Real.sqrt (2 * (x : ℝ)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s * s = 2 * x := Real.mul_self_sqrt (by positivity)
  set e := (2 : ℝ) ^ omega o / s with he
  set e' := (2 : ℝ) ^ omega o' / s with he'
  -- 2^(ω+ω'-1) = x e e'  (ω + ω' ≥ 1 since o o' > 1)
  have hω : 1 ≤ omega o + omega o' := by
    have hne : (o * o').primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h1
    have hcard : #(o * o').primeFactors ≤ omega o + omega o' := by
      rw [Nat.primeFactors_mul ho ho']; exact card_union_le _ _
    have := hne.card_pos
    omega
  have hpow : (2 : ℝ) ^ (omega o + omega o' - 1) = x * (e * e') := by
    have h2 : (2 : ℝ) ^ (omega o + omega o') = 2 * 2 ^ (omega o + omega o' - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [he, he', div_mul_div_comm, hss, ← pow_add, h2]
    field_simp
  rw [hpow] at hc
  unfold Gt at hg hg'
  rw [← he] at hg; rw [← he'] at hg'
  have hGe : 0 ≤ G o - e := hg
  have hGe' : 0 ≤ G o' - e' := hg'
  have he0 : 0 ≤ e := by positivity
  have he0' : 0 ≤ e' := by positivity
  have key : (G o - e) * (G o' - e') ≤ G o * G o' - e * e' := by
    nlinarith [mul_nonneg he0' hGe, mul_nonneg he0 hGe']
  have : (x : ℝ) * ((G o - e) * (G o' - e')) ≤ x * (G o * G o' - e * e') :=
    mul_le_mul_of_nonneg_left key hxr.le
  unfold Gt
  rw [← he, ← he']
  linarith

end Erdos883Proof
