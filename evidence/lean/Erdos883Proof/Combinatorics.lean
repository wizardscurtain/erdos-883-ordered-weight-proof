import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-!
# Combinatorial lemmas for the Family G/GA certificates

* `coprime_pair` (L1): any `h+1` odd integers in `[1,n]`, `h = n/3 - n/6`, `n ≥ 3`, contain a coprime pair.
* `ordered_hall` (L3): lists with `#{i | #L_i ≤ j-1} ≤ j-1` for all `j` have an SDR.
* `exists_top` : a subset of the `k` largest elements w.r.t. a real weight.
* `exists_antitone_enum` : an injective, weight-antitone enumeration of `k` elements of a finset.
* `bad_count` (P1): in a path whose middle is weight-antitone, the gaps touching `{w < t}` number at most
  `c + [c ≥ 1]`, `c = #{vertices with w < t}`.
* `tail_count` (P2): the tail lemma.
-/

namespace Erdos883Proof

open Finset

/-! ### L1 -/

/-- group index: `1 ↦ 0`, odd `v ≥ 3 ↦ (v-3)/6`; each group is pairwise coprime. -/
def grp (v : ℕ) : ℕ := (v - 3) / 6

lemma coprime_of_grp_eq {v w : ℕ} (hv : Odd v) (hw : Odd w) (hne : v ≠ w) (hg : grp v = grp w) :
    Nat.Coprime v w := by
  rcases Nat.lt_or_ge v 3 with h | h
  · have : v = 1 := by obtain ⟨k, rfl⟩ := hv; omega
    subst this; exact Nat.coprime_one_left w
  rcases Nat.lt_or_ge w 3 with h' | h'
  · have : w = 1 := by obtain ⟨k, rfl⟩ := hw; omega
    subst this; exact Nat.coprime_one_right v
  unfold grp at hg
  wlog hvw : v < w generalizing v w
  · exact (this hw hv (Ne.symm hne) hg.symm h' h (by omega)).symm
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨c, rfl⟩ := hw
  have hd : c = a + 1 ∨ c = a + 2 := by omega
  rcases hd with rfl | rfl
  · -- w = v + 2
    have : 2 * (a + 1) + 1 = (2 * a + 1) + 2 := by ring
    rw [this, Nat.coprime_self_add_right]
    exact Nat.coprime_two_right.mpr ⟨a, rfl⟩
  · have : 2 * (a + 2) + 1 = (2 * a + 1) + 4 := by ring
    rw [this, Nat.coprime_self_add_right]
    have h2 : Nat.Coprime (2 * a + 1) 2 := Nat.coprime_two_right.mpr ⟨a, rfl⟩
    simpa using Nat.Coprime.pow_right 2 h2

theorem coprime_pair {n : ℕ} (hn : 3 ≤ n) (Y : Finset ℕ) (hY : ∀ v ∈ Y, Odd v ∧ 1 ≤ v ∧ v ≤ n)
    (hcard : n / 3 - n / 6 + 1 ≤ #Y) : ∃ a ∈ Y, ∃ a' ∈ Y, a ≠ a' ∧ Nat.Coprime a a' := by
  have hmaps : ∀ v ∈ Y, grp v ∈ range (n / 3 - n / 6) := by
    intro v hv
    obtain ⟨hodd, h1, h2⟩ := hY v hv
    rw [mem_range]; unfold grp
    obtain ⟨k, rfl⟩ := hodd
    omega
  have hlt : #(range (n / 3 - n / 6)) < #Y := by rw [card_range]; omega
  obtain ⟨a, ha, a', ha', hne, hg⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact ⟨a, ha, a', ha', hne, coprime_of_grp_eq (hY a ha).1 (hY a' ha').1 hne hg⟩

/-! ### Ordered Hall -/

theorem ordered_hall {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (t : ι → Finset α)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card ι → #(univ.filter (fun i => #(t i) ≤ j - 1)) ≤ j - 1) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i := by
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  intro s
  by_contra hlt
  push Not at hlt
  set k := #s with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hlt; exact absurd hlt (Nat.not_lt_zero _)
    · exact h0
  have hsub : s ⊆ univ.filter (fun i => #(t i) ≤ k - 1) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    have : t i ⊆ s.biUnion t := subset_biUnion_of_mem t hi
    have := card_le_card this
    omega
  have h1 := card_le_card hsub
  have h2 := h k hk1 (by rw [hk]; exact card_le_univ s)
  omega

/-! ### Choosing the top `k` elements -/

theorem exists_top (w : ℕ → ℝ) : ∀ (Y : Finset ℕ) (k : ℕ), k ≤ #Y →
    ∃ Y0 ⊆ Y, #Y0 = k ∧ ∀ y ∈ Y, y ∉ Y0 → ∀ y0 ∈ Y0, w y ≤ w y0 := by
  intro Y
  induction Y using Finset.strongInduction with
  | H Y ih =>
    intro k hk
    by_cases heq : k = #Y
    · exact ⟨Y, subset_refl _, heq.symm, fun y hy hy' => absurd hy hy'⟩
    · have hne : Y.Nonempty := by
        rw [nonempty_iff_ne_empty]; rintro rfl; simp at hk heq; omega
      obtain ⟨ym, hym, hmin⟩ := Y.exists_min_image w hne
      have hsub : Y.erase ym ⊂ Y := erase_ssubset hym
      obtain ⟨Y0, hY0, hc, hprop⟩ := ih (Y.erase ym) hsub k (by rw [card_erase_of_mem hym]; omega)
      refine ⟨Y0, hY0.trans (erase_subset ym Y), hc, ?_⟩
      intro y hy hy0 y0 hy0'
      by_cases hyy : y = ym
      · subst hyy; exact hmin y0 (mem_of_mem_erase (hY0 hy0'))
      · exact hprop y (mem_erase.mpr ⟨hyy, hy⟩) hy0 y0 hy0'

/-- An injective enumeration `e : ℕ → ℕ` of `k` elements of `S` (on indices `< k`) with antitone weights. -/
theorem exists_antitone_enum (w : ℕ → ℝ) : ∀ (S : Finset ℕ) (k : ℕ), k ≤ #S →
    ∃ e : ℕ → ℕ, (∀ i < k, e i ∈ S) ∧ (∀ i < k, ∀ j < k, e i = e j → i = j) ∧
      (∀ i j, i ≤ j → j < k → w (e j) ≤ w (e i)) := by
  intro S k
  induction k generalizing S with
  | zero => intro _; exact ⟨fun _ => 0, by simp, by simp, by intro i j _ hj; omega⟩
  | succ k ih =>
    intro hk
    have hne : S.Nonempty := by rw [← card_pos]; omega
    obtain ⟨x, hx, hmax⟩ := S.exists_max_image w hne
    obtain ⟨e, he1, he2, he3⟩ := ih (S.erase x) (by rw [card_erase_of_mem hx]; omega)
    refine ⟨fun i => if i = 0 then x else e (i - 1), ?_, ?_, ?_⟩
    · intro i hi
      by_cases h0 : i = 0
      · simp [h0, hx]
      · simp only [h0, if_false]; exact mem_of_mem_erase (he1 _ (by omega))
    · intro i hi j hj hij
      by_cases h0 : i = 0 <;> by_cases h0' : j = 0 <;> simp only [h0, h0', if_true, if_false] at hij
      · omega
      · exact absurd hij.symm (ne_of_mem_erase (he1 _ (by omega)))
      · exact absurd hij (ne_of_mem_erase (he1 _ (by omega)))
      · have := he2 _ (by omega) _ (by omega) hij; omega
    · intro i j hij hj
      by_cases h0 : i = 0 <;> by_cases h0' : j = 0
      · subst h0; subst h0'; simp
      · subst h0; simp only [if_true, h0', if_false]
        exact hmax _ (mem_of_mem_erase (he1 _ (by omega)))
      · omega
      · simp only [h0, h0', if_false]; exact he3 _ _ (by omega) (by omega)

/-! ### P1: bad-gap count on a path with antitone middle -/

theorem bad_count (w : ℕ → ℝ) (t : ℝ) (l : ℕ) (o : ℕ → ℕ)
    (hmid : ∀ i j, 1 ≤ i → i ≤ j → j + 1 ≤ l → w (o j) ≤ w (o i)) :
    #((range l).filter (fun i => w (o i) < t ∨ w (o (i + 1)) < t)) ≤
      #((range (l + 1)).filter (fun i => w (o i) < t)) +
        (if 0 < #((range (l + 1)).filter (fun i => w (o i) < t)) then 1 else 0) := by
  classical
  set C := (range (l + 1)).filter (fun i => w (o i) < t) with hC
  set B := (range l).filter (fun i => w (o i) < t ∨ w (o (i + 1)) < t) with hB
  -- B ⊆ B' ∪ {l-1},  B' = B ∩ range (l-1) injects into C
  set B' := B.filter (fun i => i + 1 < l) with hB'
  have hBsplit : B ⊆ B' ∪ (B.filter (fun i => ¬ (i + 1 < l))) := by
    intro i hi
    by_cases h : i + 1 < l
    · exact mem_union_left _ (mem_filter.mpr ⟨hi, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi, h⟩)
  have hlast : #(B.filter (fun i => ¬ (i + 1 < l))) ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    simp only [hB, mem_filter, mem_range] at ha hb
    omega
  let φ : ℕ → ℕ := fun i => if w (o (i + 1)) < t then i + 1 else i
  have hφ : ∀ i ∈ B', φ i ∈ C := by
    intro i hi
    simp only [hB', hB, mem_filter, mem_range] at hi
    obtain ⟨⟨hil, hor⟩, hil'⟩ := hi
    simp only [φ, hC, mem_filter, mem_range]
    split_ifs with h
    · exact ⟨by omega, h⟩
    · exact ⟨by omega, hor.resolve_right h⟩
  have hφinj : Set.InjOn φ B' := by
    intro i hi j hj hij
    simp only [hB', hB, mem_coe, mem_filter, mem_range] at hi hj
    simp only [φ] at hij
    -- if the second case occurs at index i ≥ 1 we get a contradiction with antitonicity
    have key : ∀ i, 1 ≤ i → i + 1 < l → (w (o i) < t ∨ w (o (i + 1)) < t) → w (o (i + 1)) < t := by
      intro i hi1 hil hor
      rcases hor with h | h
      · exact lt_of_le_of_lt (hmid i (i + 1) hi1 (by omega) (by omega)) h
      · exact h
    split_ifs at hij with h1 h2 h2
    · omega
    · have : j = 0 ∨ 1 ≤ j := by omega
      rcases this with h0 | h0
      · omega
      · exact absurd (key j h0 hj.2 hj.1.2) h2
    · have : i = 0 ∨ 1 ≤ i := by omega
      rcases this with h0 | h0
      · omega
      · exact absurd (key i h0 hi.2 hi.1.2) h1
    · exact hij
  have hB'C : #B' ≤ #C := card_le_card_of_injOn φ hφ hφinj
  have hBle : #B ≤ #B' + 1 := (card_le_card hBsplit).trans ((card_union_le _ _).trans (by omega))
  by_cases hC0 : 0 < #C
  · simp only [hC0, if_true]; omega
  · simp only [hC0, if_false]
    have hCe : C = ∅ := by rw [← card_eq_zero]; omega
    have : B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro i hi
      simp only [hB, mem_filter, mem_range] at hi
      rcases hi.2 with h | h
      · have : i ∈ C := by simp [hC, h]; omega
        rw [hCe] at this; simp at this
      · have : i + 1 ∈ C := by simp [hC, h]; omega
        rw [hCe] at this; simp at this
    rw [this]; simp

/-! ### P2: tail lemma -/

theorem tail_count (w : ℕ → ℝ) (U Y Y0 : Finset ℕ) (t : ℝ) (b : ℕ) (hYU : Y ⊆ U) (hY0 : Y0 ⊆ Y)
    (hcard : #Y = #Y0 + b) (htop : ∀ y ∈ Y, y ∉ Y0 → ∀ y0 ∈ Y0, w y ≤ w y0) :
    #(Y0.filter (fun v => w v < t)) ≤ #(U.filter (fun v => w v ≤ t)) - b := by
  classical
  by_cases hne : (Y0.filter (fun v => w v < t)).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    rw [mem_filter] at hy0
    have hdisj : Disjoint (Y0.filter (fun v => w v < t)) (Y \ Y0) := by
      rw [disjoint_left]; intro a ha hb
      exact (mem_sdiff.mp hb).2 (mem_filter.mp ha).1
    have hsub : (Y0.filter (fun v => w v < t)) ∪ (Y \ Y0) ⊆ U.filter (fun v => w v ≤ t) := by
      intro v hv
      rw [mem_union] at hv
      rw [mem_filter]
      rcases hv with hv | hv
      · exact ⟨hYU (hY0 (mem_filter.mp hv).1), le_of_lt (mem_filter.mp hv).2⟩
      · obtain ⟨hvY, hvY0⟩ := mem_sdiff.mp hv
        exact ⟨hYU hvY, le_trans (htop v hvY hvY0 y0 hy0.1) (le_of_lt hy0.2)⟩
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hY0] at h1
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty]; exact Nat.zero_le _

end Erdos883Proof
