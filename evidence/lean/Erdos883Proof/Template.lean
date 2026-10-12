import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference

/-!
# Cycle template

An injective map `f : Fin (k+3) → V` with `f i ~ f (i+1)` for all `i` gives a cycle of length `k+3`.
For the coprime graph induced on `A`, an odd skeleton `o 0, …, o l` (distinct, `o 0` coprime to `o l`) and
connectors `u 0, …, u (l-1)` (distinct, not in the skeleton, `u i` coprime to `o i` and `o (i+1)`) give `C_{2l+1}`.
-/

namespace Erdos883Proof

open SimpleGraph

theorem mem_cycleLengths_of_injective {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (f : Fin (k + 3) → V) (hf : Function.Injective f)
    (hadj : ∀ i : Fin (k + 3), G.Adj (f i) (f (i + 1))) : k + 3 ∈ G.cycleLengths := by
  have hcopy : cycleGraph (k + 3) ⊑ G := by
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro u v huv
    rcases (cycleGraph_adj (n := k + 1)).mp huv with h | h
    · have : u = v + 1 := by rw [← h]; exact (add_sub_cancel v u).symm
      rw [this]; exact (hadj v).symm
    · have : v = u + 1 := by rw [← h]; exact (add_sub_cancel u v).symm
      rw [this]; exact hadj u
  obtain ⟨v, p, hp, hlen⟩ := (cycleGraph_isContained_iff (by omega)).mp hcopy
  exact ⟨v, p, hp, hlen⟩

/-- The coprime graph on `ℕ` (as in formal-conjectures `Erdos883.coprimeGraph`). -/
def coprimeGraph : SimpleGraph ℕ := SimpleGraph.fromRel Nat.Coprime

lemma induce_coprime_adj {A : Set ℕ} {a b : A} (hab : (a : ℕ) ≠ b) (hc : Nat.Coprime a b) :
    (coprimeGraph.induce A).Adj a b := by
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, coprimeGraph,
    SimpleGraph.fromRel_adj]
  exact ⟨hab, Or.inl hc⟩

/-- Interleaving of a skeleton `o : ℕ → ℕ` and connectors `u : ℕ → ℕ`: `2i ↦ o i`, `2i+1 ↦ u i`. -/
def weave (o u : ℕ → ℕ) (k : ℕ) : ℕ := if k % 2 = 0 then o (k / 2) else u (k / 2)

/-- Cycle template: skeleton `o 0..o l` and connectors `u 0..u (l-1)` in `A` give `2l+1 ∈ oddCycleLengths`. -/
theorem template (A : Set ℕ) (l : ℕ) (hl : 1 ≤ l) (o u : ℕ → ℕ)
    (hoA : ∀ i ≤ l, o i ∈ A) (huA : ∀ i < l, u i ∈ A)
    (ho_inj : ∀ i ≤ l, ∀ j ≤ l, o i = o j → i = j)
    (hu_inj : ∀ i < l, ∀ j < l, u i = u j → i = j)
    (hou : ∀ i ≤ l, ∀ j < l, o i ≠ u j)
    (hclose : Nat.Coprime (o l) (o 0))
    (hleft : ∀ i < l, Nat.Coprime (o i) (u i))
    (hright : ∀ i < l, Nat.Coprime (u i) (o (i + 1))) :
    2 * l + 1 ∈ (coprimeGraph.induce A).oddCycleLengths := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  -- vertices `weave o u j` for `j ≤ 2l = 2k+2`
  have hw_mem : ∀ j : Fin (2 * k + 3), weave o u j ∈ A := by
    intro j
    unfold weave
    split_ifs with h
    · exact hoA _ (by omega)
    · exact huA _ (by omega)
  let f : Fin (2 * k + 3) → A := fun j => ⟨weave o u j, hw_mem j⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hv : weave o u a = weave o u b := congrArg Subtype.val hab
    unfold weave at hv
    apply Fin.ext
    split_ifs at hv with ha hb hb
    · have := ho_inj _ (by omega) _ (by omega) hv; omega
    · exact absurd hv (hou _ (by omega) _ (by omega))
    · exact absurd hv.symm (hou _ (by omega) _ (by omega))
    · have := hu_inj _ (by omega) _ (by omega) hv; omega
  have hadj : ∀ j : Fin (2 * k + 3), (coprimeGraph.induce A).Adj (f j) (f (j + 1)) := by
    intro j
    -- value of j+1
    by_cases hlast : (j : ℕ) = 2 * k + 2
    · have hjl : j = Fin.last (2 * k + 2) := Fin.ext (by simp [hlast])
      have hj1 : ((j + 1 : Fin (2 * k + 3)) : ℕ) = 0 := by
        rw [hjl, Fin.last_add_one]; rfl
      apply induce_coprime_adj
      · simp only [f, weave, hj1, hlast]
        simp only [show (2 * k + 2) % 2 = 0 by omega, show (2 * k + 2) / 2 = k + 1 by omega,
          Nat.zero_div, if_true]
        intro h
        exact absurd (ho_inj _ le_rfl _ (by omega) h) (by omega)
      · simp only [f, weave, hj1, hlast]
        simp only [show (2 * k + 2) % 2 = 0 by omega, show (2 * k + 2) / 2 = k + 1 by omega,
          Nat.zero_div, if_true]
        exact hclose
    · have hj1 : ((j + 1 : Fin (2 * k + 3)) : ℕ) = j + 1 := by
        rw [Fin.val_add_one_of_lt]
        exact Fin.lt_last_iff_ne_last.mpr (by intro h; apply hlast; rw [h]; simp)
      have hjlt : (j : ℕ) < 2 * k + 2 := by have := j.isLt; omega
      apply induce_coprime_adj
      · simp only [f, hj1]
        unfold weave
        split_ifs with h1 h2 h2
        · omega
        · exact hou _ (by omega) _ (by omega)
        · exact fun h => hou _ (by omega) _ (by omega) h.symm
        · omega
      · simp only [f, hj1]
        unfold weave
        split_ifs with h1 h2 h2
        · omega
        · have : (j : ℕ) / 2 = ((j : ℕ) + 1) / 2 := by omega
          rw [← this]; exact hleft _ (by omega)
        · have : (j : ℕ) / 2 + 1 = ((j : ℕ) + 1) / 2 := by omega
          rw [← this]; exact hright _ (by omega)
        · omega
  have hmem := mem_cycleLengths_of_injective (coprimeGraph.induce A) (2 * k) f hinj hadj
  refine ⟨?_, ?_⟩
  · have e : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [e]; exact hmem
  · exact ⟨k + 1, by omega⟩

end Erdos883Proof
