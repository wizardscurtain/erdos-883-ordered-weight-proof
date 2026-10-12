import Erdos883Proof.FamilyG

/-!
# Theorem G and the link to `erdos_883.parts.i`

`CriterionG n Y B` is the refined full-coverage criterion of FAMILY_G.md / ANALYTIC_TAIL_G.md with explicit
witnesses: `Y` certifies `y1 ≥ Y + 1` and `B ≥ b_A`. It implies the per-n statement `Stmt n`, and `Stmt n`
for every `n ≥ 6` is exactly the formal-conjectures statement (with `answer = True`).
-/

namespace Erdos883Proof

open Finset

/-- Per-n statement of Erdős #883(i). -/
def Stmt (n : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 n → T n < #A → ∀ l, 1 ≤ l → l ≤ n / 6 →
    2 * l + 1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

/-- Theorem-G criterion with witnesses. -/
structure CriterionG (n Y B : ℕ) : Prop where
  hG0 : NG n 0 = 0
  hG : ∀ y, 1 ≤ y → y ≤ Y → NG n y ≤ y - 1
  hA1 : NA n (n - T n + n / 6) ≤ B
  hA : ∀ j, 2 ≤ j → j ≤ n / 6 → NA n (n - T n + n / 6 + j - 1) ≤ B + j - 2
  hYB : B + n / 6 ≤ Y + 1

lemma NA_mono {n y y' : ℕ} (h : y ≤ y') : NA n y ≤ NA n y' := by
  unfold NA
  apply card_le_card
  intro v hv
  simp only [mem_filter] at hv ⊢
  refine ⟨hv.1, le_trans hv.2 (Real.sqrt_le_sqrt ?_)⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast h

lemma certG_of {n Y B : ℕ} (hc : CriterionG n Y B) {b l : ℕ} (hbl : b + l ≤ Y + 1) : CertG n b l := by
  intro j hj1 hjl
  set y := b + j - 1 with hy
  have hyY : y ≤ Y := by omega
  by_cases hy0 : y = 0
  · have hb0 : b = 0 := by omega
    rw [hy0, hc.hG0, hb0]; simp
  · have hN := hc.hG y (by omega) hyY
    split_ifs with h <;> omega

lemma certGA_of {n Y B : ℕ} (hc : CriterionG n Y B) {b l : ℕ} (hBb : B ≤ b) (hlm : l ≤ n / 6) :
    CertGA n b l := by
  intro j hj1 hjl
  have hmono : NA n (n - T n + l + j - 1) ≤ NA n (n - T n + n / 6 + j - 1) := NA_mono (by omega)
  by_cases hj : j = 1
  · subst hj
    have h1 := hc.hA1
    have : n - T n + n / 6 + 1 - 1 = n - T n + n / 6 := by omega
    rw [this] at hmono
    split_ifs with h <;> omega
  · have h2 := hc.hA j (by omega) (by omega)
    split_ifs with h <;> omega

lemma oddCycleLengths_mono {A A' : Set ℕ} (h : A' ⊆ A) :
    (coprimeGraph.induce A').oddCycleLengths ⊆ (coprimeGraph.induce A).oddCycleLengths := by
  rintro L ⟨⟨v, p, hp, hlen⟩, hodd⟩
  let f := SimpleGraph.induceHomOfLE (G := coprimeGraph) h
  refine ⟨⟨f v, p.map f.toHom, ?_, by simpa using hlen⟩, hodd⟩
  exact (SimpleGraph.Walk.isCycle_map_iff_of_injective f.injective).mpr hp

theorem stmt_of_criterion {n Y B : ℕ} (hn : 6 ≤ n) (hc : CriterionG n Y B) : Stmt n := by
  intro A hA hTA l hl1 hlm
  obtain ⟨A', hA'A, hA'⟩ := exists_subset_card_eq (s := A) (n := T n + 1) (by omega)
  have hA'n : A' ⊆ Icc 1 n := hA'A.trans hA
  apply oddCycleLengths_mono (A' := (A' : Set ℕ)) (by exact_mod_cast hA'A)
  by_cases hB : B ≤ missEven n A'
  · exact familyGA hn hA'n hA' hl1 hlm (certGA_of hc hB hlm)
  · exact familyG hn hA'n hA' hl1 hlm (certG_of hc (by have := hc.hYB; omega))

/-- The formal-conjectures statement `erdos_883.parts.i` (with answer `True`) follows from `Stmt n`
for every `n ≥ 6`. The graph `coprimeGraph` here is definitionally `SimpleGraph.fromRel Nat.Coprime`,
the same as `Erdos883.coprimeGraph`. -/
theorem erdos883_i_of (h : ∀ n, 6 ≤ n → Stmt n) :
    ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 n → n / 2 + n / 3 - n / 6 < A.card →
      ∀ L : ℕ, Odd L → 3 ≤ L → L ≤ n / 3 + 1 →
        L ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  intro n A hA hcard L hL h3 hLn
  obtain ⟨l, rfl⟩ := hL
  have hl1 : 1 ≤ l := by omega
  have hlm : l ≤ n / 6 := by omega
  have hn : 6 ≤ n := by omega
  exact h n hn A hA hcard l hl1 hlm

end Erdos883Proof
