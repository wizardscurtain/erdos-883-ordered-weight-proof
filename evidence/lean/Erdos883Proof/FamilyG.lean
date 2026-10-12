import Erdos883Proof.Counting
import Erdos883Proof.Template
import Erdos883Proof.Combinatorics

/-!
# Families G and GA (FAMILY_G.md) and the per-n Theorem G

Everything is stated for a fixed `n ≥ 6` and a set `A ⊆ [1,n]` with `#A = T+1`.
`NG n y = #{odd v ≤ n : G̃_q(v) ≤ √(y/q)}` and `NA n y = #{odd v ≤ n : G̃_n(v) ≤ √(y/n)}`.
-/

namespace Erdos883Proof

open Finset

/-- `T(n) = ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋`. -/
def T (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/-- odd integers in `[1, n]`. -/
def odds (n : ℕ) : Finset ℕ := (Icc 1 n).filter Odd

/-- `Ñ(y)` for Family G. -/
noncomputable def NG (n y : ℕ) : ℕ :=
  #((odds n).filter (fun v => Gt (n / 2) v ≤ Real.sqrt ((y : ℝ) / ((n / 2 : ℕ) : ℝ))))

/-- The count for Family GA. -/
noncomputable def NA (n y : ℕ) : ℕ :=
  #((odds n).filter (fun v => Gt n v ≤ Real.sqrt ((y : ℝ) / (n : ℝ))))

/-- number of even integers of `[1,n]` missing from `A`. -/
def missEven (n : ℕ) (A : Finset ℕ) : ℕ := #((Icc 1 (n / 2)).filter (fun k => 2 * k ∉ A))

section Setup

variable {n : ℕ} {A : Finset ℕ}

lemma odd_part_card (hA : A ⊆ Icc 1 n) (hcard : #A = T n + 1) :
    #(A.filter Odd) = n / 3 - n / 6 + 1 + missEven n A := by
  classical
  have hsplit := card_filter_add_card_filter_not (s := A) Odd
  have hE : #(A.filter (fun u => ¬ Odd u)) = #((Icc 1 (n / 2)).filter (fun k => 2 * k ∈ A)) := by
    symm
    refine card_bij (fun k _ => 2 * k) ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_Icc] at hk
      simp only [mem_filter, Nat.not_odd_iff_even]
      exact ⟨hk.2, even_two_mul k⟩
    · intro a _ b _ h; omega
    · intro u hu
      simp only [mem_filter, Nat.not_odd_iff_even] at hu
      obtain ⟨huA, k, hk⟩ := hu
      have hu' := mem_Icc.mp (hA huA)
      refine ⟨k, ?_, by omega⟩
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by rw [show 2 * k = u by omega]; exact huA⟩
  have hq := card_filter_add_card_filter_not (s := Icc 1 (n / 2)) (fun k => 2 * k ∈ A)
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hq
  unfold missEven
  unfold T at hcard
  have h3 : n / 6 ≤ n / 3 := Nat.div_le_div_left (by norm_num) (by norm_num)
  omega

end Setup

/-- Lower bound for the even-connector lists. -/
lemma even_list_lower {n : ℕ} {A : Finset ℕ} {o o' : ℕ} (ho : Odd o) (ho' : Odd o') :
    #((Icc 1 (n / 2)).filter (fun k => Nat.Coprime k (o * o'))) ≤
      #(A.filter (fun u => Even u ∧ Nat.Coprime u o ∧ Nat.Coprime u o')) + missEven n A := by
  classical
  have hsub : (Icc 1 (n / 2)).filter (fun k => Nat.Coprime k (o * o')) ⊆
      ((Icc 1 (n / 2)).filter (fun k => Nat.Coprime k (o * o') ∧ 2 * k ∈ A)) ∪
        ((Icc 1 (n / 2)).filter (fun k => 2 * k ∉ A)) := by
    intro k hk
    simp only [mem_filter, mem_union] at hk ⊢
    by_cases h : 2 * k ∈ A
    · exact Or.inl ⟨hk.1, hk.2, h⟩
    · exact Or.inr ⟨hk.1, h⟩
  have hinj : #((Icc 1 (n / 2)).filter (fun k => Nat.Coprime k (o * o') ∧ 2 * k ∈ A)) ≤
      #(A.filter (fun u => Even u ∧ Nat.Coprime u o ∧ Nat.Coprime u o')) := by
    apply card_le_card_of_injOn (fun k => 2 * k)
    · intro k hk
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter] at hk ⊢
      obtain ⟨_, hc, hA⟩ := hk
      rw [Nat.coprime_mul_iff_right] at hc
      refine ⟨hA, even_two_mul k, ?_, ?_⟩
      · exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr ho, hc.1⟩
      · exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr ho', hc.2⟩
    · intro a _ b _ h; simp only at h; omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by unfold missEven; omega

/-- Lower bound for the arbitrary-connector lists. -/
lemma any_list_lower {n : ℕ} {A V : Finset ℕ} (hA : A ⊆ Icc 1 n) {o o' : ℕ} :
    #((Icc 1 n).filter (fun u => Nat.Coprime u (o * o'))) ≤
      #((A \ V).filter (fun u => Nat.Coprime u o ∧ Nat.Coprime u o')) + (n - #(A \ V)) := by
  classical
  have hsub : (Icc 1 n).filter (fun u => Nat.Coprime u (o * o')) ⊆
      ((A \ V).filter (fun u => Nat.Coprime u o ∧ Nat.Coprime u o')) ∪ (Icc 1 n \ (A \ V)) := by
    intro u hu
    simp only [mem_filter, mem_union, mem_sdiff] at hu ⊢
    rw [Nat.coprime_mul_iff_right] at hu
    by_cases h : u ∈ A ∧ u ∉ V
    · exact Or.inl ⟨h, hu.2⟩
    · exact Or.inr ⟨hu.1, h⟩
  have hAV : A \ V ⊆ Icc 1 n := (sdiff_subset).trans hA
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ = _ := by rw [card_sdiff_of_subset hAV, Nat.card_Icc, Nat.add_sub_cancel]

/-- If a gap list is short, one endpoint has small shifted weight. -/
lemma bad_endpoint {x : ℕ} (hx : 0 < x) {o o' : ℕ} (ho : Odd o) (ho' : Odd o') (hne : o ≠ o')
    {c : ℕ} (hc : #((Icc 1 x).filter (fun k => Nat.Coprime k (o * o'))) ≤ c) :
    Gt x o < Real.sqrt ((c : ℝ) / x) ∨ Gt x o' < Real.sqrt ((c : ℝ) / x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hs0 : 0 ≤ Real.sqrt ((c : ℝ) / x) := Real.sqrt_nonneg _
  have ho0 : o ≠ 0 := by rintro rfl; simp at ho
  have ho0' : o' ≠ 0 := by rintro rfl; simp at ho'
  have hprod : 1 < o * o' := by
    rcases ho with ⟨a, rfl⟩; rcases ho' with ⟨b, rfl⟩
    rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb
    · subst ha; subst hb; exact absurd rfl hne
    · subst ha; nlinarith
    · subst hb; nlinarith
    · nlinarith
  have hlt := pair_count_tilde o o' x ho0 ho0' hprod hx (le_trans hs0 h1) (le_trans hs0 h2)
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hsq : Real.sqrt ((c : ℝ) / x) * Real.sqrt ((c : ℝ) / x) = (c : ℝ) / x :=
    Real.mul_self_sqrt (by positivity)
  have hmul : Real.sqrt ((c : ℝ) / x) * Real.sqrt ((c : ℝ) / x) ≤ Gt x o * Gt x o' :=
    mul_le_mul h1 h2 hs0 (le_trans hs0 h1)
  rw [hsq] at hmul
  have : (c : ℝ) ≤ x * (Gt x o * Gt x o') := by
    rw [div_le_iff₀ hxr] at hmul; linarith
  have hc' : (#((Icc 1 x).filter (fun k => Nat.Coprime k (o * o'))) : ℝ) ≤ c := by exact_mod_cast hc
  linarith

/-! ### The skeleton -/

/-- Data of a skeleton: a weight-top set `Y0` of `h+1` odd elements of `A`, a coprime pair and an
antitone enumeration of `l-1` further elements. -/
structure Skeleton (n : ℕ) (A : Finset ℕ) (w : ℕ → ℝ) (b l : ℕ) where
  Y0 : Finset ℕ
  hY0 : Y0 ⊆ A.filter Odd
  hcard : #(A.filter Odd) = #Y0 + b
  htop : ∀ y ∈ A.filter Odd, y ∉ Y0 → ∀ y0 ∈ Y0, w y ≤ w y0
  o : ℕ → ℕ
  ho_mem : ∀ i ≤ l, o i ∈ Y0
  ho_inj : ∀ i ≤ l, ∀ j ≤ l, o i = o j → i = j
  hmid : ∀ i j, 1 ≤ i → i ≤ j → j + 1 ≤ l → w (o j) ≤ w (o i)
  hclose : Nat.Coprime (o l) (o 0)

theorem exists_skeleton {n : ℕ} (hn : 6 ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hcard : #A = T n + 1) (w : ℕ → ℝ) {l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ n / 6) :
    Nonempty (Skeleton n A w (missEven n A) l) := by
  classical
  set b := missEven n A
  set Y := A.filter Odd
  have hY := odd_part_card hA hcard
  obtain ⟨Y0, hY0, hc0, htop⟩ := exists_top w Y (n / 3 - n / 6 + 1) (by rw [hY]; omega)
  have hYodd : ∀ v ∈ Y0, Odd v ∧ 1 ≤ v ∧ v ≤ n := by
    intro v hv
    have := hY0 hv
    simp only [Y, mem_filter] at this
    have := mem_Icc.mp (hA this.1)
    exact ⟨(mem_filter.mp (hY0 hv)).2, this.1, this.2⟩
  obtain ⟨a, ha, a', ha', hne, hcop⟩ := coprime_pair (by omega) Y0 hYodd (by rw [hc0])
  set S := (Y0.erase a).erase a'
  have hS : #S = n / 3 - n / 6 - 1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne, ha'⟩), card_erase_of_mem ha, hc0]; omega
  have hlS : l - 1 ≤ #S := by
    rw [hS]
    have : n / 6 ≤ n / 3 - n / 6 := by omega
    omega
  obtain ⟨e, he1, he2, he3⟩ := exists_antitone_enum w S (l - 1) hlS
  let o : ℕ → ℕ := fun i => if i = 0 then a else if i < l then e (i - 1) else a'
  have hS_sub : ∀ x ∈ S, x ∈ Y0 ∧ x ≠ a ∧ x ≠ a' := by
    intro x hx
    simp only [S, mem_erase] at hx
    exact ⟨hx.2.2, hx.2.1, hx.1⟩
  refine ⟨{ Y0 := Y0, hY0 := hY0, hcard := by rw [hY, hc0], htop := htop, o := o,
            ho_mem := ?_, ho_inj := ?_, hmid := ?_, hclose := ?_ }⟩
  · intro i hi
    simp only [o]
    split_ifs with h0 h1
    · exact ha
    · exact (hS_sub _ (he1 _ (by omega))).1
    · exact ha'
  · intro i hi j hj hij
    simp only [o] at hij
    split_ifs at hij with h0 h1 h2 h3 h2 h3 h2 h3
    all_goals first
      | omega
      | exact absurd hij hne
      | exact absurd hij.symm hne
      | exact absurd hij.symm (hS_sub _ (he1 _ (by omega))).2.1
      | exact absurd hij (hS_sub _ (he1 _ (by omega))).2.1
      | exact absurd hij.symm (hS_sub _ (he1 _ (by omega))).2.2
      | exact absurd hij (hS_sub _ (he1 _ (by omega))).2.2
      | (have := he2 _ (by omega) _ (by omega) hij; omega)
  · intro i j hi hij hjl
    simp only [o]
    have h0 : i ≠ 0 := by omega
    have h0' : j ≠ 0 := by omega
    simp only [h0, h0', if_false, show i < l by omega, show j < l by omega, if_true]
    exact he3 _ _ (by omega) (by omega)
  · simp only [o, show l ≠ 0 by omega, if_false, lt_irrefl, if_true]
    exact hcop.symm

/-! ### Family G -/

/-- The Family-G certificate condition at `(b, l)`. -/
def CertG (n b l : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ l → (NG n (b + j - 1) - b) + (if 0 < NG n (b + j - 1) - b then 1 else 0) ≤ j - 1

theorem familyG {n : ℕ} (hn : 6 ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : #A = T n + 1)
    {l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ n / 6) (hcert : CertG n (missEven n A) l) :
    2 * l + 1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  classical
  set q := n / 2 with hq
  set b := missEven n A with hb
  set w : ℕ → ℝ := Gt q with hw
  obtain ⟨K⟩ := exists_skeleton hn hA hcard w hl1 hlm
  have hq0 : 0 < q := by omega
  have hodd : ∀ i ≤ l, Odd (K.o i) := fun i hi => (mem_filter.mp (K.hY0 (K.ho_mem i hi))).2
  have hoA : ∀ i ≤ l, K.o i ∈ A := fun i hi => (mem_filter.mp (K.hY0 (K.ho_mem i hi))).1
  -- the lists
  let t : Fin l → Finset ℕ := fun i =>
    A.filter (fun u => Even u ∧ Nat.Coprime u (K.o i) ∧ Nat.Coprime u (K.o (i + 1)))
  have hhall : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card (Fin l) →
      #(univ.filter (fun i => #(t i) ≤ j - 1)) ≤ j - 1 := by
    intro j hj1 hjl
    rw [Fintype.card_fin] at hjl
    set τ := Real.sqrt (((b + j - 1 : ℕ) : ℝ) / (q : ℝ)) with hτ
    -- short list ⇒ small endpoint
    have hshort : ∀ i : Fin l, #(t i) ≤ j - 1 → w (K.o i) < τ ∨ w (K.o (i + 1)) < τ := by
      intro i hi
      have hlow := even_list_lower (n := n) (A := A) (hodd i (by omega)) (hodd (i + 1) (by omega))
      replace hlow : _ ≤ _ + b := hlow
      have hti : #(A.filter (fun u => Even u ∧ Nat.Coprime u (K.o i) ∧ Nat.Coprime u (K.o (i + 1)))) ≤ j - 1 := hi
      have hne : K.o i ≠ K.o (i + 1) := fun h => by
        have := K.ho_inj i (by omega) (i + 1) (by omega) h; omega
      exact bad_endpoint (x := n / 2) (c := b + j - 1) (by omega) (hodd i (by omega)) (hodd (i + 1) (by omega)) hne (by omega)
    -- count
    set P : ℕ → Prop := fun i => w (K.o i) < τ ∨ w (K.o (i + 1)) < τ
    have h1 : #(univ.filter (fun i : Fin l => #(t i) ≤ j - 1)) ≤ #((range l).filter P) := by
      apply card_le_card_of_injOn (fun i : Fin l => (i : ℕ))
      · intro i hi
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_range] at hi ⊢
        exact ⟨i.isLt, hshort i hi⟩
      · intro a _ c _ h; exact Fin.ext h
    have h2 := bad_count w τ l K.o K.hmid
    set C := (range (l + 1)).filter (fun i => w (K.o i) < τ)
    have h3 : #C ≤ #(K.Y0.filter (fun v => w v < τ)) := by
      apply card_le_card_of_injOn K.o
      · intro i hi
        simp only [C, coe_filter, Set.mem_setOf_eq, mem_filter, mem_range] at hi ⊢
        exact ⟨K.ho_mem i (by omega), hi.2⟩
      · intro i hi i' hi' h
        simp only [C, coe_filter, Set.mem_setOf_eq, mem_range] at hi hi'
        exact K.ho_inj i (by omega) i' (by omega) h
    have hU : A.filter Odd ⊆ odds n := by
      intro v hv
      simp only [mem_filter] at hv
      simp only [odds, mem_filter]
      exact ⟨hA hv.1, hv.2⟩
    have h4 := tail_count w (odds n) (A.filter Odd) K.Y0 τ b hU K.hY0 K.hcard K.htop
    have hNG : #((odds n).filter (fun v => w v ≤ τ)) = NG n (b + j - 1) := by
      simp only [NG, hw, hτ, hq]
    rw [hNG] at h4
    have hc := hcert j hj1 hjl
    -- monotonicity of x ↦ x + [x > 0]
    set N := NG n (b + j - 1) - b
    have hmono : ∀ x y : ℕ, x ≤ y → x + (if 0 < x then 1 else 0) ≤ y + (if 0 < y then 1 else 0) := by
      intro x y hxy
      split_ifs <;> omega
    have := hmono _ _ (h3.trans h4)
    exact le_trans h1 (le_trans h2 (le_trans this hc))
  obtain ⟨f, hf_inj, hf_mem⟩ := ordered_hall t hhall
  let u : ℕ → ℕ := fun i => if h : i < l then f ⟨i, h⟩ else 0
  have hu : ∀ i (h : i < l), u i = f ⟨i, h⟩ := fun i h => by simp [u, h]
  have hu_prop : ∀ i < l, u i ∈ A ∧ Even (u i) ∧ Nat.Coprime (u i) (K.o i) ∧
      Nat.Coprime (u i) (K.o (i + 1)) := by
    intro i hi
    have := hf_mem ⟨i, hi⟩
    simp only [t, mem_filter] at this
    rw [hu i hi]; exact this
  refine template (A : Set ℕ) l hl1 K.o u (fun i hi => hoA i hi) (fun i hi => (hu_prop i hi).1)
    K.ho_inj ?_ ?_ K.hclose (fun i hi => (hu_prop i hi).2.2.1.symm) (fun i hi => (hu_prop i hi).2.2.2)
  · intro i hi j hj h
    rw [hu i hi, hu j hj] at h
    have := hf_inj h
    simpa using congrArg Fin.val this
  · intro i hi j hj h
    have h1 := hodd i hi
    have h2 := (hu_prop j hj).2.1
    rw [h] at h1
    exact (Nat.not_even_iff_odd.mpr h1) h2

/-! ### Family GA -/

/-- The Family-GA certificate condition at `(b, l)`. -/
def CertGA (n b l : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ l →
    (NA n (n - T n + l + j - 1) - b) + (if 0 < NA n (n - T n + l + j - 1) - b then 1 else 0) ≤ j - 1

theorem familyGA {n : ℕ} (hn : 6 ≤ n) {A : Finset ℕ} (hA : A ⊆ Icc 1 n) (hcard : #A = T n + 1)
    {l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ n / 6) (hcert : CertGA n (missEven n A) l) :
    2 * l + 1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  classical
  set b := missEven n A with hb
  set w : ℕ → ℝ := Gt n with hw
  obtain ⟨K⟩ := exists_skeleton hn hA hcard w hl1 hlm
  have hn0 : 0 < n := by omega
  have hodd : ∀ i ≤ l, Odd (K.o i) := fun i hi => (mem_filter.mp (K.hY0 (K.ho_mem i hi))).2
  have hoA : ∀ i ≤ l, K.o i ∈ A := fun i hi => (mem_filter.mp (K.hY0 (K.ho_mem i hi))).1
  set V := (range (l + 1)).image K.o with hV
  have hVcard : #V = l + 1 := by
    rw [hV, card_image_of_injOn]
    · simp
    · intro i hi j hj h
      simp only [coe_range, Set.mem_Iio] at hi hj
      exact K.ho_inj i (by omega) j (by omega) h
  have hVA : V ⊆ A := by
    intro v hv
    simp only [hV, mem_image, mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact hoA i (by omega)
  have hAV : #(A \ V) = T n - l := by
    rw [card_sdiff_of_subset hVA, hcard, hVcard]; omega
  let t : Fin l → Finset ℕ := fun i =>
    (A \ V).filter (fun u => Nat.Coprime u (K.o i) ∧ Nat.Coprime u (K.o (i + 1)))
  have hTn : T n ≤ n := by unfold T; omega
  have hTl : l ≤ T n := by unfold T; omega
  have hhall : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card (Fin l) →
      #(univ.filter (fun i => #(t i) ≤ j - 1)) ≤ j - 1 := by
    intro j hj1 hjl
    rw [Fintype.card_fin] at hjl
    set τ := Real.sqrt (((n - T n + l + j - 1 : ℕ) : ℝ) / (n : ℝ)) with hτ
    have hshort : ∀ i : Fin l, #(t i) ≤ j - 1 → w (K.o i) < τ ∨ w (K.o (i + 1)) < τ := by
      intro i hi
      have hlow := any_list_lower (V := V) hA (o := K.o i) (o' := K.o (i + 1))
      rw [hAV] at hlow
      have hne : K.o i ≠ K.o (i + 1) := fun h => by
        have := K.ho_inj i (by omega) (i + 1) (by omega) h; omega
      have hti : #((A \ V).filter (fun u => Nat.Coprime u (K.o i) ∧ Nat.Coprime u (K.o (i + 1)))) ≤ j - 1 := hi
      exact bad_endpoint (c := n - T n + l + j - 1) hn0 (hodd i (by omega)) (hodd (i + 1) (by omega)) hne (by omega)
    set P : ℕ → Prop := fun i => w (K.o i) < τ ∨ w (K.o (i + 1)) < τ
    have h1 : #(univ.filter (fun i : Fin l => #(t i) ≤ j - 1)) ≤ #((range l).filter P) := by
      apply card_le_card_of_injOn (fun i : Fin l => (i : ℕ))
      · intro i hi
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and, mem_range] at hi ⊢
        exact ⟨i.isLt, hshort i hi⟩
      · intro a _ c _ h; exact Fin.ext h
    have h2 := bad_count w τ l K.o K.hmid
    set C := (range (l + 1)).filter (fun i => w (K.o i) < τ)
    have h3 : #C ≤ #(K.Y0.filter (fun v => w v < τ)) := by
      apply card_le_card_of_injOn K.o
      · intro i hi
        simp only [C, coe_filter, Set.mem_setOf_eq, mem_filter, mem_range] at hi ⊢
        exact ⟨K.ho_mem i (by omega), hi.2⟩
      · intro i hi i' hi' h
        simp only [C, coe_filter, Set.mem_setOf_eq, mem_range] at hi hi'
        exact K.ho_inj i (by omega) i' (by omega) h
    have hU : A.filter Odd ⊆ odds n := by
      intro v hv
      simp only [mem_filter] at hv
      simp only [odds, mem_filter]
      exact ⟨hA hv.1, hv.2⟩
    have h4 := tail_count w (odds n) (A.filter Odd) K.Y0 τ b hU K.hY0 K.hcard K.htop
    have hNA : #((odds n).filter (fun v => w v ≤ τ)) = NA n (n - T n + l + j - 1) := by
      simp only [NA, hw, hτ]
    rw [hNA] at h4
    have hc := hcert j hj1 hjl
    have hmono : ∀ x y : ℕ, x ≤ y → x + (if 0 < x then 1 else 0) ≤ y + (if 0 < y then 1 else 0) := by
      intro x y hxy
      split_ifs <;> omega
    have := hmono _ _ (h3.trans h4)
    exact le_trans h1 (le_trans h2 (le_trans this hc))
  obtain ⟨f, hf_inj, hf_mem⟩ := ordered_hall t hhall
  let u : ℕ → ℕ := fun i => if h : i < l then f ⟨i, h⟩ else 0
  have hu : ∀ i (h : i < l), u i = f ⟨i, h⟩ := fun i h => by simp [u, h]
  have hu_prop : ∀ i < l, (u i ∈ A ∧ u i ∉ V) ∧ Nat.Coprime (u i) (K.o i) ∧
      Nat.Coprime (u i) (K.o (i + 1)) := by
    intro i hi
    have := hf_mem ⟨i, hi⟩
    simp only [t, mem_filter, mem_sdiff] at this
    rw [hu i hi]; exact this
  refine template (A : Set ℕ) l hl1 K.o u (fun i hi => hoA i hi) (fun i hi => (hu_prop i hi).1.1)
    K.ho_inj ?_ ?_ K.hclose (fun i hi => (hu_prop i hi).2.1.symm) (fun i hi => (hu_prop i hi).2.2)
  · intro i hi j hj h
    rw [hu i hi, hu j hj] at h
    have := hf_inj h
    simpa using congrArg Fin.val this
  · intro i hi j hj h
    apply (hu_prop j hj).1.2
    rw [← h, hV, mem_image]
    exact ⟨i, mem_range.mpr (by omega), rfl⟩

end Erdos883Proof
