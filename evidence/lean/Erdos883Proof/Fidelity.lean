import FormalConjectures.ErdosProblems.«883»
import Erdos883Proof.Statement

/-!
# Statement correspondence with formal-conjectures `Erdos883.erdos_883.parts.i`

The graph used in this development is definitionally the one of the formal statement, and the right-hand
side of `erdos_883.parts.i` follows from the per-n statement `Erdos883Proof.Stmt n` for all `n ≥ 6`.
`erdos_883_parts_i_linked` states this against the upstream constant's own type (`type_of%`).
-/

namespace Erdos883Proof

theorem coprimeGraph_eq : Erdos883.coprimeGraph = Erdos883Proof.coprimeGraph := rfl

/-- The proposition on the right of `erdos_883.parts.i`, verbatim. -/
def ErdosRHS : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ),
    A ⊆ Finset.Icc 1 n →
    n / 2 + n / 3 - n / 6 < A.card →
    ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
      l ∈ (Erdos883.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

theorem erdosRHS_of_stmt (h : ∀ n, 6 ≤ n → Stmt n) : ErdosRHS :=
  erdos883_i_of h

/-- With answer `True`, the formal statement is equivalent to `ErdosRHS`; so it follows from `Stmt n`
for every `n ≥ 6`. -/
theorem erdos_883_parts_i_of_stmt (h : ∀ n, 6 ≤ n → Stmt n) : True ↔ ErdosRHS :=
  ⟨fun _ => erdosRHS_of_stmt h, fun _ => trivial⟩

/-- Statement link checked by Lean itself: the conclusion is the elaborated type of the upstream
constant `Erdos883.erdos_883.parts.i` (formal-conjectures' default elaborates `answer(sorry)` in `Prop`
to `True`), not a re-typed copy. Only the constant's type is used, never its (`sorry`) proof, so its
axiom report in `Axioms.lean` stays free of `sorryAx`. -/
theorem erdos_883_parts_i_linked (h : ∀ n, 6 ≤ n → Stmt n) :
    type_of% Erdos883.erdos_883.parts.i :=
  erdos_883_parts_i_of_stmt h

end Erdos883Proof
