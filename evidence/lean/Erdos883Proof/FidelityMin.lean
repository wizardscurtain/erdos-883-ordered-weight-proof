/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Copied statement source: formal-conjectures commit
1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89,
FormalConjectures/ErdosProblems/883.lean.
Historical adaptation replaces answer(sorry) with True and changes the namespace.
Public derivative notice restored 12 October 2026; declarations are unchanged.
-/
import Erdos883Proof.Statement

/-!
# Statement correspondence without importing all of Mathlib

The text below reproduces `Erdos883.coprimeGraph` and the proposition of `Erdos883.erdos_883.parts.i`
(google-deepmind/formal-conjectures@1646ca16, `FormalConjectures/ErdosProblems/883.lean`) verbatim, with
`answer(sorry)` replaced by `True`; `SimpleGraph.oddCycleLengths` is the definition imported from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference`, exactly as in the original file.
`Fidelity.lean` performs the same check against the imported original (it needs all of Mathlib).
-/

namespace Erdos883Copy

/-- Verbatim copy of `Erdos883.coprimeGraph`. -/
def coprimeGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel Nat.Coprime

/-- Verbatim copy of the statement of `erdos_883.parts.i` with `answer(sorry) := True`. -/
def erdos_883_parts_i_statement : Prop :=
  True ↔
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

theorem coprimeGraph_eq : coprimeGraph = Erdos883Proof.coprimeGraph := rfl

/-- The formal statement follows from the per-n statement for every `n ≥ 6`. -/
theorem erdos_883_parts_i_of_stmt (h : ∀ n, 6 ≤ n → Erdos883Proof.Stmt n) :
    erdos_883_parts_i_statement :=
  ⟨fun _ => Erdos883Proof.erdos883_i_of h, fun _ => trivial⟩

end Erdos883Copy
