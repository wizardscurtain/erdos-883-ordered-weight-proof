# Third-party notices

No blanket license is assigned to Cecil Jentges' project by this package. This file identifies upstream material and dependencies; it preserves existing rights rather than relicensing the mathematical work.

## Copied formal statement

`lean/Erdos883Proof/FidelityMin.lean` reproduces statement material from [formal-conjectures, Erdős 883](https://github.com/google-deepmind/formal-conjectures/blob/1646ca16/FormalConjectures/ErdosProblems/883.lean), at full commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`. The source attribution is “Copyright 2026 The Formal Conjectures Authors.”

The upstream [Apache License 2.0](https://github.com/google-deepmind/formal-conjectures/blob/1646ca16/LICENSE) is preserved verbatim at `third_party/formal-conjectures/LICENSE`. The historical adaptation substitutes `True` for `answer(sorry)` and uses a local namespace; the public derivative restores attribution without changing the declarations.

The remaining Lean imports refer to separately obtained Mathlib and formal-conjectures installations. Those imported libraries are not bundled in this package.

## Separately installed checkers and libraries

The Python tools import NumPy, mpmath, and python-sat. Their installed distributions and dependencies retain their own notices; none of their source trees, binaries, or package installations is copied into this evidence directory.

The optional SAT verification binary is built from drat-trim commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. Its [license and copyright notices](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/LICENSE) remain with the separate checkout; the checker source and binary are not bundled here.
