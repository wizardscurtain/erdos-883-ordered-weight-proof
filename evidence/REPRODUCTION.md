# Evidence setup guide

Use this guide only for setup. The separate `VALIDATION_PROTOCOL.md` specifies what each command tests and what its result does not establish.

## Python environment

Work from the repository root, with Python 3.10 or newer and assertions enabled. Do not use `-O`, `-OO`, or `PYTHONOPTIMIZE` with historical mathematical checks.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r evidence/hall_tail_20261010/requirements.txt
export PYTHONDONTWRITEBYTECODE=1
```

The historical requirements are retained as supplied, including their exact version pins. A later validation environment must record its actual versions separately; it must not describe itself as identical to the historical environment if it differs.

The standard-library-only integrity checker can run before NumPy, mpmath, or python-sat is installed. Mathematical modes import their additional dependencies only when needed.

## Optional LRAT checker

Deep SAT replay needs the original checker revision `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. Download and build it in a directory outside `evidence/`; no proof driver downloads or installs it automatically.

```sh
git clone https://github.com/marijnheule/drat-trim.git ../erdos883-drat-trim
git -C ../erdos883-drat-trim checkout --detach 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C ../erdos883-drat-trim lrat-check
export DRAT_TOOLS="$(cd ../erdos883-drat-trim && pwd)"
```

Preserve the checker's own notices in that checkout. Its upstream license is available at the [pinned license page](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/LICENSE).

## Output isolation

Place generated outputs outside `evidence/`, for example under `validation_out/` at the repository root. The public manifest rejects unexpected files, including bytecode caches, so `-B` or `PYTHONDONTWRITEBYTECODE=1` is intentional.

Keep the original certificate bytes unchanged. New receipts must be separately dated and must name the exact public version and actual commands.

## Lean

The retained Lean fragments are conditional historical reductions. They are not a complete build environment, do not discharge all finite and analytic hypotheses, and are not part of the mathematical-only filing requirement.
