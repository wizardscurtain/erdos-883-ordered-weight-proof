#!/bin/sh
# Read-only public verification. Install dependencies explicitly; no hidden network use.
# The original frozen replay driver is not modified by this derivative.
set -eu
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
export PYTHONDONTWRITEBYTECODE=1
MODE="${1:---quick}"
case "$MODE" in
  --quick|--deep|--scanners) ;;
  *) echo "usage: sh replay.sh [--quick|--deep|--scanners]" >&2; exit 2 ;;
esac
"$PYTHON" -B ../public_integrity.py
case "$MODE" in
  --quick) "$PYTHON" -B code/coverage_ledger2.py --require-second-source ;;
  --deep)
    : "${DRAT_TOOLS:?Set DRAT_TOOLS to a locally built pinned drat-trim directory}"
    test -x "$DRAT_TOOLS/lrat-check"
    "$PYTHON" -B code/coverage_ledger2.py --deep --require-second-source
    ;;
  --scanners)
    : "${REPLAY_OUT:?Set REPLAY_OUT to an absolute directory outside evidence/}"
    : "${JOBS:=2}"
    "$PYTHON" -B -c 'from pathlib import Path; import sys; p=Path(sys.argv[1]); root=Path("..").resolve(); sys.exit("REPLAY_OUT must be absolute and outside evidence/") if not p.is_absolute() or p.resolve().is_relative_to(root) else None' "$REPLAY_OUT"
    "$PYTHON" -B code/replay_scanners.py --jobs "$JOBS" --out "$REPLAY_OUT"
    "$PYTHON" -B code/coverage_ledger2.py --scanners "$REPLAY_OUT/SCANNER_REPLAY.json" --require-second-source
    ;;
esac
