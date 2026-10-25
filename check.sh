#!/usr/bin/env bash
# Rebuild and check everything: the Lean formalization and the numerical checks.
#
#   ./check.sh            Lean build + axiom audit + every numerical check (about 30 min of numerics on 2 cores)
#   ./check.sh --quick    the same, skipping the three slow end-to-end runs (thmA_numeric, a_minus_pred, arith_s4)
#   ./check.sh --lean     Lean only
#   ./check.sh --python   numerical checks only (add --quick to skip the slow ones)
#
# Needs: elan (https://github.com/leanprover/elan), Python >= 3.10 with venv, git, curl.
# Output: build/logs/ (one log per check, plus lean_build.log and lean_axioms.log).
set -euo pipefail
cd "$(dirname "$0")"
ROOT="$PWD"
mkdir -p build/logs

DO_LEAN=1; DO_PY=1; QUICK=""
for arg in "$@"; do
  case "$arg" in
    --lean)   DO_PY=0 ;;
    --python) DO_LEAN=0 ;;
    --quick)  QUICK="--quick" ;;
    -h|--help) sed -n '2,9p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

if [[ $DO_LEAN == 1 ]]; then
  echo "== Lean: $(cat lean/lean-toolchain), Mathlib $(python3 -c 'import json;print([p["rev"] for p in json.load(open("lean/lake-manifest.json"))["packages"] if p["name"]=="mathlib"][0])')"
  command -v lake >/dev/null || { echo "lake not found: install elan from https://github.com/leanprover/elan" >&2; exit 1; }
  cd lean
  # Prebuilt Mathlib for the pinned commit; if the download is unavailable, `lake build` compiles Mathlib from source (hours).
  lake exe cache get || echo "   (Mathlib cache unavailable; building Mathlib from source)"
  lake build 2>&1 | tee "$ROOT/build/logs/lean_build.log"
  echo "== Lean: re-elaborating LocalDensities.lean and auditing axioms"
  lake env lean PrimeSquareMurmurations/LocalDensities.lean 2>&1 | tee "$ROOT/build/logs/lean_axioms.log"
  cd "$ROOT"
  python3 scripts/check_lean_output.py build/logs/lean_axioms.log
fi

if [[ $DO_PY == 1 ]]; then
  echo "== Python: environment"
  if [[ ! -x .venv/bin/python ]]; then python3 -m venv .venv; fi
  .venv/bin/python -m pip install -q --upgrade pip
  .venv/bin/python -m pip install -q -r requirements.txt
  echo "== Python: numerical checks"
  PATH="$ROOT/.venv/bin:$PATH" python scripts/run_checks.py $QUICK
fi

echo "== All checks passed."
