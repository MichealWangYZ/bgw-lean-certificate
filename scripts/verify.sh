#!/usr/bin/env bash
# Full gate by default (~5 h cold, ~1 h warm; required before any merge).
# `scripts/verify.sh --gate scientific` runs only the numeric/algebraic tests;
# `--gate workflow` runs only the provenance contracts. `--gate fast` is the
# routine-change gate (< 10 min warm): registry check, default-library build,
# memoized audit without GWKernelData, and the tests covering the change.
# See scripts/gates.py for the criteria.
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$PROJECT_ROOT"
python3 scripts/verify.py "$@"
