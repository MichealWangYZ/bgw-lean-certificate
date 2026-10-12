#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$PROJECT_ROOT"
mkdir -p .tools
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl -fsSL --retry 3 https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o .tools/elan-init.sh
  sh .tools/elan-init.sh -y --no-modify-path --default-toolchain none
fi
lean --version
if [[ ! -f lake-manifest.json ]]; then
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
fi
lake exe cache get

