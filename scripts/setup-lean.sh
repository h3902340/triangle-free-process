#!/usr/bin/env bash
# Install elan if needed, fetch the mathlib cache, and build the verified core.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if ! command -v lake >/dev/null 2>&1; then
  if [[ ! -x "${HOME}/.elan/bin/lake" ]]; then
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
      | sh -s -- -y --default-toolchain none
  fi
  # shellcheck disable=SC1091
  source "${HOME}/.elan/env"
fi

cd "${ROOT}/lean"
lake exe cache get
lake build
