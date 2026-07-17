#!/usr/bin/env bash
set -euo pipefail

./scripts/lean_local_check.sh lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/InvalidComposition.lean"
  "lean/Mutations/InvalidDualCap.lean"
  "lean/Mutations/MissingMoveProof.lean"
)

for mutation in "${mutations[@]}"; do
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-lean-mutation.XXXXXX")"
  if ./scripts/lean_local_check.sh "${mutation}" >"${output}" 2>&1; then
    printf 'Mutation unexpectedly compiled: %s\n' "${mutation}" >&2
    rm -f "${output}"
    exit 1
  fi
  if ! rg -q 'error(:|\()' "${output}"; then
    printf 'Mutation failed without a Lean error: %s\n' "${mutation}" >&2
    cat "${output}" >&2
    rm -f "${output}"
    exit 1
  fi
  printf 'PASS expected rejection: %s\n' "${mutation}"
  rm -f "${output}"
done
