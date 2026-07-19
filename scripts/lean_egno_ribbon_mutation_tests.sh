#!/usr/bin/env bash
set -euo pipefail

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/EGNORibbon.lean >/dev/null

mutations=(
  "lean/Mutations/MissingPivotalMonoidality.lean"
  "lean/Mutations/MissingSphericalDimensionDual.lean"
  "lean/Mutations/MissingBalancingTensor.lean"
  "lean/Mutations/MissingRibbonDual.lean"
)

expected_diagnostics=(
  'Fields missing: `monoidal`'
  'Fields missing: `dimension_dual`'
  'Fields missing: `tensor`'
  'Fields missing: `dual`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-mutation.XXXXXX")"
  if ./scripts/lean_local_check.sh "${mutation}" >"${output}" 2>&1; then
    printf 'Mutation unexpectedly compiled: %s\n' "${mutation}" >&2
    rm -f "${output}"
    exit 1
  fi
  if ! rg -Fq "${expected_diagnostic}" "${output}"; then
    printf 'Mutation failed for the wrong reason: %s\n' "${mutation}" >&2
    printf 'Expected diagnostic: %s\n' "${expected_diagnostic}" >&2
    cat "${output}" >&2
    rm -f "${output}"
    exit 1
  fi
  printf 'PASS expected rejection: %s [diagnostic: %s]\n' \
    "${mutation}" "${expected_diagnostic}"
  rm -f "${output}"
done
