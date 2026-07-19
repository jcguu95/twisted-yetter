#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}" \
  lake build TwistedYetter.Fusion.EGNOPairingCompatibility >/dev/null

./scripts/lean_egno_fusion_category_mutation_tests.sh

mutations=(
  "lean/Mutations/MissingSphericalMateTraceLaw.lean"
  "lean/Mutations/MissingPivotalFunctorTraceLaw.lean"
)

expected_diagnostics=(
  "Application type mismatch"
  "Application type mismatch"
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-trace-pairing-mutation.XXXXXX")"
  if ./scripts/lean_local_check.sh "${mutation}" >"${output}" 2>&1; then
    printf 'Mutation unexpectedly compiled: %s\n' "${mutation}" >&2
    rm -f "${output}"
    exit 1
  fi
  if ! rg -Fq "${expected_diagnostic}" "${output}"; then
    printf 'Mutation failed for the wrong reason: %s\n' "${mutation}" >&2
    printf 'Expected diagnostic fragment: %s\n' "${expected_diagnostic}" >&2
    cat "${output}" >&2
    rm -f "${output}"
    exit 1
  fi
  printf 'PASS expected rejection: %s [diagnostic contains: %s]\n' \
    "${mutation}" "${expected_diagnostic}"
  rm -f "${output}"
done
