#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}" \
  lake build TwistedYetter.Fusion.EGNOCanonicalSpherical >/dev/null

./scripts/lean_egno_canonical_pivotal_mutation_tests.sh

mutations=(
  "lean/Mutations/BalancedTwistIsNotSpherical.lean"
  "lean/Mutations/WrongRibbonLoopMirror.lean"
  "lean/Mutations/WrongRibbonDualInverseTwist.lean"
)

expected_diagnostics=(
  "Application type mismatch"
  "rfl"
  "rfl"
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-spherical-mutation.XXXXXX")"
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
