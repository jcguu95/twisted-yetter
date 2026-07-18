#!/usr/bin/env bash
set -euo pipefail

./scripts/lean_local_check.sh lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/ArbitraryNormalizedEqualityAsCancellation.lean"
  "lean/Mutations/MissingCancellationKillingIdentity.lean"
  "lean/Mutations/MissingTransparentTwistWitness.lean"
  "lean/Mutations/MissingPivotalCancellationDimension.lean"
  "lean/Mutations/HandwrittenCancellationCharacter.lean"
)

expected_diagnostics=(
  'Unknown constant `TwistedYetter.Kirby.KirbyCancellation.AdmittedCancellation.fromEquality`'
  'Fields missing: `killing_identity`'
  'Fields missing: `transparent_twist_witness`'
  'Fields missing: `pivotal_dimension_preserved`'
  '`afterCharacter` is not a field of structure `CancellationHomologyTransport`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-r9-mutation.XXXXXX")"
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
