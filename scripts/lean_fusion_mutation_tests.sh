#!/usr/bin/env bash
set -euo pipefail

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/PairingTransport.lean >/dev/null

mutations=(
  "lean/Mutations/MissingDualBasisProof.lean"
  "lean/Mutations/MissingPairingPreservation.lean"
  "lean/Mutations/WrongTransportedDualIndex.lean"
)

expected_diagnostics=(
  'Fields missing: `dual_eq`'
  'Fields missing: `preserves_pairing`'
  'if i = j then 1 else 0'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-lean-fusion-mutation.XXXXXX")"
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
