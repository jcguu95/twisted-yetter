#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

lake build TwistedYetter.Kirby.EGNOModularKirbyMoves >/dev/null

./scripts/lean_egno_kirby_color_mutation_tests.sh

mutations=(
  "lean/Mutations/SingletonFormalKirbyColorSliding.lean"
  "lean/Mutations/MissingLabelIndexedEncirclingFamily.lean"
  "lean/Mutations/FreeModularGlobalDimension.lean"
  "lean/Mutations/WrongModularTransparentDimension.lean"
  "lean/Mutations/MissingUnitQuantumDimensionCertificate.lean"
  "lean/Mutations/WrongRibbonSnapshotInModularPackage.lean"
  "lean/Mutations/UnboundOrdinarySlidingInModularPackage.lean"
  "lean/Mutations/MalformedModularPackageHash.lean"
)

expected_diagnostics=(
  "Application type mismatch"
  "Type mismatch"
  "Tactic \`rfl\` failed"
  "Tactic \`rfl\` failed"
  "Fields missing"
  "Type mismatch"
  "Type mismatch"
  "Tactic \`decide\` failed"
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-modular-kirby-mutation.XXXXXX")"
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
