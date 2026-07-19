#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

lake build TwistedYetter.Kirby.EGNOModularFourManifoldInvariant >/dev/null

./scripts/lean_egno_modular_kirby_moves_mutation_tests.sh

mutations=(
  "lean/Mutations/GenericTaggedMoveInEGNOAssembly.lean"
  "lean/Mutations/ReboundPackageInEGNOAssembly.lean"
  "lean/Mutations/GeneralizedSlideAsOrdinary.lean"
  "lean/Mutations/OrdinarySlideAsGeneralized.lean"
  "lean/Mutations/FreeComponentWeightInEGNOAssembly.lean"
  "lean/Mutations/EventwiseLabelWithoutGlobalResolver.lean"
  "lean/Mutations/NormalizedEqualityAsLocalMoveCompiler.lean"
  "lean/Mutations/MissingMoveFamiliesInLocalCompiler.lean"
  "lean/Mutations/MalformedInvariantAssemblyHash.lean"
  "lean/Mutations/ReboundPresentationCompilerPackage.lean"
)

expected_diagnostics=(
  "Unknown constant"
  "Type mismatch"
  "Type mismatch"
  "Type mismatch"
  "Tactic \`rfl\` failed"
  "Fields missing"
  "Type mismatch"
  "Fields missing"
  "Tactic \`decide\` failed"
  "Type mismatch"
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-four-manifold-mutation.XXXXXX")"
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
