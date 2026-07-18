#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS=1 ./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/ComputationArtifactImporter.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/DirtyArtifactAsExactR12.lean"
  "lean/Mutations/RoundedArtifactAsExactR12.lean"
  "lean/Mutations/MissingR11BindingR12.lean"
  "lean/Mutations/MissingEvaluatorClosureR12.lean"
  "lean/Mutations/IncompleteDistributionR12.lean"
  "lean/Mutations/InconclusiveArtifactAsExactR12.lean"
  "lean/Mutations/MutableAliasArtifactAsExactR12.lean"
  "lean/Mutations/StructuralAggregatePromotionR12.lean"
  "lean/Mutations/Figure21ExactValueProjectionR12.lean"
  "lean/Mutations/Figure21ExactDispositionR12.lean"
)

expected_diagnostics=(
  "has type"
  "has type"
  'Fields missing: `r11_binding_witness`'
  'Fields missing: `evaluatorClosureHash`'
  "has type"
  "has type"
  "has type"
  "Unknown constant"
  "Invalid field"
  "has type"
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-r12-mutation.XXXXXX")"
  if LEAN_NUM_THREADS=1 ./scripts/lean_local_check.sh \
      "${mutation}" >"${output}" 2>&1; then
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
