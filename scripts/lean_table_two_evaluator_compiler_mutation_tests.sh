#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS=1 ./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/TableTwoEvaluatorCompiler.lean \
  lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/DirectPrescriptionAsTargetInput.lean"
  "lean/Mutations/ArbitraryLocalStepAsCompiler.lean"
  "lean/Mutations/MissingTwoThreeDeathCompilerCase.lean"
  "lean/Mutations/WrongEvaluatorCompilerCaseResult.lean"
)

expected_diagnostics=(
  '`prescription` is not a field of structure `FourManifoldInvariantInputs`'
  '`localStep` is not a field of structure `TableTwoEvaluatorCompiler`'
  'Fields missing: `twoThreeDeath`'
  'TableTwoMove.twoOverOne'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-compiler-mutation.XXXXXX")"
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
