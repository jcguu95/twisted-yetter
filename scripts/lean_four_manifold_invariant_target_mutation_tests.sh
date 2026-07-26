#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/CategoricalPresentationCompiler.lean \
  lean/TwistedYetter/Kirby/SourceBoundTableTwoEvaluatorCompiler.lean \
  lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean \
  lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/PromoteFourManifoldInvariantTarget.lean"
  "lean/Mutations/DropFourManifoldInvariantTargetCondition.lean"
  "lean/Mutations/RequireCraneYetterIdentificationForTarget.lean"
  "lean/Mutations/ArbitraryEvaluatorCompilerAsTargetInput.lean"
  "lean/Mutations/DirectGeometricH2CompilerAsTargetInput.lean"
)

diagnostics=(
  'Tactic `rfl` failed'
  'Tactic `rfl` failed'
  'Unknown constant `TwistedYetter.Kirby.FourManifoldInvariantTarget.TargetCondition.craneYetterIdentification`'
  'TableTwoEvaluatorCompiler categoryData H2'
  '`markedH2Compiler` is not a field of structure `FourManifoldInvariantInputs`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  diagnostic="${diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-4mf-target-mutation.XXXXXX")"
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
  if ! rg -Fq "${diagnostic}" "${output}"; then
    printf 'Mutation failed for the wrong reason: %s\n' "${mutation}" >&2
    printf 'Expected diagnostic: %s\n' "${diagnostic}" >&2
    cat "${output}" >&2
    rm -f "${output}"
    exit 1
  fi
  printf 'PASS expected rejection: %s [diagnostic: %s]\n' \
    "${mutation}" "${diagnostic}"
  rm -f "${output}"
done
