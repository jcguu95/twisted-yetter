#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/IntegralCharacterKirbyColorCompiler.lean >/dev/null

mutations=(
  "lean/Mutations/GenericCategoryBoundAsIntegralCharacterCompiler.lean"
  "lean/Mutations/MissingIntegralCycleClassSoundness.lean"
  "lean/Mutations/MissingTensorAutomorphismLaw.lean"
)

diagnostics=(
  "Type mismatch"
  'Fields missing: `cycle_class_sound`'
  'Fields missing: `tensor_hom`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  diagnostic="${diagnostics[${index}]}"
  output="$(mktemp \
    "${TMPDIR:-/tmp}/twisted-yetter-integral-character-mutation.XXXXXX")"
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
