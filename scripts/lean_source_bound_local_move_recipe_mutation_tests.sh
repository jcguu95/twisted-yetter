#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipe.lean \
  lean/TwistedYetter/Kirby/KirbyCompleteness.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/ArbitraryPropAsLocalMoveRecipe.lean"
  "lean/Mutations/FinalEqualityInsideLocalMoveRecipe.lean"
  "lean/Mutations/MissingSourceBoundRecipeCase.lean"
  "lean/Mutations/WrongKindLocalMoveRecipe.lean"
  "lean/Mutations/SwappedPresentationLocalMoveRecipe.lean"
  "lean/Mutations/SplitGraphicalChainRecipeIdentity.lean"
  "lean/Mutations/MissingGraphicalProgramInLocalRecipe.lean"
  "lean/Mutations/WrongGraphicalProgramKind.lean"
)

diagnostics=(
  '`locallyRealizesTableTwoMove` is not a field of structure `TableTwoMoveMetadata`'
  '`normalizedEvaluationEquality` is not a field of structure `SourceBoundRecipe`'
  'Tactic `rfl` failed'
  'RecipeKind.twoThreeDeath'
  'Type mismatch'
  '`graphicalRecipeId` is not a field of structure `SourceBoundRecipe`'
  'Fields missing: `graphicalProgram`'
  'Type mismatch'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  diagnostic="${diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-recipe-mutation.XXXXXX")"
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
