#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS=1 ./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/PresentationExecutionTrace.lean \
  lean/TwistedYetter/Kirby/KirbyCompleteness.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/EvaluatorEqualityInsideKirbyCompleteness.lean"
  "lean/Mutations/MissingKirbyCompletenessCaveat.lean"
  "lean/Mutations/ZeroOneAsTableTwoMove.lean"
  "lean/Mutations/HandwrittenMovieTargetCharacter.lean"
  "lean/Mutations/MissingUniqueFourHandle.lean"
  "lean/Mutations/ArbitraryTopologyMoveInjection.lean"
  "lean/Mutations/MissingInducedH2ChainWitness.lean"
  "lean/Mutations/MissingSpecialManifoldBinding.lean"
  "lean/Mutations/MissingLocalTopologyWitness.lean"
  "lean/Mutations/MissingPresentationExecutionTrace.lean"
)

expected_diagnostics=(
  '`evaluatorEquality` is not a field of structure `TableTwoLinkCompleteness`'
  'Fields missing: `source_scope_caveat`'
  'Unknown constant `TwistedYetter.Kirby.KirbyCompleteness.TableTwoMove.zeroOneBirth`'
  '`targetCharacter` is not a field of structure `MarkedH2Transport`'
  'Fields missing: `uniqueFourHandle`'
  'Unknown constant `TwistedYetter.Kirby.KirbyCompleteness.TableTwoMove.fromArbitraryRelation`'
  '`homologyEquiv` is not a field of structure `MarkedH2Transport`'
  'Fields missing: `provenance`'
  'Fields missing: `recipe`'
  'Fields missing: `execution`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-r10-mutation.XXXXXX")"
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
