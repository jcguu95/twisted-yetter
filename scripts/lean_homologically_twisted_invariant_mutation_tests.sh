#!/usr/bin/env bash
set -euo pipefail

LEAN_NUM_THREADS=1 ./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/ArbitraryNormalizedEqualityAsR11Step.lean"
  "lean/Mutations/DirectFinalInvariantInjection.lean"
  "lean/Mutations/CraneYetterIdentificationInjection.lean"
  "lean/Mutations/HandwrittenR11TargetAlpha.lean"
  "lean/Mutations/MissingR11SingleSnapshotCoherence.lean"
  "lean/Mutations/MissingR11DecorationWitness.lean"
  "lean/Mutations/MissingR11LocalBindingHashes.lean"
  "lean/Mutations/WrongR11OrdinarySlideKind.lean"
  "lean/Mutations/MissingR11MarkedTransportSound.lean"
  "lean/Mutations/MissingR11SourceScopeCaveat.lean"
)

expected_diagnostics=(
  'Unknown identifier `TwistedYetter.Kirby.HomologicallyTwistedInvariant.r11StepFromNormalizedEquality`'
  'Unknown constant `TwistedYetter.Kirby.HomologicallyTwistedInvariant.MarkedPairPresentationSystem.finalInvariant`'
  'Unknown identifier `TwistedYetter.Kirby.HomologicallyTwistedInvariant.craneYetterIdentification`'
  'Unknown identifier `TwistedYetter.Kirby.HomologicallyTwistedInvariant.handwrittenTargetAlpha`'
  'Fields missing: `single_snapshot_witness`'
  'Fields missing: `decoration_representation_witness`'
  'Fields missing: `moveId`, `move_id_sound`, `sourcePresentationHash`, `source_hash_sound`, `targetPresentationHash`, `target_hash_sound`'
  'SlideKind.oneOverOne'
  'Fields missing: `marked_transport_sound`'
  'Fields missing: `sourceScopeCaveat`'
)

for index in "${!mutations[@]}"; do
  mutation="${mutations[${index}]}"
  expected_diagnostic="${expected_diagnostics[${index}]}"
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-r11-mutation.XXXXXX")"
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
