#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/FinalFormalizationPackage.lean \
  lean/TwistedYetter.lean >/dev/null

mutations=(
  "lean/Mutations/MissingEvidenceLayerR13.lean"
  "lean/Mutations/Figure21ExactPromotionR13.lean"
  "lean/Mutations/Figure21ComparisonPromotionR13.lean"
  "lean/Mutations/CraneYetterIdentificationPromotionR13.lean"
  "lean/Mutations/MissingFigure21BlockerR13.lean"
  "lean/Mutations/CtlClaimPromotionR13.lean"
)

for mutation in "${mutations[@]}"; do
  output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-r13-mutation.XXXXXX")"
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
  if ! rg -iq "tactic .*rfl.* failed" "${output}"; then
    printf 'Mutation failed for the wrong reason: %s\n' "${mutation}" >&2
    cat "${output}" >&2
    rm -f "${output}"
    exit 1
  fi
  printf 'PASS expected rejection: %s\n' "${mutation}"
  rm -f "${output}"
done

injected="lean/Mutations/InjectedAxiomR13.lean"
if ! rg -q '^\s*axiom\b' "${injected}"; then
  printf 'Axiom-injection fixture lost its forbidden token\n' >&2
  exit 1
fi
printf 'PASS expected static rejection: %s [forbidden axiom]\n' "${injected}"
