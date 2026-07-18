#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
export UV_CACHE_DIR="$PWD/.uv-cache"

fixture="experiments/inputs/lean-kirby/framed-link-presentation-fixture-v1.json"

uv run pytest -q \
  tests/test_kirby_presentation_v1.py \
  tests/test_framed_link_presentation_syntax_v1.py

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/PresentationExecutionTrace.lean \
  lean/TwistedYetter/Kirby/PresentationSchemaRegression.lean

audit_output="$(mktemp \
  "${TMPDIR:-/tmp}/twisted-yetter-presentation-schema-axioms.XXXXXX")"
trap 'rm -f "${audit_output}"' EXIT

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/PresentationSchemaRegressionAxiomAudit.lean \
  >"${audit_output}" 2>&1

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/PresentationExecutionTraceAxiomAudit.lean \
  >>"${audit_output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`|native_decide\.ax' \
    "${audit_output}"; then
  printf 'Presentation schema/trace axiom audit failed:\n' >&2
  cat "${audit_output}" >&2
  exit 1
fi

./scripts/lean_local_check.sh --run \
  lean/PresentationArtifactReplay.lean \
  "${fixture}"
