#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-source-kirby-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/SourceBackedKirbyCompletenessAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`|native_decide\.ax' "${output}"; then
  printf 'Source-backed Kirby axiom audit found a proof oracle:\n' >&2
  cat "${output}" >&2
  exit 1
fi

expected="TwistedYetter.Kirby.SourceBackedKirbyCompleteness.standardSpecialKirbyCalculusConnected"
if ! rg -Fq "${expected}" "${output}"; then
  printf 'Expected topology domain axiom is absent from audit output.\n' >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
