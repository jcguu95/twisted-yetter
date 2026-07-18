#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp \
  "${TMPDIR:-/tmp}/twisted-yetter-integral-character-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/IntegralCharacterKirbyColorCompiler.lean >/dev/null

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/IntegralCharacterKirbyColorCompilerAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q \
    'sorryAx|declaration uses `sorry`|native_decide\.ax|standardHandleChainNaturalityInput|standardSpecialKirbyCalculusConnected' \
    "${output}"; then
  printf 'Integral-character compiler axiom audit found a proof oracle or domain axiom:\n' >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
