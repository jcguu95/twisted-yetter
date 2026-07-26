#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-graphical-compiler-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

LEAN_NUM_THREADS=1 ./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/SourceBoundGraphicalMoveCompilerAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q \
    'sorryAx|standardSpecialKirbyPresentationsConnected|standardHandleChainNaturality' \
    "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
