#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-compiler-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

LEAN_NUM_THREADS=1 ./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/TableTwoEvaluatorCompilerAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|standardSpecialKirbyCalculusConnected' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
