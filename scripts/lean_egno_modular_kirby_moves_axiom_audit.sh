#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-modular-kirby-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_egno_kirby_color_axiom_audit.sh \
  >"${output}" 2>&1

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/EGNOModularKirbyMovesAxiomAudit.lean \
  >>"${output}" 2>&1

if rg -q 'sorryAx|native_decide\.ax|declaration uses `sorry`' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
