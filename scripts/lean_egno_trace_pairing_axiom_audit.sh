#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-trace-pairing-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_egno_fusion_category_axiom_audit.sh \
  >"${output}" 2>&1

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/EGNOTracePairingAxiomAudit.lean \
  >>"${output}" 2>&1

if rg -q 'sorryAx|native_decide\.ax|declaration uses `sorry`' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
