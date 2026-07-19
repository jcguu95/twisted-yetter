#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-trace-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_egno_canonical_spherical_axiom_audit.sh \
  >"${output}" 2>&1

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/EGNOTraceCyclicityAxiomAudit.lean \
  >>"${output}" 2>&1

if rg -q 'sorryAx|native_decide\.ax|declaration uses `sorry`' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
