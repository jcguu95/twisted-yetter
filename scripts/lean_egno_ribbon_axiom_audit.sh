#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/EGNORibbonAxiomAudit.lean >"${output}" 2>&1

if rg -q 'sorryAx' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
