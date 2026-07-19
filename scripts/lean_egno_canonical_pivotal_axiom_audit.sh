#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-egno-canonical-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Fusion/EGNOCanonicalPivotalAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|native_decide\.ax' "${output}"; then
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
