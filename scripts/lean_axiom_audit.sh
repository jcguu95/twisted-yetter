#!/usr/bin/env bash
set -euo pipefail

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-lean-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/AxiomAudit.lean >"${output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`' "${output}"; then
  printf 'Lean axiom audit found an unresolved proof:\n' >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
