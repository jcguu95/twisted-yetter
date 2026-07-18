#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp \
  "${TMPDIR:-/tmp}/twisted-yetter-source-h2-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/SourceBoundGeometricH2CompilerAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`|native_decide\.ax' "${output}"; then
  printf 'Source-bound geometric H2 audit found a proof oracle:\n' >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
