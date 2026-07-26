#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp "${TMPDIR:-/tmp}/twisted-yetter-ribbon-kirby-algebra-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/RibbonKirbyGraphicalAlgebra.lean

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/RibbonKirbyGraphicalAlgebraAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`|native_decide\.ax' "${output}"; then
  printf 'Ribbon-Kirby algebra axiom audit found a proof oracle:\n' >&2
  cat "${output}" >&2
  exit 1
fi

if rg -q \
    'TwistedYetter\.[A-Za-z0-9_.]*(standardSpecialKirbyPresentationsConnected|standardHandleChainNaturality)' \
    "${output}"; then
  printf 'Ribbon-Kirby algebra unexpectedly depends on a topology/domain axiom:\n' >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
