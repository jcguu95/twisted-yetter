#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1

output="$(mktemp \
  "${TMPDIR:-/tmp}/twisted-yetter-handle-chain-naturality-axioms.XXXXXX")"
trap 'rm -f "${output}"' EXIT

./scripts/lean_local_build.sh \
  lean/TwistedYetter/Kirby/SourceBackedHandleChainNaturality.lean

./scripts/lean_local_check.sh \
  lean/TwistedYetter/Kirby/SourceBackedHandleChainNaturalityAxiomAudit.lean \
  >"${output}" 2>&1

if rg -q 'sorryAx|declaration uses `sorry`|native_decide\.ax' "${output}"; then
  printf 'Handle-chain naturality audit found a proof oracle:\n' >&2
  cat "${output}" >&2
  exit 1
fi

expected="TwistedYetter.Kirby.SourceBackedHandleChainNaturality.standardHandleChainNaturalityInput"
if ! rg -Fq "${expected}" "${output}"; then
  printf 'Expected handle-homology domain axiom is absent.\n' >&2
  cat "${output}" >&2
  exit 1
fi

custom="$(
  rg -o \
    'TwistedYetter\.[A-Za-z0-9_.]*standardHandleChainNaturalityInput' \
    "${output}" | sort -u
)"
if [[ "${custom}" != "${expected}" ]]; then
  printf 'Unexpected custom handle-homology axiom denominator:\n%s\n' \
    "${custom}" >&2
  cat "${output}" >&2
  exit 1
fi

cat "${output}"
