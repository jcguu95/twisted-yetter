#!/usr/bin/env bash
set -euo pipefail

if [[ "${LEAN_NUM_THREADS:-1}" -gt 2 ]]; then
  printf 'Refusing LEAN_NUM_THREADS=%s; local policy permits at most 2.\n' \
    "${LEAN_NUM_THREADS}" >&2
  exit 64
fi

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"

lock_dir=".lake/lean-local-check.lock"
mkdir -p .lake
if ! mkdir "${lock_dir}" 2>/dev/null; then
  printf 'Refusing concurrent local Lean process; lock exists at %s.\n' \
    "${lock_dir}" >&2
  exit 75
fi
trap 'rmdir "${lock_dir}"' EXIT

lake env lean -j "${LEAN_NUM_THREADS}" "$@"
